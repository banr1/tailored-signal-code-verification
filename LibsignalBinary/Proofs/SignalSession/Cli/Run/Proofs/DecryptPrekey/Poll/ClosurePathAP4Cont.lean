/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4None
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesTryDecrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll New-Session Path A Stage P4 Continuation

Proves parameterized and fixed-table Stage P4 continuation theorems
(`closure_pathA_p4_cont_of_stageP4`, `closure_pathA_p4_cont_ext`, and `closure_pathA_p4_cont`) from
`+0x34dc` to `s0.readReg64 .x30` on new-session Path A (`opt.bind (·.currentSession) = none`,
`trusted = .ok true`).
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
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
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
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
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

theorem pmOfE_preKeyId_spkId_baseKey_eq (m : PreKeyMessageFields) (i : SignalMessage) :
    (pmOfE m i).preKeyId = m.opkId ∧
    (pmOfE m i).signedPreKeyId = m.spkId ∧
    (pmOfE m i).baseKey = ⟨m.baseKey⟩ := by
  have hf := pmOfE_fields m i
  exact ⟨hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1⟩

theorem cliPollKpk_markOk_of_pmOfE {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (m : PreKeyMessageFields) (i : SignalMessage) {pm : PreKeySignalMessage}
    (σ : DpKitStk) (_hpm : pm = pmOfE m i) :
    (cliPollKpkKit A b F0 m.kpkId m.spkId pm.baseKey σ).markOk m.kpkId m.spkId pm.baseKey :=
  ⟨rfl, rfl, rfl⟩

theorem cliPollPk_removeIdOk_of_pmOfE {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (m : PreKeyMessageFields) (i : SignalMessage) {pm : PreKeySignalMessage}
    (σ : DpKitStk) (hpm : pm = pmOfE m i) :
    ∀ opkId, m.opkId = some opkId →
      (cliPollPkKit A b F0 (pmPreKeyId pm) σ).removeIdOk opkId := by
  intro opkId hopk
  subst hpm
  have hpre : (pmOfE m i).preKeyId = m.opkId := (pmOfE_fields m i).2.2.1
  dsimp only [cliPollPkKit, cliPreKeyStoreSpec, pmPreKeyId]
  rw [hpre, hopk]
  rfl

theorem pathA_recOk_of_tryDecrypt {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {m : PreKeyMessageFields} {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : (genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st' := (genP3S5Model W.C W.Q.K peer me pm.message coins (pathAInitState W meE k m dk)).2
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    Slots.scopeKit ⟨some ses'⟩ ∧ (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 32 := by
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st' := (genP3S5Model W.C W.Q.K peer me pm.message coins (pathAInitState W meE k m dk)).2
  have hok_pair : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W meE k m dk) = (.ok pt, st') := by
    rcases hg : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W meE k m dk) with ⟨r1, r2⟩
    have hr1 : r1 = .ok pt := by rw [hg] at hok; exact hok
    subst hr1
    have hr2 : r2 = st' := by dsimp only [st']; rw [hg]
    subst hr2
    rfl
  have htry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) (pathAInitState W meE k m dk) = (.ok pt, st') := by
    rw [tryDecryptFromRecord_preKey_ver_eq hd hver, hok_pair]
  exact tryDecryptFromRecord_preKey_recOk_of_scopeIn
    (pathAInitSession_scopeIn W meE k m dk).1 htry

/-! ## 1. `TraceFsSound` Exit/FS Helpers, `StageP4PathAV1ExtAt`, & `PollPathACallees` -/

theorem pathA_files_eq_of_trace_eq {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 sf : State}
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hst : Steps (tripleRatchetProgAtExt img.base ext) s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  hFs.files_eq hst (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil

private theorem pathA_slotTraceFT_of_trace_eq {img : Obj.Image}
    {ext : String → Option (State → State)} {s0 sf : State}
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hst : Steps (tripleRatchetProgAtExt img.base ext) s0 sf)
    (htr : sf.trace = s0.trace) :
    slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
  ⟨htr ▸ List.prefix_refl s0.trace,
   pathA_files_eq_of_trace_eq hFs hst htr,
   congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩

private theorem pathA_dpPollPost_of_decResAt {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S)) (s0 sf : State)
    (g' : StoresGhost) (e : Except (ApiError AddrVal Unit) E2E.Bytes) (Leftover : SepProp)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hsteps : Steps (tripleRatchetProgAtExt img.base ext) s0 sf) (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' e s0.trace sf.trace) :
    decResAt A y.out e ∗ storesAt A y.g.stores g' ∗ protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗ preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ A.pool ∗ Leftover ∗ dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' ⊢
      ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf := by
  have hft : slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
    pathA_slotTraceFT_of_trace_eq hFs hsteps htr
  have hdec := decResAt_entails_dpWords_resHeap A y.out e
  have hany : Leftover ⊢ anyHeap := entails_anyHeap Leftover
  refine Entails.trans (sepConj_mono hdec
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hany)))))))) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun ws => ?_
  let K := dpSlotPollKState A img B S
  change (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt y.out ws ∗ dpResHeap A ws e) ∗
      storesAt A y.g.stores g' ∗ protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗ preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ A.pool ∗ anyHeap ∗ dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' ⊢
    (∃∗ ws', ⌜ws'.length = 6 ∧ ws'.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws' ∗ K.res y.g s0.fs s0.trace sf.fs sf.trace ws') ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk'
  have hreord :
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt y.out ws ∗ dpResHeap A ws e) ∗
      storesAt A y.g.stores g' ∗ protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗ preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ A.pool ∗ anyHeap ∗ dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' =
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt y.out ws ∗
        (storesAt A y.g.stores g' ∗ dpResHeap A ws e ∗ protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗ preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
          logOff img ∗ A.pool ∗ anyHeap)) ∗
      (dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk') := by ac_rfl
  rw [hreord]
  refine sepConj_mono_left (Entails.sepExists_right ws (sepConj_mono_right (sepConj_mono_right ?_)))
  dsimp only [K, dpSlotPollKState]
  have hEq : (slotTraceFT s0.fs s0.trace sf.fs sf.trace ∧
      slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        g' e s0.trace sf.trace) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hft, hout⟩⟩
  refine Entails.sepExists_right g' (Entails.sepExists_right e ?_)
  rw [hEq, pure_true, emp_sepConj]
  exact Entails.refl _

theorem pathA_exit_entails_dpPollPost {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S)) (s0 sf : State)
    (g' : StoresGhost) (res : Except (ApiError AddrVal Unit) E2E.Bytes) (Leftover : SepProp)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hsteps : Steps (tripleRatchetProgAtExt img.base ext) s0 sf) (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' res s0.trace sf.trace) :
    let sp := s0.sp - 0xcd0#64
    decResAt A y.out res ∗ storesAt A y.g.stores g' ∗ protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗ preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ A.pool ∗ Leftover ∗ dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗
      memRegion sp 3280 ∗ stackAt sp (dpClosSubStack B) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ⊢
      ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf := by
  dsimp only
  have hstk_back := stackAt_poll_exit_join s0.sp B stk' hneed hstk63
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hstk_back)))))))))) ?_
  exact pathA_dpPollPost_of_decResAt B S stk' y s0 sf g' res Leftover hFs hsteps htr hout

private theorem pathA_pollStageP4_fsAt {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (pid sid kid : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt (Kits.stageP4EnvOk (cliPollSessKit A img.base F0 Scope peer (cliKitStk B))
        (cliPollIdKit A img.base F0 peer (cliKitStk B))
        (cliPollPkKit A img.base F0 pid (cliKitStk B))
        (cliPollKpkKit A img.base F0 kid sid kbk (cliKitStk B)))
      (Kits.stageP4Quiet (cliPollSessKit A img.base F0 Scope peer (cliKitStk B))
        (cliPollIdKit A img.base F0 peer (cliKitStk B))
        (cliPollPkKit A img.base F0 pid (cliKitStk B))
        (cliPollKpkKit A img.base F0 kid sid kbk (cliKitStk B)))
      (tripleRatchetProgAtExt img.base ext) s :=
  .inr ⟨⟨cliPollSess_quiet img.base F0 Scope peer (cliKitStk B),
         cliPollId_quiet F0 peer (cliKitStk B),
         cliPollPk_quiet img.base F0 pid (cliKitStk B),
         cliPollKpk_quiet img.base F0 kid sid kbk (cliKitStk B)⟩,
        hFs, ⟨hf, hf, hf, hf⟩⟩

/-- Stage-decoupled 4-kit Stage P4 (`+0x34dc → s0.readReg64.x30`) contract on Path A at `(img, A, B, ext)`,
free of `RunHooks` and 0-stack `AllocContracts` so both `PollPathACallees` and `AllocContractsX`
callers instantiate it directly. -/
def StageP4PathAV1ExtAt (img : Obj.Image) (A : RustAlloc) (B : RunBudgets)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost) (pid kyberPreKeyId signedPreKeyId : BitVec 32)
    (baseKey : PublicKey) (remoteIk : IdentityKey)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (G : SessionGhost) (ss : Session (List (BitVec 8))),
    let σ := cliKitStk B
    let kit := cliPollSessKit A img.base F0 Slots.scopeKit peer σ
    let ikit := cliPollIdKit A img.base F0 peer σ
    let pkKit := cliPollPkKit A img.base F0 pid σ
    let kpkKit := cliPollKpkKit A img.base F0 kyberPreKeyId signedPreKeyId baseKey σ
    dpClosSubStack B ≤ 2 ^ 64 →
    prevStatesPtr ≠ 0#64 →
    SessionExtraRel G ss →
    kit.RecOk ⟨some ss⟩ →
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
      (Kits.stageP4Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        Kits.StageP4Branch img kit ikit pkKit kpkKit E2E.Record.encodeRecord s0 s coroPtr msgPtr
          outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt peer remoteIk
          baseKey StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber ss sf Pf)
      (PanicOomProp s0)

/-- Minimal external/callee obligation bundle consumed by Poll Path A on
`tripleRatchetProgAtExt img.base ext` without `RunHooks` fixed-hook pointer equalities. -/
structure PollPathACallees (img : Obj.Image) (P : PEParams) (A : RustAlloc) (B : RunBudgets)
    (ext : String → Option (State → State)) : Prop where
  alloc : AllocContracts img.base A ext
  fs : TraceFsSound (tripleRatchetProgAtExt img.base ext)
  sessKitOk : ∀ F peer, MessageDecrypt.SessionOnlyKitOkSE
    (cliPollSessKit A img.base F Slots.scopeKit peer (cliKitStk B)) Slots.scopeKit
    E2E.Record.encodeRecord ext
  idKitOk : ∀ F peer, IdentityStoreKitOkIE img (cliPollIdKit A img.base F peer (cliKitStk B)) ext
  pkKitOk : ∀ F pid, PreKeyStoreKitOkImgE img (cliPollPkKit A img.base F pid (cliKitStk B)) ext
  kpkKitOk : ∀ F kid sid kbk,
    KyberPreKeyStoreKitOkImgE img (cliPollKpkKit A img.base F kid sid kbk (cliKitStk B)) ext
  tryDecrypt : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
    (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64 uuidTryParse
      (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img)

theorem PollPathACallees.chainClone3 {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (hc : PollPathACallees img P A B ext) :
    ChainClone3OkExt img.base A ext :=
  chainClone3_ok_ext hc.alloc

theorem PollPathACallees.senderChainClone3 {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (hc : PollPathACallees img P A B ext) :
    SenderChainClone3OkExt img.base A ext :=
  senderChainClone3_ok_ext hc.alloc

theorem PollPathACallees.dropSessionStructure3 {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (hc : PollPathACallees img P A B ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A) :=
  drop_session_structure3_ok_ext hc.alloc

theorem PollPathACallees.of_cliHooks {img : Obj.Image} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img)) :
    PollPathACallees img ⟨W.C, W.Q⟩ E2E.HooksE.A0 B (cliExterns W) :=
  ⟨hh.allocContracts, hh.fs,
    fun F peer => cliPollSess_kitOkSE_of_deser W himg F Slots.scopeKit peer B hDeser,
    fun F peer => cliPollId_kitOkIE W himg F peer B,
    fun F pid => cliPollPk_kitOkImgE W himg F pid B,
    fun F kid sid kbk => cliPollKpk_kitOkImgE W himg F kid sid kbk B,
    cliTryDecryptPqV1_ok W 0#64 himg⟩

theorem stageP4PathAV1ExtAt_of_callees {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hc : PollPathACallees img P A B ext) :
    StageP4PathAV1ExtAt img A B ext := by
  intro F0 peer pid kyberPreKeyId signedPreKeyId baseKey remoteIk
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    opkId? b_2c0 pt G ss
  dsimp only
  intro hsub64 hprev_nz hExtra hrec_ok hmark_ok hrem_ok hpt_le hcap_lt hptr_nz
    hfiles hF hsym hpc hrun hsp_align htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  let σ := cliKitStk B
  have hp4_64 : stageP4CallStack
      (cliPollSessKit A img.base F0 Slots.scopeKit peer σ)
      (cliPollIdKit A img.base F0 peer σ)
      (cliPollPkKit A img.base F0 pid σ)
      (cliPollKpkKit A img.base F0 kyberPreKeyId signedPreKeyId baseKey σ) ≤ 2 ^ 64 :=
    Nat.le_trans
      (stageP4CallStack_le_subStack img.base F0 Slots.scopeKit peer pid signedPreKeyId
        kyberPreKeyId baseKey B)
      hsub64
  exact Kits.stageP4_v1_vregs_kits_ok img ext Slots.scopeKit E2E.Record.encodeRecord
    (cliPollSessKit A img.base F0 Slots.scopeKit peer σ)
    (cliPollIdKit A img.base F0 peer σ)
    (cliPollPkKit A img.base F0 pid σ)
    (cliPollKpkKit A img.base F0 kyberPreKeyId signedPreKeyId baseKey σ)
    hc.alloc hc.dropSessionStructure3
    (hc.sessKitOk F0 peer) (cliPollSess_vtablesOk himg F0 Slots.scopeKit peer σ)
    (hc.idKitOk F0 peer) (cliPollId_vtablesOk himg F0 peer σ)
    (hc.pkKitOk F0 pid) (cliPollPk_vtablesOk himg F0 pid σ)
    (hc.kpkKitOk F0 kyberPreKeyId signedPreKeyId baseKey)
    (cliPollKpk_vtablesOk himg F0 kyberPreKeyId signedPreKeyId baseKey σ)
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber G ss
    (cliBase_aligned himg) hprev_nz hExtra hrec_ok rfl rfl
    hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hp4_64
    (pathA_pollStageP4_fsAt hc.fs F0 Slots.scopeKit peer pid signedPreKeyId kyberPreKeyId
      baseKey B hfiles)
    hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

/-! ## 2. Stage P4 Continuations (`closure_pathA_p4_cont_of_stageP4`, `_ext`, and Fixed-Table) -/

set_option maxHeartbeats 1200000 in
theorem closure_pathA_p4_cont_of_stageP4
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hP4 : StageP4PathAV1ExtAt img A B ext)
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (recG G₁ G' : SessionGhost)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
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
      stageP3DispatchOkMid A img.base s0 s2 y.fut y.out 8#64 8#64 ptCap ptPtr pt 0#8 G'
        (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      genP3S5PostFrame A img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfter img.base y.g.coinsP y.g.coins
          (decryptDraws P.C (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins))) :
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
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
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
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  let pkKit := cliPollPkKit A img.base y.g.F pid σ
  let spkKit := cliPollSpkKit A img.base y.g.F m.spkId σ
  let kpkKit := cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
  let F_p3 : SepProp :=
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
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st0 := pathAInitState P meE k m dk
  let st' := (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
  let ses' : Session (List (BitVec 8)) :=
    { pathAInitSession P meE k m dk with
      state := st', pendingPreKey := none, pendingKyberPreKey := none }
  let coinsPost := Coins.coinsAfter img.base y.g.coinsP y.g.coins
    (decryptDraws P.C st0 y.g.msg.message.senderRatchetKey y.g.coins)
  have hok_pair : genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 =
      (.ok pt, st') := by
    rcases hg : genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 with ⟨r1, r2⟩
    have hr1 : r1 = .ok pt := by rw [hg] at hok; exact hok
    subst hr1
    have hr2 : r2 = st' := by dsimp only [st']; rw [hg]
    subst hr2
    rfl
  obtain ⟨hKit', hLen'⟩ := pathA_recOk_of_tryDecrypt hdecOk hver hok
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := sp_frame_sub_add s0.sp
  have hf' : s'.fs.files = y.g.F :=
    (pathA_files_eq_of_trace_eq hFs hsteps2' (htr'.trans htr2.symm)).trans hfiles2
  have hwp4 := hP4 y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey y.g.msg.identityKey
    s0 s' y.fut y.cx y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
    8#64 ptCap ptPtr 8#64 m.opkId 0#8 pt G' ses'
    (by have := dpPollNeed_eq_frame_add_subStack B; omega)
    (by decide) hex' ⟨hKit', hLen'⟩
    (cliPollKpk_markOk_of_pmOfE img.base y.g.F m i σ hpm_eq)
    (cliPollPk_removeIdOk_of_pmOfE img.base y.g.F m i σ hpm_eq)
    hpt_le hpt_lt hpt_ne hf' hfz' hsym' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPathA_eq_p4 img B y s0 s2 s' rngPtr 8#64 8#64 whisperMsgPtr ptCap ptPtr whisperG
    preKeyMsgRem coinsPost m.opkId (y.g.msg.message.messageVersion.zeroExtend 32)
    pid m.kpkId m.spkId pt G' st' hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hm2 : s'.mem ⊨
      Kits.stageP4Pre img kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        8#64 ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' ∗
      (pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost ∗
        R') := by
    rw [hs2_sp] at hm1
    rw [hmid, sepConj_assoc] at hm1
    exact hm1
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
      have htr_sf : sf.trace = s0.trace := by
        revert _hrem htr_f
        generalize m.opkId = opk?
        rintro _hrem htr_f _
        cases opk? <;>
          simpa [kit, ikit, pkKit, kpkKit,
            cliPollSessKit, cliSessionStoreSpec,
            cliPollIdKit, cliIdStoreSpecFull, cliIdentityStoreSpec,
            cliPollPkKit, cliPreKeyStoreSpec,
            cliPollKpkKit, cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
            htr'] using htr_f
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
      obtain ⟨_, _, _, hDec, hWr⟩ :=
        decPkDef_pathA_ok X P Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hfPeer hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hok_pair hmark_eq
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
            (E2E.Record.encodeRecord ⟨some ses'⟩) }
      have hout : slotOutTr
          (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
          g' (.ok pt) s0.trace sf.trace :=
        slotOutTr_of_accept hS hDec hWr
      have hot_eq : g'.oneTime =
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ())) := by
        dsimp only [g', oneTime', pkKit, cliPollPkKit, cliPreKeyStoreSpec]
        rw [hpre_id]
      have hexit := stageP4PathAExit_entails_exit img B y s0 s' rngPtr 8#64 8#64 whisperMsgPtr ptCap ptPtr
        whisperG (vecResultAt A y.out (.ok pt)) preKeyMsgRem coinsPost
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.ok pt)
        (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
        (match m.opkId with
         | none => StoresGhost.opened.oneTime
         | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ()))
        g' hs'_sp0 hsp_sub (decResultAt_ok_entails_decResAt_anyHeap A y.out pt)
        hmsg_fold rfl rfl hot_eq rfl rfl rfl
      dsimp only at hexit
      have hpost_f' : Pf ⊢
          stageP4ExitAt img kit ikit pkKit kpkKit s0 s' y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
            (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
            8#64 ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
            (vecResultAt A y.out (.ok pt)) m.kpkId m.spkId pt
            y.g.peer y.g.msg.identityKey y.g.msg.baseKey
            (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
            (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
            (match m.opkId with
             | none => StoresGhost.opened.oneTime
             | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
            (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ())) := by
        revert _hrem htr_f hpost_f
        generalize m.opkId = opk?
        rintro _ _ hpost_f
        cases opk? <;> exact hpost_f
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f')) hm_f
      have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
      have hm_f3 : sf.mem ⊨
          (decResAt A y.out (.ok pt) ∗
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
      have hpost_goal := pathA_exit_entails_dpPollPost B S stk' hneed hstk63 y s0 sf g' (.ok pt)
        (TokenInit img ∗ coinsPost ∗ anyHeap ∗ stageP1VtablesAt img kit ikit)
        hFs hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3
    · exact False.elim (cliId_saveRel_not_err hsave)
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        simpa [ikit, kpkKit,
          cliPollIdKit, cliIdStoreSpecFull, cliIdentityStoreSpec,
          cliPollKpkKit, cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
          htr'] using htr_f
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
      have hDec := decPkDef_pathA_mark_err X P Scope y.g.F y.g.peer y.g.me y.g.msg
        y.g.coins hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hok_pair hmark_err
      let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val
            y.g.msg.identityKey (.ok c)
          kyber := kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e) }
      have hout : slotOutTr
          (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
          g' (.error err) s0.trace sf.trace :=
        slotOutTr_of_reject g' hS nofun nofun hDec
      have hexit := stageP4PathAExit_entails_exit img B y s0 s' rngPtr 8#64 8#64 whisperMsgPtr ptCap ptPtr
        whisperG (speErrAt kpkKit.markErr y.out e) preKeyMsgRem coinsPost
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.error err)
        StoresGhost.opened.sessions StoresGhost.opened.oneTime
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.error e))
        g' hs'_sp0 hsp_sub
        (cliPollKpk_markErr_entails_decResAt_anyHeap A img.base y.g.F m.kpkId m.spkId
          y.g.msg.baseKey σ y.out e err)
        hmsg_fold rfl rfl rfl rfl rfl rfl
      dsimp only at hexit
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f)) hm_f
      have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
      have hm_f3 : sf.mem ⊨
          (decResAt A y.out (.error err) ∗
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
      have hpost_goal := pathA_exit_entails_dpPollPost B S stk' hneed hstk63 y s0 sf g' (.error err)
        (TokenInit img ∗ coinsPost ∗ anyHeap ∗ stageP1VtablesAt img kit ikit)
        hFs hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3
    · exact False.elim (cliPk_removeRel_not_err_of_pkStoreKeys hk hopk hrem)
    · exact False.elim (cliSess_storeRel_not_err hstore)
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

theorem closure_pathA_p4_cont_ext
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hc : PollPathACallees img P A B ext)
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (recG G₁ G' : SessionGhost)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
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
      stageP3DispatchOkMid A img.base s0 s2 y.fut y.out 8#64 8#64 ptCap ptPtr pt 0#8 G'
        (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      genP3S5PostFrame A img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfter img.base y.g.coinsP y.g.coins
          (decryptDraws P.C (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins))) :
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
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
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
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) :=
  closure_pathA_p4_cont_of_stageP4 B S hc.fs (stageP4PathAV1ExtAt_of_callees himg hc)
    hS stk' hneed hstk63 y hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk recG G₁ G'
    rngPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
    hpm_eq hi hk hkp hreg hacc hex hmsg_fold hfiles2 htr2 hs2_sp hsp_align2 hsp_sub hver
    hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
    hx19' hx24' hx25' hx26' hx27' hx28' hfz' hsym' hent_s'

theorem closure_pathA_p4_cont
    {img : Obj.Image} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (recG G₁ G' : SessionGhost)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
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
      stageP3DispatchOkMid E2E.HooksE.A0 img.base s0 s2 y.fut y.out 8#64 8#64 ptCap ptPtr pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      genP3S5PostFrame E2E.HooksE.A0 img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfter img.base y.g.coinsP y.g.coins
          (decryptDraws W.C (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins))) :
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
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
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
  closure_pathA_p4_cont_ext B S himg (PollPathACallees.of_cliHooks W B himg hh hDeser)
    hS stk' hneed hstk63 y hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk recG G₁ G'
    rngPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
    hpm_eq hi hk hkp hreg hacc hex hmsg_fold hfiles2 htr2 hs2_sp hsp_align2 hsp_sub hver
    hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
    hx19' hx24' hx25' hx26' hx27' hx28' hfz' hsym' hent_s'

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
