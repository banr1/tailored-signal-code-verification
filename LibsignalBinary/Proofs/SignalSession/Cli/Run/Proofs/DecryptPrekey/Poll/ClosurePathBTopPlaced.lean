/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanicPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridgePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Poll Matched-Session Stage P4 Continuation

Provides common exit stack recombination, `genP3S5PanicProp` panic adaptation, and matched-session
Stage P4 continuation `closure_pathB_p4_cont_placed` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Common Exit Stack & Postcondition Packager -/

/-- Recombines `(memRegion sp 3280 ∗ stackAt sp (dpClosSubStack B) ∗ bottomGap)` into
`stackAt s0.sp stk'` and delegates to `dpPollPost_of_decResAt_placed`. -/
theorem exit_entails_dpPollPost_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 sf : State)
    (g' : StoresGhost) (res : Except (ApiError AddrVal Unit) E2E.Bytes)
    (Leftover : SepProp)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hsteps : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf)
    (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' res s0.trace sf.trace) :
    let sp := s0.sp - 0xcd0#64
    decResAt E2E.HooksE.A0 y.out res ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      memRegion sp 3280 ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ⊢
      (StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk')).post y s0 sf := by
  dsimp only
  have hstk_back := stackAt_poll_exit_join s0.sp B stk' hneed hstk63
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hstk_back)))))))))) ?_
  exact dpPollPost_of_decResAt_placed (i := 518) B S stk' y s0 sf g' res Leftover hh hsteps htr hout

/-- Adapts a `SepWPp` with panic predicate `genP3S5PanicProp` to `P3P4.PanicOomProp`-compatible
top-level `dpPollSpecState.onPanic` under `[LibsignalPlacement]` when `Fr_p3` is framed around `s2`. -/
theorem sepWPp_genP3_to_pollGoal_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 s2 : State} {P_p3 Fr_p3 R : SepProp}
    (_hsteps02 : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s2)
    (hpan : st.version = msgVer →
      (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error .panic →
      (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).panics y.g)
    (hwp : SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2 P_p3
      (fun sf P_f =>
        (Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s2 sf →
          (sf.mem ⊨ P_f ∗ (Fr_p3 ∗ R)) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl
            (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5PanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
      (P_p3 ∗ Fr_p3)
      (fun sf P_f =>
        (Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl
            (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl
            (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk')).onPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps2f, ⟨hpcm, hrunm, P_f, hmf, hpost, hspf, hcs⟩ | ⟨hpanf, P_f, hmf, hgp⟩ | ⟨_, hoom⟩⟩ :=
    hwp (Fr_p3 ∗ R') hm hL
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps2f, Or.inl ⟨hpcm, hrunm, P_f ∗ Fr_p3, hmf, ?_, hspf, hcs⟩⟩
    intro _ hmR
    rw [sepConj_assoc] at hmR
    exact hpost hsteps2f hmR
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps2f, Or.inr (Or.inl ⟨hpanf, P_f ∗ Fr_p3, hmf, ?_⟩)⟩
    intro _ hmR
    exact dpPollOnPanic_of_genP3_placed stk' y hgp hpan hmR
  · exact (not_satisfies_false_sepConj hoom).elim

theorem fsAt_pathB_p4_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {F0 : FsFiles} {peer : AddrGhost} {σ : DpKitStk} {s' : State}
    (hf : FsAt (fun f => f = F0) True
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s') :
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 F0 Slots.scopeKit peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 F0 peer σ
    FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s' :=
  FsAt.mono (fun _ h => ⟨h, h⟩)
    (fun _ => ⟨cliPollSessPlaced_quiet F0 Slots.scopeKit peer σ, cliPollIdPlaced_quiet F0 peer σ⟩) hf

theorem stageP4MatchedStack_placed_le_pow64 [LibsignalPlacement]
    {F0 : FsFiles} {peer : AddrGhost}
    (B : RunBudgets) {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    stageP4MatchedCallStack
      (cliPollSessKitPlaced E2E.HooksE.A0 F0 Slots.scopeKit peer (cliKitStk B))
      (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)) ≤ 2 ^ 64 :=
  Nat.le_trans
    (cliPollStageP4MatchedStack_placed_le_subStack E2E.HooksE.A0 F0 Slots.scopeKit peer B)
    (dpClosSubStack_le_pow64 B hneed hstk63)

/-! ## 2. Matched-Session Stage P4 Continuation (`+0x34dc → s0.readReg64 .x30`) -/

set_option maxHeartbeats 800000 in
theorem closure_pathB_p4_cont_placed [LibsignalPlacement]
    (hP4 : StageP4MatchedPlacedStmt)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (sess : Session (List (BitVec 8)))
    (s0 s2 s' : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (g : RecordGhost) (recG G₁ G' : SessionGhost)
    (pt : List (BitVec 8))
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hIn : Slots.scopeIn ⟨some sess⟩)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some ⟨some sess⟩))
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hMatch : SessMatchesPm sess y.g.msg)
    (hrem : sess.state.remoteIdentity = some y.g.msg.identityKey)
    (hex : SessionExtraRel recG sess)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
    (hs2_files : s2.fs.files = y.g.F)
    (htr20 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hver : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s2 s')
    (hpc' : s'.pc = dpPollEntryPlaced + 0x34dc#64)
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
    (hro' : StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem)
    (hent_s' : P_s' ⊢
      stageP3DispatchOkMidPrevEmpty_placed E2E.HooksE.A0 s0 s2 y.fut y.out 8#64
        ptCap ptPtr g pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2 ∗
      genP3S5PostFrame_placed E2E.HooksE.A0 s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins))) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced E2E.HooksE.A0 B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid sid kbk σ
    let Fr_tail : SepProp :=
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32
    SepWPp prog (s0.readReg64 .x30) s'
      (P_s' ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
          (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
          (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
            ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
            memRegion (y.fut + 0x2a8#64) 4) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ∗
        ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
        kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5PanicProp W.C W.Q.K y.g.peer y.g.me sess.state y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid sid kbk σ
  let st' := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
  let ses' : Session (List (BitVec 8)) :=
    { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  let coinsPost := coinsAfterPlaced y.g.coinsP y.g.coins
    (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)
  obtain ⟨hDec, hWr, hKit', hLen'⟩ :=
    decPkDef_pathB_ok X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
      hfPeer hdecOk hIn hloadS htrusted hMatch hrem hver hok
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := BitVec.sub_add_cancel s0.sp 0xcd0#64
  have hs'_files : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps2' (htr'.trans htr20.symm)).trans hs2_files
  have hfs_p4 := cliPollStageP1_fsAt_placed hh y.g.F Slots.scopeKit y.g.peer B hs'_files
  have hp4_64 : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 :=
    stageP4MatchedStack_placed_le_pow64 B hneed hstk63
  have hwp4 := hP4 mmpl gh W B y.g.F y.g.peer hh hReadFile hDeser s0 s'
    y.fut y.g.msgA y.cx y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
    y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
    g G' ses'
    hex' ⟨hKit', hLen'⟩ rfl rfl
    hpt_le hpt_lt hpt_ne hp4_64 hfs_p4 hro' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPrevEmpty_eq_p4_placed B y s0 s2 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG
    preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
    opkHi kyberPreKeyId signedPreKeyId pt g G' st' hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hm2 : s'.mem ⊨
      stageP4MatchedPrePlaced kit ikit s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
        y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
        g G' st' ∗
      (pathBP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
    have hEq :
        ((stageP3DispatchOkMidPrevEmpty_placed E2E.HooksE.A0 s0 s2 y.fut y.out 8#64
            ptCap ptPtr g pt 0#8 G' st' ∗
          genP3S5PostFrame_placed E2E.HooksE.A0 s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            coinsPost) ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
            (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
            (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
            (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
              ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
              memRegion (y.fut + 0x2a8#64) 4) ∗
          stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem ∗
          ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
          kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
          memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) ∗ R' =
        stageP4MatchedPrePlaced kit ikit s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
          y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
          g G' st' ∗
        (pathBP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
      dsimp only [sp, σ, kit, ikit]
      rw [hs2_sp, hmid, sepConj_assoc]
    exact hEq ▸ hm1

  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hro_f, hBr⟩⟩ |
    ⟨hpanf, Pf, hmf, hoom⟩ |
    ⟨_, hoom⟩
  · rcases hBr with ⟨c, _hsave, _hstore, htr_f, hpost_f⟩ | ⟨hsave, _, _⟩ | ⟨_, _, hstore, _, _⟩
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        dsimp only [kit, ikit, cliPollSessKitPlaced, cliPollSessKit, cliSessionStoreSpec,
          cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull,
          cliIdentityStoreSpec] at htr_f
        simpa [htr'] using htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathBP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          sessions := StoresGhost.opened.sessions.put (Cli.addressText y.g.peer.val)
            (E2E.Record.encodeRecord ⟨some ses'⟩) }
      have hout : slotOutTr
          (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
          g' (.ok pt) s0.trace sf.trace :=
        slotOutTr_of_ok s0.trace sf.trace (by rw [hS]; exact hDec) hWr
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f)) hm_f
      have hexit := stageP4MatchedExit_entails_exit_placed B y s0 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG
        preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
        opkHi kyberPreKeyId signedPreKeyId pid kid pt
        (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        g' hs'_sp0 hsp_sub hmsg_fold rfl rfl rfl rfl rfl rfl
      dsimp only at hexit
      have hm_f2 : sf.mem ⊨
          (stageP4MatchedExitAtPlaced kit ikit s0 s' y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
              (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
              (vecResultAt E2E.HooksE.A0 y.out (.ok pt)) pt
              y.g.peer y.g.msg.identityKey
              (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
              (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c)) ∗
            pathBP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
              (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗
            pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            memRegion y.cx 32 ∗ R) :=
        Arm64.Satisfies.mono (by sep_frame) hm_f1
      have hm_f3 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f2
      have hm_f4 : sf.mem ⊨
          (decResAt E2E.HooksE.A0 y.out (.ok pt) ∗
            storesAt E2E.HooksE.A0 y.g.stores g' ∗
            protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
            protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
            preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
            FromRecordCallees.lsLogOff ∗
            E2E.HooksE.A0.pool ∗
            (LsTokenInit ∗ coinsPost) ∗
            dpFutDoneAt y.fut ∗
            memRegion y.cx 32 ∗
            memRegion sp 3280 ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
        Arm64.Satisfies.mono (by sep_frame) hm_f3
      have hpost_goal := exit_entails_dpPollPost_placed B S stk' hneed hstk63 y s0 sf g' (.ok pt)
        (LsTokenInit ∗ coinsPost) hh hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f4
    · dsimp only [cliPollIdKitPlaced, cliIdStoreSpecFullPlaced] at hsave
      exact False.elim (cliId_saveRel_not_err hsave)
    · dsimp only [cliPollSessKitPlaced] at hstore
      exact False.elim (cliSess_storeRel_not_err hstore)
  · rw [← sepConj_assoc] at hmf
    refine Or.inr (Or.inl ⟨hpanf, Pf ∗ pathBP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
      (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost, hmf, Or.inl ?_⟩)
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

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
