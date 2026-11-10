/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Matched-Session Stage P4 Continuation and Exit Packagers

Provides common exit stack recombination (`exit_entails_dpPollPost`), `genP3S5PanicProp` panic
adapters, and matched-session Stage P4 continuations (`closure_pathB_p4_cont`,
`closure_pathB_p4_cont_of_stageP4`, and `closure_pathB_p4_cont_ext`) from `+0x34dc` to
`s0.readReg64 .x30`.
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Common Exit Stack & Postcondition Packager -/

theorem stackAt_poll_exit_join (sp0 : BitVec 64) (B : RunBudgets) (stk' : Nat)
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    memRegion (sp0 - 0xcd0#64) 3280 ∗
      stackAt (sp0 - 0xcd0#64) (dpClosSubStack B) ∗
      memRegion (sp0 - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ⊢
    stackAt sp0 stk' := by
  rw [stackAt_poll_entry_split sp0 B stk' hneed hstk63]
  sep_frame

/-- Recombines `(memRegion sp 3280 ∗ stackAt sp (dpClosSubStack B) ∗ bottomGap)` into
`stackAt s0.sp stk'` and delegates to `dpPollPost_of_decResAt`. -/
theorem exit_entails_dpPollPost {img : Obj.Image} {W : CliHooks}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 sf : State)
    (g' : StoresGhost) (res : Except (ApiError AddrVal Unit) E2E.Bytes)
    (Leftover : SepProp)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hsteps : Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf)
    (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' res s0.trace sf.trace) :
    let sp := s0.sp - 0xcd0#64
    decResAt E2E.HooksE.A0 y.out res ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗
      E2E.HooksE.A0.pool ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      memRegion sp 3280 ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ⊢
      ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).post y s0 sf := by
  dsimp only
  have hstk_back := stackAt_poll_exit_join s0.sp B stk' hneed hstk63
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hstk_back)))))))))) ?_
  exact dpPollPost_of_decResAt B S stk' y s0 sf g' res Leftover hh hsteps htr hout

/-- Adapts a `SepWPp` with panic predicate `genP3S5PanicProp` to `P3P4.PanicOomProp`-compatible
top-level `dpPollSpecState.onPanic` when `Fr_p3` is framed around `s2`. -/
theorem sepWPp_genP3_to_pollGoal {img : Obj.Image} {W : CliHooks}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 s2 : State} {P_p3 Fr_p3 R : SepProp}
    (_hsteps02 : Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 s2)
    (hpan : st.version = msgVer →
      (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error .panic →
      (dpSlotPollKState E2E.HooksE.A0 img B S).panics y.g)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s2 P_p3
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s2 sf →
          (sf.mem ⊨ P_f ∗ (Fr_p3 ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5PanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s2
      (P_p3 ∗ Fr_p3)
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).onPanic y s0 sf ∗ R)) := by
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
    exact dpPollOnPanic_of_genP3 stk' y hgp hpan hmR
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Under `DecPkOk₀`, `me` and `peer` are opposite `Party` addresses (`P` vs `P.other`), hence
have distinct parsed UUID service IDs (`DistinctSid uuidTryParse`). -/
theorem distinctSid_of_decPkOk₀ {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm) :
    DistinctSid uuidTryParse me.name.bytes peer.name.bytes :=
  distinctSid_of_decPkOk hd

/-- Preserves `SessionExtraRel` across `CloneRel recG G₁` and `G₁.AfterTryDecrypt true G'` into the
cleared post-decrypt session `{ sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }`. -/
theorem sessionExtraRel_of_clone_decRel {recG G₁ G' : SessionGhost}
    {sess : Session (List (BitVec 8))} {st' : SessionState (List (BitVec 8))}
    (hex : SessionExtraRel recG sess)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec : G₁.AfterTryDecrypt true G') :
    SessionExtraRel G'
      { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none } := by
  obtain ⟨_, _, halice, hrem4, hloc4⟩ := hex
  obtain ⟨_, _, halice1, hreg1⟩ := hcl
  obtain ⟨⟨_, _, halice', hreg'⟩, hp', hkp'⟩ := hdec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hp', PendingRel]
  · simp [hkp', KyberRel]
  · dsimp only; rw [halice', halice1, halice]
  · dsimp only; rw [hreg', hreg1, hrem4]
  · dsimp only; rw [hreg', hreg1, hloc4]

theorem dpClosSubStack_le_pow64 (B : RunBudgets) {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    dpClosSubStack B ≤ 2 ^ 64 := by
  have := dpPollNeed_eq_frame_add_subStack B
  omega

theorem fsAt_pathB_p4 {img : Obj.Image} {W : CliHooks}
    {F0 : FsFiles} {peer : AddrGhost} {σ : DpKitStk} {s' : State}
    (hf : FsAt (fun f => f = F0) True (tripleRatchetProgAtExt img.base (cliExterns W)) s') :
    let kit := cliPollSessKit E2E.HooksE.A0 img.base F0 Slots.scopeKit peer σ
    let ikit := cliPollIdKit E2E.HooksE.A0 img.base F0 peer σ
    FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base (cliExterns W)) s' :=
  FsAt.mono (fun _ h => ⟨h, h⟩)
    (fun _ => ⟨cliPollSess_quiet img.base F0 Slots.scopeKit peer σ, cliPollId_quiet F0 peer σ⟩) hf

theorem stageP4MatchedStack_le_pow64 {b : BitVec 64} {F0 : FsFiles} {peer : AddrGhost}
    (B : RunBudgets) {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    stageP4MatchedCallStack
      (cliPollSessKit E2E.HooksE.A0 b F0 Slots.scopeKit peer (cliKitStk B))
      (cliPollIdKit E2E.HooksE.A0 b F0 peer (cliKitStk B)) ≤ 2 ^ 64 :=
  Nat.le_trans
    (cliPollStageP4MatchedStack_le_subStack E2E.HooksE.A0 b F0 Slots.scopeKit peer B)
    (dpClosSubStack_le_pow64 B hneed hstk63)

/-! ## 2. Matched-Session Stage P4 Continuation (`+0x34dc → s0.readReg64 .x30`) -/

set_option maxHeartbeats 800000 in
theorem closure_pathB_p4_cont
    (hP4 : StageP4MatchedExtStmt)
    {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
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
    (hsteps2' : Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s2 s')
    (hpc' : s'.pc = closureEntry img (cliExterns W) + 0x34dc#64)
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
      stageP3DispatchOkMidPrevEmpty E2E.HooksE.A0 img.base s0 s2 y.fut y.out 8#64
        ptCap ptPtr g pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2 ∗
      genP3S5PostFrame E2E.HooksE.A0 img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfter img.base y.g.coinsP y.g.coins
          (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins))) :
    let prog := tripleRatchetProgAtExt img.base (cliExterns W)
    let K := dpSlotPollKState E2E.HooksE.A0 img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit E2E.HooksE.A0 img.base y.g.F pid σ
    let spkKit := cliPollSpkKit E2E.HooksE.A0 img.base y.g.F sid σ
    let kpkKit := cliPollKpkKit E2E.HooksE.A0 img.base y.g.F kid sid kbk σ
    let Fr_tail : SepProp :=
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      stageP1VtablesAt img kit ikit
    SepWPp prog (s0.readReg64 .x30) s'
      (P_s' ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr
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
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
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
  let kit := cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
  let pkKit := cliPollPkKit E2E.HooksE.A0 img.base y.g.F pid σ
  let spkKit := cliPollSpkKit E2E.HooksE.A0 img.base y.g.F sid σ
  let kpkKit := cliPollKpkKit E2E.HooksE.A0 img.base y.g.F kid sid kbk σ
  let st' := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
  let ses' : Session (List (BitVec 8)) :=
    { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  let coinsPost := Coins.coinsAfter img.base y.g.coinsP y.g.coins
    (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)
  obtain ⟨hDec, hWr, hKit', hLen'⟩ :=
    decPkDef_pathB_ok X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
      hfPeer hdecOk hIn hloadS htrusted hMatch hrem hver hok
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := BitVec.sub_add_cancel s0.sp 0xcd0#64
  have hs'_files : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq hh hsteps2' (htr'.trans htr20.symm)).trans hs2_files
  have hfs_p4 := cliPollStageP1_fsAt hh y.g.F Slots.scopeKit y.g.peer B hs'_files
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp4_64 : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 :=
    Nat.le_trans (cliPollStageP4MatchedStack_le_subStack E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer B) hsub64
  have hwp4 := hP4 img (cliExterns W) kit ikit
    hh.allocContracts
    (cliDropSessionStructure3_ok hh)
    (cliPollSess_kitOkSE_of_deser W himg y.g.F Slots.scopeKit y.g.peer B hDeser)
    (cliPollSess_vtablesOk himg y.g.F Slots.scopeKit y.g.peer σ)
    (cliPollId_kitOkIE W himg y.g.F y.g.peer B)
    (cliPollId_vtablesOk himg y.g.F y.g.peer σ)
    himg s0 s'
    y.fut y.g.msgA y.cx y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (signedVt img)
    ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
    y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
    g G' ses'
    (cliBase_aligned himg) hex' ⟨hKit', hLen'⟩ rfl rfl
    hpt_le hpt_lt hpt_ne hp4_64 hfs_p4 hfz' hsym' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPrevEmpty_eq_p4 img B y s0 s2 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG
    preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
    opkHi kyberPreKeyId signedPreKeyId pt g G' st' hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hm2 : s'.mem ⊨
      stageP4MatchedPre img kit ikit s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (signedVt img)
        ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
        y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
        g G' st' ∗
      (pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
    have hEq :
        ((stageP3DispatchOkMidPrevEmpty E2E.HooksE.A0 img.base s0 s2 y.fut y.out 8#64
            ptCap ptPtr g pt 0#8 G' st' ∗
          genP3S5PostFrame E2E.HooksE.A0 img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            coinsPost) ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
            (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
            (y.g.stores + 0x78#64) (kyberVt img) rngPtr
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
        stageP4MatchedPre img kit ikit s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (signedVt img)
          ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
          y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
          g G' st' ∗
        (pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
      dsimp only [sp, σ, kit, ikit]
      rw [hs2_sp, hmid, sepConj_assoc]
    exact hEq ▸ hm1
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hfz_f, _hsym_f, hBr⟩⟩ |
    ⟨hpanf, Pf, hmf, hoom⟩ |
    ⟨_, hoom⟩
  · rcases hBr with ⟨c, _hsave, _hstore, htr_f, hpost_f⟩ | ⟨hsave, _, _⟩ | ⟨_, _, hstore, _, _⟩
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        dsimp only [kit, ikit, cliPollSessKit, cliSessionStoreSpec,
          cliPollIdKit, cliIdStoreSpecFull, cliIdentityStoreSpec] at htr_f
        simpa [htr'] using htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
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
      have hexit := stageP4MatchedExit_entails_exit img B y s0 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG
        preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
        opkHi kyberPreKeyId signedPreKeyId pid kid pt
        (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        g' hs'_sp0 hsp_sub hmsg_fold rfl rfl rfl rfl rfl rfl
      dsimp only at hexit
      have hm_f2 : sf.mem ⊨
          (stageP4MatchedExitAt img kit ikit s0 s' y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
              (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (signedVt img)
              ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
              (vecResultAt E2E.HooksE.A0 y.out (.ok pt)) pt
              y.g.peer y.g.msg.identityKey
              (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
              (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c)) ∗
            pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
              (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗
            pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            memRegion y.cx 32 ∗
            stageP1VtablesAt img kit ikit ∗ R) :=
        Arm64.Satisfies.mono (by sep_frame) hm_f1
      have hm_f3 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f2
      have hm_f4 : sf.mem ⊨
          (decResAt E2E.HooksE.A0 y.out (.ok pt) ∗
            storesAt E2E.HooksE.A0 y.g.stores g' ∗
            protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
            protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
            preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
            logOff img ∗
            E2E.HooksE.A0.pool ∗
            (TokenInit img ∗ coinsPost ∗ stageP1VtablesAt img kit ikit) ∗
            dpFutDoneAt y.fut ∗
            memRegion y.cx 32 ∗
            memRegion sp 3280 ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
        Arm64.Satisfies.mono (by sep_frame) hm_f3
      have hpost_goal := exit_entails_dpPollPost B S stk' hneed hstk63 y s0 sf g' (.ok pt)
        (TokenInit img ∗ coinsPost ∗ stageP1VtablesAt img kit ikit) hh hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f4
    · exact False.elim (cliId_saveRel_not_err hsave)
    · exact False.elim (cliSess_storeRel_not_err hstore)
  · rw [← sepConj_assoc] at hmf
    refine Or.inr (Or.inl ⟨hpanf, Pf ∗ pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
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

/-! ## 3. Contract-Parameterized `(P, A, ext)` Stage P4 Continuation -/

/-- Extern- and allocator-polymorphic counterpart of `exit_entails_dpPollPost`, delegating to
`dpPollPost_of_decResAt_ext` under `TraceFsSound (tripleRatchetProgAtExt img.base ext)`. -/
theorem exit_entails_dpPollPost_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 sf : State)
    (g' : StoresGhost) (res : Except (ApiError AddrVal Unit) E2E.Bytes)
    (Leftover : SepProp)
    (hfs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hsteps : Steps (tripleRatchetProgAtExt img.base ext) s0 sf)
    (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' res s0.trace sf.trace) :
    let sp := s0.sp - 0xcd0#64
    decResAt A y.out res ∗
      storesAt A y.g.stores g' ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗
      A.pool ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      memRegion sp 3280 ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ⊢
      ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf := by
  dsimp only
  have hstk_back := stackAt_poll_exit_join s0.sp B stk' hneed hstk63
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hstk_back)))))))))) ?_
  exact dpPollPost_of_decResAt_ext B S stk' y s0 sf g' res Leftover hfs hsteps htr hout

/-- Allocator- and extern-polymorphic counterpart of `sepWPp_genP3_to_pollGoal`. -/
theorem sepWPp_genP3_to_pollGoal_ext {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 s2 : State} {P_p3 Fr_p3 R : SepProp}
    (_hsteps02 : Steps (tripleRatchetProgAtExt img.base ext) s0 s2)
    (hpan : st.version = msgVer →
      (genP3S5Model P.C P.Q.K rem loc msg rest st).1 = .error .panic →
      (dpSlotPollKState A img B S).panics y.g)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2 P_p3
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base ext) s2 sf →
          (sf.mem ⊨ P_f ∗ (Fr_p3 ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5PanicProp P.C P.Q.K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
      (P_p3 ∗ Fr_p3)
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base ext) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).onPanic y s0 sf ∗ R)) := by
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
    exact dpPollOnPanic_of_genP3 stk' y hgp hpan hmR
  · exact (not_satisfies_false_sepConj hoom).elim

theorem fsAt_pathB_p4_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {F0 : FsFiles} {peer : AddrGhost} {σ : DpKitStk} {s' : State}
    (hf : FsAt (fun f => f = F0) True (tripleRatchetProgAtExt img.base ext) s') :
    let kit := cliPollSessKit A img.base F0 Slots.scopeKit peer σ
    let ikit := cliPollIdKit A img.base F0 peer σ
    FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s' :=
  FsAt.mono (fun _ h => ⟨h, h⟩)
    (fun _ => ⟨cliPollSess_quiet img.base F0 Slots.scopeKit peer σ, cliPollId_quiet F0 peer σ⟩) hf

theorem stageP4MatchedStack_le_pow64_ext {A : RustAlloc} {b : BitVec 64}
    {F0 : FsFiles} {peer : AddrGhost}
    (B : RunBudgets) {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    stageP4MatchedCallStack
      (cliPollSessKit A b F0 Slots.scopeKit peer (cliKitStk B))
      (cliPollIdKit A b F0 peer (cliKitStk B)) ≤ 2 ^ 64 :=
  Nat.le_trans
    (cliPollStageP4MatchedStack_le_subStack A b F0 Slots.scopeKit peer B)
    (dpClosSubStack_le_pow64 B hneed hstk63)

/-- Stage-decoupled Path B Stage P4 (`+0x34dc → s0.readReg64.x30`) contract at `(img, A, B, ext)`
specialized to `cliPollSessKit` and `cliPollIdKit`. -/
def StageP4MatchedExtAt (img : Obj.Image) (A : RustAlloc) (B : RunBudgets)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  ∀ (F0 : FsFiles) (peer : AddrGhost)
    (s0 s : State)
    (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (remoteIk : IdentityKey)
    (sst0 : (cliPollSessKit A img.base F0 Slots.scopeKit peer (cliKitStk B)).StoreState)
    (ist0 : (cliPollIdKit A img.base F0 peer (cliKitStk B)).IdState)
    (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))),
    let kit := cliPollSessKit A img.base F0 Slots.scopeKit peer (cliKitStk B)
    let ikit := cliPollIdKit A img.base F0 peer (cliKitStk B)
    img.base &&& 0xfff#64 = 0#64 →
    SessionExtraRel G ss →
    kit.RecOk ⟨some ss⟩ →
    pt.length ≤ ptCap.toNat →
    ptCap.toNat < 2 ^ 63 →
    ptPtr ≠ 0#64 →
    stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
    FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s →
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
      (stageP4MatchedPre img kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk
        sst0 ist0 g G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        StageP4MatchedBranch img kit ikit E2E.Record.encodeRecord s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
          ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk
          sst0 ist0 ss sf Pf)
      (PanicOomProp s0)

/-- Callee bundle for Path B (`StageP3PrevEmptyVRegsStmt` + `StageP4MatchedExtStmt`) at `(img, P, A, B, ext)`. -/
structure PollPathBCallees (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (B : RunBudgets) (ext : String → Option (State → State)) : Prop where
  alloc : AllocContracts img.base A ext
  chainClone : ChainClone3OkExt img.base A ext
  senderChainClone : SenderChainClone3OkExt img.base A ext
  tryDecrypt : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
    (_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64 uuidTryParse
      (LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img)
  dropSs3 : DropSessionStructure3OkExt img.base A ext
  sessKitOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyKitOkSE (cliPollSessKit A img.base F0 Slots.scopeKit peer (cliKitStk B))
      Slots.scopeKit E2E.Record.encodeRecord ext
  idKitOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityStoreKitOkIE img (cliPollIdKit A img.base F0 peer (cliKitStk B)) ext

/-- `AllocHooks` Stage P4 callee bundle for Path B (`StageP4MatchedXExtStmt`) at `(img, A, B, ext)`. -/
structure PollPathBXCallees (img : Obj.Image) (A : RustAlloc)
    (B : RunBudgets) (ext : String → Option (State → State)) : Prop where
  alloc : AllocHooks A ext
  dropSs3 : DropSessionStructure3OkExt img.base A ext
  sessKitOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyKitOkSE (cliPollSessKit A img.base F0 Slots.scopeKit peer (cliKitStk B))
      Slots.scopeKit E2E.Record.encodeRecord ext
  idKitOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityStoreKitOkIE img (cliPollIdKit A img.base F0 peer (cliKitStk B)) ext

/-- Instantiates `StageP4MatchedExtAt` from `StageP4MatchedExtStmt` and `PollPathBCallees`. -/
theorem stageP4MatchedExtAt_of_callees {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (hP4 : StageP4MatchedExtStmt) (hC : PollPathBCallees img P A B ext) :
    StageP4MatchedExtAt img A B ext := by
  intro himg F0 peer s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId b_2c0 pt remoteIk sst0 ist0 g G ss
    _kit _ikit hb hex hrec hpt_le hpt_lt hpt_ne hstk hfs hfz hsym hpc hrun hsp_align htr
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  exact hP4 img ext
    (cliPollSessKit A img.base F0 Slots.scopeKit peer (cliKitStk B))
    (cliPollIdKit A img.base F0 peer (cliKitStk B))
    hC.alloc hC.dropSs3 (hC.sessKitOk F0 peer)
    (cliPollSess_vtablesOk himg F0 Slots.scopeKit peer (cliKitStk B))
    (hC.idKitOk F0 peer)
    (cliPollId_vtablesOk himg F0 peer (cliKitStk B))
    himg s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ss
    hb hex hrec rfl rfl hpt_le hpt_lt hpt_ne hstk hfs hfz hsym hpc hrun hsp_align htr
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs

/-- Instantiates `StageP4MatchedExtAt` from `StageP4MatchedXExtStmt` and `PollPathBXCallees`. -/
theorem stageP4MatchedExtAt_of_xCallees {img : Obj.Image} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (hP4 : StageP4MatchedXExtStmt) (hC : PollPathBXCallees img A B ext) :
    StageP4MatchedExtAt img A B ext := by
  intro himg F0 peer s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId b_2c0 pt remoteIk sst0 ist0 g G ss
    _kit _ikit hb hex hrec hpt_le hpt_lt hpt_ne hstk hfs hfz hsym hpc hrun hsp_align htr
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  exact hP4 img ext
    (cliPollSessKit A img.base F0 Slots.scopeKit peer (cliKitStk B))
    (cliPollIdKit A img.base F0 peer (cliKitStk B))
    hC.alloc hC.dropSs3 (hC.sessKitOk F0 peer)
    (cliPollSess_vtablesOk himg F0 Slots.scopeKit peer (cliKitStk B))
    (hC.idKitOk F0 peer)
    (cliPollId_vtablesOk himg F0 peer (cliKitStk B))
    himg s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ss
    hb hex hrec rfl rfl hpt_le hpt_lt hpt_ne hstk hfs hfz hsym hpc hrun hsp_align htr
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs

set_option maxHeartbeats 800000 in
/-- Stage-decoupled Path B Stage P4 continuation (`+0x34dc → s0.readReg64.x30`) over arbitrary
`(P, A, ext)` given `TraceFsSound` and `StageP4MatchedExtAt`. -/
theorem closure_pathB_p4_cont_of_stageP4
    {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hP4B : StageP4MatchedExtAt img A B ext)
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (sess : Session (List (BitVec 8)))
    (s0 s2 s' : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (g : RecordGhost) (recG G₁ G' : SessionGhost)
    (pt : List (BitVec 8))
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hIn : Slots.scopeIn ⟨some sess⟩)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some ⟨some sess⟩))
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hMatch : SessMatchesPm sess y.g.msg)
    (hrem : sess.state.remoteIdentity = some y.g.msg.identityKey)
    (hex : SessionExtraRel recG sess)
    (hmsg_fold :
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg)
    (hs2_files : s2.fs.files = y.g.F)
    (htr20 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hver : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (tripleRatchetProgAtExt img.base ext) s2 s')
    (hpc' : s'.pc = closureEntry img ext + 0x34dc#64)
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
      stageP3DispatchOkMidPrevEmpty A img.base s0 s2 y.fut y.out 8#64
        ptCap ptPtr g pt 0#8 G'
        (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2 ∗
      genP3S5PostFrame A img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfter img.base y.g.coinsP y.g.coins
          (decryptDraws P.C sess.state y.g.msg.message.senderRatchetKey y.g.coins))) :
    let prog := tripleRatchetProgAtExt img.base ext
    let K := dpSlotPollKState A img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit A img.base y.g.F pid σ
    let spkKit := cliPollSpkKit A img.base y.g.F sid σ
    let kpkKit := cliPollKpkKit A img.base y.g.F kid sid kbk σ
    let Fr_tail : SepProp :=
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      stageP1VtablesAt img kit ikit
    SepWPp prog (s0.readReg64 .x30) s'
      (P_s' ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr
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
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5PanicProp P.C P.Q.K y.g.peer y.g.me sess.state y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  let pkKit := cliPollPkKit A img.base y.g.F pid σ
  let spkKit := cliPollSpkKit A img.base y.g.F sid σ
  let kpkKit := cliPollKpkKit A img.base y.g.F kid sid kbk σ
  let st' := (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
  let ses' : Session (List (BitVec 8)) :=
    { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  let coinsPost := Coins.coinsAfter img.base y.g.coinsP y.g.coins
    (decryptDraws P.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)
  obtain ⟨hDec, hWr, hKit', hLen'⟩ :=
    decPkDef_pathB_ok X P Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
      hfPeer hdecOk hIn hloadS htrusted hMatch hrem hver hok
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := BitVec.sub_add_cancel s0.sp 0xcd0#64
  have hs'_files : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_ext hFs hsteps2' (htr'.trans htr20.symm)).trans hs2_files
  have hfs_p4 := fsAt_pathB_p4_ext (A := A) (peer := y.g.peer) (σ := σ)
    (cliFsAt_of_files_eq_ext (Q := True) (envOk := fun f => f = y.g.F) hFs trivial rfl hs'_files)
  have hp4_64 : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 :=
    stageP4MatchedStack_le_pow64_ext B hneed hstk63
  have hwp4 := hP4B himg y.g.F y.g.peer s0 s'
    y.fut y.g.msgA y.cx y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (signedVt img)
    ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
    y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
    g G' ses'
    (cliBase_aligned himg) hex' ⟨hKit', hLen'⟩
    hpt_le hpt_lt hpt_ne hp4_64 hfs_p4 hfz' hsym' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPrevEmpty_eq_p4 img B y s0 s2 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG
    preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
    opkHi kyberPreKeyId signedPreKeyId pt g G' st' hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hm2 : s'.mem ⊨
      stageP4MatchedPre img kit ikit s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (signedVt img)
        ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
        y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
        g G' st' ∗
      (pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
    have hEq :
        ((stageP3DispatchOkMidPrevEmpty A img.base s0 s2 y.fut y.out 8#64
            ptCap ptPtr g pt 0#8 G' st' ∗
          genP3S5PostFrame A img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            coinsPost) ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
            (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
            (y.g.stores + 0x78#64) (kyberVt img) rngPtr
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
        stageP4MatchedPre img kit ikit s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (signedVt img)
          ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
          y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
          g G' st' ∗
        (pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
      dsimp only [sp, σ, kit, ikit]
      rw [hs2_sp, hmid, sepConj_assoc]
    exact hEq ▸ hm1
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hfz_f, _hsym_f, hBr⟩⟩ |
    ⟨hpanf, Pf, hmf, hoom⟩ |
    ⟨_, hoom⟩
  · rcases hBr with ⟨c, _hsave, _hstore, htr_f, hpost_f⟩ | ⟨hsave, _, _⟩ | ⟨_, _, hstore, _, _⟩
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        dsimp only [kit, ikit, cliPollSessKit, cliSessionStoreSpec,
          cliPollIdKit, cliIdStoreSpecFull, cliIdentityStoreSpec] at htr_f
        simpa [htr'] using htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
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
      have hexit := stageP4MatchedExit_entails_exit img B y s0 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG
        preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
        opkHi kyberPreKeyId signedPreKeyId pid kid pt
        (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        g' hs'_sp0 hsp_sub hmsg_fold rfl rfl rfl rfl rfl rfl
      dsimp only at hexit
      have hm_f2 : sf.mem ⊨
          (stageP4MatchedExitAt img kit ikit s0 s' y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
              (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (signedVt img)
              ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
              (vecResultAt A y.out (.ok pt)) pt
              y.g.peer y.g.msg.identityKey
              (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
              (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c)) ∗
            pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
              (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗
            pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            memRegion y.cx 32 ∗
            stageP1VtablesAt img kit ikit ∗ R) :=
        Arm64.Satisfies.mono (by sep_frame) hm_f1
      have hm_f3 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f2
      have hm_f4 : sf.mem ⊨
          (decResAt A y.out (.ok pt) ∗
            storesAt A y.g.stores g' ∗
            protocolAddressAt A y.g.peer y.g.peerA ∗
            protocolAddressAt A y.g.me y.g.meA ∗
            preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
            logOff img ∗
            A.pool ∗
            (TokenInit img ∗ coinsPost ∗ stageP1VtablesAt img kit ikit) ∗
            dpFutDoneAt y.fut ∗
            memRegion y.cx 32 ∗
            memRegion sp 3280 ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
        Arm64.Satisfies.mono (by sep_frame) hm_f3
      have hpost_goal := exit_entails_dpPollPost_ext B S stk' hneed hstk63 y s0 sf g' (.ok pt)
        (TokenInit img ∗ coinsPost ∗ stageP1VtablesAt img kit ikit) hFs hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f4
    · exact False.elim (cliId_saveRel_not_err hsave)
    · exact False.elim (cliSess_storeRel_not_err hstore)
  · rw [← sepConj_assoc] at hmf
    refine Or.inr (Or.inl ⟨hpanf, Pf ∗ pathBP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
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

/-- Callee-bundled corollary of `closure_pathB_p4_cont_of_stageP4` from `StageP4MatchedExtStmt`
and `PollPathBCallees`. -/
theorem closure_pathB_p4_cont_ext
    (hP4 : StageP4MatchedExtStmt)
    {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hC : PollPathBCallees img P A B ext)
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (sess : Session (List (BitVec 8)))
    (s0 s2 s' : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (g : RecordGhost) (recG G₁ G' : SessionGhost)
    (pt : List (BitVec 8))
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hIn : Slots.scopeIn ⟨some sess⟩)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some ⟨some sess⟩))
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hMatch : SessMatchesPm sess y.g.msg)
    (hrem : sess.state.remoteIdentity = some y.g.msg.identityKey)
    (hex : SessionExtraRel recG sess)
    (hmsg_fold :
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg)
    (hs2_files : s2.fs.files = y.g.F)
    (htr20 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hver : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (tripleRatchetProgAtExt img.base ext) s2 s')
    (hpc' : s'.pc = closureEntry img ext + 0x34dc#64)
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
      stageP3DispatchOkMidPrevEmpty A img.base s0 s2 y.fut y.out 8#64
        ptCap ptPtr g pt 0#8 G'
        (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2 ∗
      genP3S5PostFrame A img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfter img.base y.g.coinsP y.g.coins
          (decryptDraws P.C sess.state y.g.msg.message.senderRatchetKey y.g.coins))) :
    let prog := tripleRatchetProgAtExt img.base ext
    let K := dpSlotPollKState A img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit A img.base y.g.F pid σ
    let spkKit := cliPollSpkKit A img.base y.g.F sid σ
    let kpkKit := cliPollKpkKit A img.base y.g.F kid sid kbk σ
    let Fr_tail : SepProp :=
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      stageP1VtablesAt img kit ikit
    SepWPp prog (s0.readReg64 .x30) s'
      (P_s' ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr
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
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5PanicProp P.C P.Q.K y.g.peer y.g.me sess.state y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) :=
  closure_pathB_p4_cont_of_stageP4 P A ext X B S Scope himg hFs
    (stageP4MatchedExtAt_of_callees hP4 hC) hS stk' hneed hstk63 y sess s0 s2 s'
    rngPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R
    opkHi kyberPreKeyId signedPreKeyId g recG G₁ G' pt
    hfPeer hdecOk hIn hloadS htrusted hMatch hrem hex hmsg_fold
    hs2_files htr20 hs2_sp hsp_sub hsp_align2 hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne
    hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
    hfz' hsym' hent_s'

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
