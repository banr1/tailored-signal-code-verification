/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesTryDecrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Matched-Session Path B Top-Level Branch

Combines `StageP2MatchedFramedExtAt` (`+0x0868 -> +0x1778` or mismatch exit),
`StageP3GenPathBExtAt` (`+0x1778 -> +0x34dc` or reject/panic exit), and Stage P4 continuation
(`+0x34dc -> s0.readReg64 .x30`) to prove `closure_pathB_ok_of_stages`, `closure_pathB_ok_ext`, and
`closure_pathB_ok`.
-/

@[expose] public section

set_option autoImplicit false

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

/-! ## 1. `SepWPp` Outer-Frame Adapter for `P3P4.PanicOomProp` -/

/-- Allocator- and extern-polymorphic counterpart of `sepWPp_p3p4Oom_to_pollGoal`. -/
theorem sepWPp_p3p4Oom_to_pollGoal_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S)) {s0 s1 : State} {P_p2 Fr_p2 R : SepProp}
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P_p2
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ (Fr_p2 ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 (P_p2 ∗ Fr_p2)
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).onPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps1f, ⟨hpcm, hrunm, P_f, hmf, hpost, hspf, hcs⟩ | ⟨hpanf, P_f, hmf, hoom⟩ | ⟨_, hoom⟩⟩ :=
    hwp (Fr_p2 ∗ R') hm hL
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps1f, Or.inl ⟨hpcm, hrunm, P_f ∗ Fr_p2, hmf, ?_, hspf, hcs⟩⟩
    intro hsteps0f hmR; rw [sepConj_assoc] at hmR; exact hpost hsteps0f hmR
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps1f, Or.inr (Or.inl ⟨hpanf, P_f ∗ Fr_p2, hmf, ?_⟩)⟩
    intro _ hmR; exact dpPollOnPanic_of_p3p4Oom stk' y hoom hmR
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Frames `Fr_p2` around a `SepWPp` at `s1` with panic predicate `P3P4.PanicOomProp s0`,
packaging both normal returns and OOM panics into `dpPollSpecState`. -/
theorem sepWPp_p3p4Oom_to_pollGoal {img : Obj.Image} {W : CliHooks}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    {s0 s1 : State} {P_p2 Fr_p2 R : SepProp}
    (hwp : SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s1 P_p2
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ (Fr_p2 ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s1
      (P_p2 ∗ Fr_p2)
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).onPanic y s0 sf ∗ R)) :=
  sepWPp_p3p4Oom_to_pollGoal_ext B S stk' y hwp

/-! ## 2. Framed CPS Stage P2 Statement for Path B (`StageP2MatchedFramedCliStmt`) -/

/-- Framed + general-`Qpan` Stage P2 contract for Path B (`opt = some ⟨some sess⟩`) at `+0x0868`:
threads caller frame `F_frame` (`ikit.identityAt ∗ kit.storeAt ∗ subStackGap`) into both `hmismatch`
and `hmatch`, and lifts Stage P2 OOM panics (`PanicOomProp s0`) into `Qpan` via `hpan` so `hmatch`
can continue into Stage P3 (`genP3S5PanicProp`). -/
def StageP2MatchedFramedCliStmt : Prop :=
  ∀ (W : CliHooks) (img : Obj.Image) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (F_frame : SepProp) (Q Qpan : State → SepProp → Prop),
    Obj.Loads libsignalSessionImage img →
    RunHooks img E2E.HooksE.A0 (cliExterns W) →
    img.base &&& 0xfff#64 = 0#64 →
    y.g.coins.length < 2 ^ 63 →
    SessMatchesPm sess y.g.msg →
    ImgCallInv img s1 →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    rootStack ≤ sp.toNat →
    s1.pc = closureEntry img (cliExterns W) + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qpan sf (Pf ∗ F_frame)) →
    (hmismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ sf Pf,
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 sf →
        sf.sp = s0.sp →
        sf.trace = s1.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        ImgCallInv img sf →
        (Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          apiDecResultAt E2E.HooksE.A0 y.out
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          coinsInstalled img y.g.coinsP y.g.coins ∗
          TokenInit img ∗
          logOff img ∗
          E2E.HooksE.A0.pool ∗
          stackAt sp rootStack) →
        Q sf (Pf ∗ F_frame)) →
    (hmatch : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ (s2 : State) (g : RecordGhost) (recG : SessionGhost)
        (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
        (preKeyMsgRem : SepProp)
        (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
        SessionExtraRel recG sess →
        (signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem ⊢
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) →
        Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 s2 →
        s2.pc = closureEntry img (cliExterns W) + 0x1778#64 →
        s2.status = .Running →
        s2.sp = sp →
        (s2.sp &&& 15#64 == 0#64) = true →
        s2.trace = s1.trace →
        s2.readReg64 .x19 = y.fut →
        s2.readReg64 .x27 = sp + 0x370#64 →
        s2.readReg64 .x29 = s0.sp - 0x60#64 →
        calleeSavedVRegs s2 = calleeSavedVRegs s0 →
        ImgCallInv img s2 →
        SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s2
          ((TokenInit img ∗
            genP3Pre E2E.HooksE.A0 img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
              whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
              recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
            stageP3Sub5ExtraPrePrevEmpty E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 g 0#8 ∗
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
            preKeyMsgRem) ∗ F_frame)
          Q Qpan) →
    SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s1
      ((stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
         (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
         (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt Scope E2E.HooksE.A0 y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
        protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
        coinsInstalled img y.g.coinsP y.g.coins ∗
        TokenInit img ∗
        logOff img ∗
        stackAt sp rootStack) ∗ F_frame)
      Q Qpan

/-! ## 3. Store Unpacking, Outer-Frame Adapter, & Stage P3 Reject Packaging -/

/-- Allocator-polymorphic counterpart of `storesAt_opened_entails_cliPollStoresKitsAt`. -/
theorem storesAt_opened_entails_cliPollStoresKitsAt_ext
    {A : RustAlloc} (b : BitVec 64) {P : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {me : AddrVal} {pm : PreKeySignalMessage}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : DpKitStk) (a : BitVec 64)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOk₀ P Scope F peer.val me pm) :
    storesAt A a StoresGhost.opened ⊢
      cliPollStoresKitsAt A b F Slots.scopeKit peer pid sid kid kbk σ a StoresGhost.opened :=
  storesAt_entails_cliPollStoresKitsAt b σ a StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hf) (cliIdOwnInv_opened hd) (cliIdInv_opened_peer hf)
    (cliPkInv_opened hd pid) (cliSpkInv_opened hd sid) (cliKpkInvFull_opened hd kid sid kbk)

/-- Unpacks `storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened` into `cliPollStoresKitsAt`
under `Scope ⊆ Slots.scopeIn`, `Slots.FilesOkPeer`, and `DecPkOk₀`. -/
theorem storesAt_opened_entails_cliPollStoresKitsAt
    (b : BitVec 64) {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {me : AddrVal} {pm : PreKeySignalMessage}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : DpKitStk) (a : BitVec 64)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOk₀ W Scope F peer.val me pm) :
    storesAt E2E.HooksE.A0 a StoresGhost.opened ⊢
      cliPollStoresKitsAt E2E.HooksE.A0 b F Slots.scopeKit peer pid sid kid kbk σ a
        StoresGhost.opened :=
  storesAt_opened_entails_cliPollStoresKitsAt_ext b σ a hsub hf hd

/-- Allocator- and extern-polymorphic counterpart of `sepWPp_pollGoal_frame`. -/
theorem sepWPp_pollGoal_frame_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S)) {s0 s1 : State} {P1 Fr_tail R : SepProp}
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).onPanic y s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 (P1 ∗ Fr_tail)
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).onPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps1f, ⟨hpcm, hrunm, P_f, hmf, hpost, hspf, hcs⟩ | ⟨hpanf, P_f, hmf, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hwp (Fr_tail ∗ R') hm hL
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps1f, Or.inl ⟨hpcm, hrunm, P_f ∗ Fr_tail, hmf, ?_, hspf, hcs⟩⟩
    intro hsteps0f hmR; rw [sepConj_assoc] at hmR; exact hpost hsteps0f hmR
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps1f, Or.inr (Or.inl ⟨hpanf, P_f ∗ Fr_tail, hmf, ?_⟩)⟩
    intro hsteps0f hmR; rw [sepConj_assoc] at hmR; exact hpan hsteps0f hmR
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Frames `Fr_tail` around a `SepWPp` whose normal and panic postconditions already expect
`Fr_tail ∗ R`. -/
theorem sepWPp_pollGoal_frame {img : Obj.Image} {W : CliHooks}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    {s0 s1 : State} {P1 Fr_tail R : SepProp}
    (hwp : SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s1 P1
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).onPanic y s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s1
      (P1 ∗ Fr_tail)
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).onPanic y s0 sf ∗ R)) :=
  sepWPp_pollGoal_frame_ext B S stk' y hwp

set_option maxHeartbeats 800000 in
/-- Allocator- and extern-polymorphic counterpart of `stageP3_exit_prevEmpty_to_pollPost` under
`TraceFsSound (tripleRatchetProgAtExt img.base ext)`. -/
theorem stageP3_exit_prevEmpty_to_pollPost_ext
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hfs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 s2 sf : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost P_f R : SepProp)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (e : SignalProtocolError)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg)
    (hdec : decPkDef X P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none)
    (hent : P_f ⊢
      ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (s2.sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmpty A img.base s0 s2 y.fut y.out e ∗
      genP3S5PostFrame A img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        coinsPost)
    (hsf_sp : sf.sp = s2.sp + 0xcd0#64)
    (htr_f : sf.trace = s0.trace)
    (hcs_f : ClosureCalleeSaved s0 sf)
    (hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0) :
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
    let F_p3 : SepProp :=
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
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      stageP1VtablesAt img kit ikit
    (Steps prog s0 sf → (sf.mem ⊨ (P_f ∗ F_p3) ∗ (Fr_tail ∗ R)) →
      (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
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
  let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .decryptionFailed)
  have hsf_sp0 : sf.sp = s0.sp := by rw [hsf_sp, hs2_sp, sp_frame_sub_add]
  have hcs_full : CalleeSavedPreserved s0 sf :=
    closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
  refine ⟨?_, hsf_sp0, hcs_full⟩
  intro hsteps0f hm_f
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm_f
  rw [hs2_sp] at hm1
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hexit := stageP3ErrPrevEmpty_entails_exit img y s0 s2 rngPtr whisperMsgPtr whisperG
    preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
    opkHi kyberPreKeyId signedPreKeyId e err hs2_sp hroot hmsg_fold
  dsimp only at hexit
  have hm2 : sf.mem ⊨
      ((((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
          memRegion (sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty A img.base s0 s2 y.fut y.out e ∗
          genP3S5PostFrame A img sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
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
        preKeyMsgRem) ∗
      (cliPollStoresKitsAt A img.base y.g.F Slots.scopeKit y.g.peer pid sid kid kbk σ
        y.g.stores StoresGhost.opened ∗
       memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ∗
       stageP1VtablesAt img kit ikit ∗ R) :=
    Arm64.Satisfies.mono
      (by dsimp only [cliPollStoresKitsAt, sp, σ, pid, sid, kid, kbk, kit, ikit]; sep_frame) hm1
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := A) img.base
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
  have hm3 := Arm64.Satisfies.mono (sepConj_mono hexit (sepConj_mono_left hstores)) hm2
  have hstk_join := (stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub).symm
  have hm4 : sf.mem ⊨
      (decResAt A y.out (.error err) ∗
        storesAt A y.g.stores StoresGhost.opened ∗
        protocolAddressAt A y.g.peer y.g.peerA ∗
        protocolAddressAt A y.g.me y.g.meA ∗
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
        logOff img ∗
        A.pool ∗
        (TokenInit img ∗ coinsPost ∗ stageP1VtablesAt img kit ikit) ∗
        dpFutDoneAt y.fut ∗
        memRegion y.cx 32 ∗
        memRegion sp 3280 ∗
        (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
          stackAt sp rootStack) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
    Arm64.Satisfies.mono (by dsimp only [sp]; sep_frame) hm3
  rw [hstk_join] at hm4
  have hout : slotOutTr
      (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      StoresGhost.opened (.error err) s0.trace sf.trace :=
    slotOutTr_of_reject StoresGhost.opened hS (err := err) nofun nofun hdec
  have hpost_goal := exit_entails_dpPollPost_ext B S stk' hneed hstk63 y s0 sf
    StoresGhost.opened (.error err) (TokenInit img ∗ coinsPost ∗ stageP1VtablesAt img kit ikit)
    hfs hsteps0f htr_f hout
  exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm4

/-- Packages both `hErr` and `hVerNe` exits of `StageP3PrevEmptyVRegsStmt` on Path B into
`dpPollSpecState.post`. -/
theorem stageP3_exit_prevEmpty_to_pollPost
    {img : Obj.Image} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 s2 sf : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost P_f R : SepProp)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (e : SignalProtocolError)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
    (hdec : decPkDef X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none)
    (hent : P_f ⊢
      ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (s2.sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmpty E2E.HooksE.A0 img.base s0 s2 y.fut y.out e ∗
      genP3S5PostFrame E2E.HooksE.A0 img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        coinsPost)
    (hsf_sp : sf.sp = s2.sp + 0xcd0#64)
    (htr_f : sf.trace = s0.trace)
    (hcs_f : ClosureCalleeSaved s0 sf)
    (hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0) :
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
    let F_p3 : SepProp :=
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
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      stageP1VtablesAt img kit ikit
    (Steps prog s0 sf → (sf.mem ⊨ (P_f ∗ F_p3) ∗ (Fr_tail ∗ R)) →
      (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf :=
  stageP3_exit_prevEmpty_to_pollPost_ext (P := ⟨W.C, W.Q⟩) B S hh.toExt.fs hS stk' hneed hstk63
    y s0 s2 sf rngPtr whisperMsgPtr whisperG preKeyMsgRem coinsPost P_f R
    opkHi kyberPreKeyId signedPreKeyId e hs2_sp hsp_sub hmsg_fold hdec hent
    hsf_sp htr_f hcs_f hvregs_f

/-- Precondition monotonicity for `SepWPp`. -/
theorem sepWPp_conseq_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qpan : State → SepProp → Prop}
    (hent : P ⊢ P') (hwp : SepWPp prog target s P' Q Qpan) :
    SepWPp prog target s P Q Qpan :=
  fun R' hm hL => hwp R' (Arm64.Satisfies.mono (sepConj_mono_left hent) hm) hL

/-- Allocator- and extern-polymorphic counterpart of `sepWPp_genP3_to_tailQpan`. -/
theorem sepWPp_genP3_to_tailQpan_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 s2 : State} {Pre Fr_tail R : SepProp} {Q : State → SepProp → Prop}
    (hpan : st.version = msgVer →
      (genP3S5Model C K rem loc msg rest st).1 = .error .panic →
      (dpSlotPollKState A img B S).panics y.g)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2 Pre Q
      (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2 Pre Q
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).onPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hnorm | ⟨hpanf, P_f, hmf, hgp⟩ | ⟨_, hoom⟩⟩ := hwp R' hm hL
  · exact ⟨sf, hsteps, Or.inl hnorm⟩
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpanf, P_f, hmf, ?_⟩)⟩
    intro _ hmR; rw [← sepConj_assoc] at hmR
    exact dpPollOnPanic_of_genP3 stk' y hgp hpan hmR
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Converts `genP3S5PanicProp` into the `Fr_tail`-framed `dpPollSpecState.onPanic` predicate. -/
theorem sepWPp_genP3_to_tailQpan {img : Obj.Image} {W : CliHooks}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 s2 : State} {P Fr_tail R : SepProp}
    {Q : State → SepProp → Prop}
    (hpan : st.version = msgVer →
      (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error .panic →
      (dpSlotPollKState E2E.HooksE.A0 img B S).panics y.g)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s2 P Q
      (genP3S5PanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s2 P Q
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf →
          (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).onPanic y s0 sf ∗ R)) :=
  sepWPp_genP3_to_tailQpan_ext B S stk' y hpan hwp

/-! ## 4. Stage-Decoupled `(P, A, ext)` Stage P2 / P3 Interfaces & Top-Level Path B Branch -/

/-- Stage-decoupled framed Stage P2 contract for Path B (`+0x0868 → +0x1778` / `x30`) at `(img, A, ext)`. -/
def StageP2MatchedFramedExtAt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState A img B S)) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (F_frame : SepProp) (Q Qpan : State → SepProp → Prop),
    img.base &&& 0xfff#64 = 0#64 → y.g.coins.length < 2 ^ 63 → SessMatchesPm sess y.g.msg →
    ImgCallInv img s1 → s0.trace <+: s1.trace → s1.sp = sp → sp + 0xcd0#64 = s0.sp →
    rootStack ≤ sp.toNat → s1.pc = closureEntry img ext + 0x0868#64 →
    s1.status = .Running → (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qpan sf (Pf ∗ F_frame)) →
    (hmismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        Steps (tripleRatchetProgAtExt img.base ext) s1 sf → sf.sp = s0.sp → sf.trace = s1.trace →
        ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
        (Pf ⊢ dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗
          apiDecResultAt A y.out (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗ protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗ coinsInstalled img y.g.coinsP y.g.coins ∗
          TokenInit img ∗ logOff img ∗ A.pool ∗ stackAt sp rootStack) →
        Q sf (Pf ∗ F_frame)) →
    (hmatch : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ (s2 : State) (g : RecordGhost) (recG : SessionGhost) (whisperMsgPtr : BitVec 64)
        (whisperG : SignalMessageGhost) (preKeyMsgRem : SepProp)
        (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
        SessionExtraRel recG sess →
        (signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem ⊢ preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg) →
        Steps (tripleRatchetProgAtExt img.base ext) s1 s2 →
        s2.pc = closureEntry img ext + 0x1778#64 → s2.status = .Running →
        s2.sp = sp → (s2.sp &&& 15#64 == 0#64) = true → s2.trace = s1.trace →
        s2.readReg64 .x19 = y.fut → s2.readReg64 .x27 = sp + 0x370#64 →
        s2.readReg64 .x29 = s0.sp - 0x60#64 → calleeSavedVRegs s2 = calleeSavedVRegs s0 →
        ImgCallInv img s2 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
          ((TokenInit img ∗
            genP3Pre A img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
              whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
              recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
            stageP3Sub5ExtraPrePrevEmpty A s0 s2 y.fut y.out 8#64 g 0#8 ∗
            stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
              (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
              (y.g.stores + 0x78#64) (kyberVt img) rngPtr
              (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
              (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
               ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗ memRegion (y.fut + 0x2a8#64) 4) ∗
            stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem) ∗ F_frame) Q Qpan) →
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      ((stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
         (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
         (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt Scope A y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗ protocolAddressAt A y.g.peer y.g.peerA ∗
        protocolAddressAt A y.g.me y.g.meA ∗ coinsInstalled img y.g.coinsP y.g.coins ∗
        TokenInit img ∗ logOff img ∗ stackAt sp rootStack) ∗ F_frame) Q Qpan

/-- Instantiates `StageP2MatchedFramedExtAt` at `(img, E2E.HooksE.A0, cliExterns W)` from
`StageP2MatchedFramedCliStmt`. -/
theorem stageP2MatchedFramedExtAt_of_cli {W : CliHooks} {img : Obj.Image}
    (hP2 : StageP2MatchedFramedCliStmt)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W)) :
    StageP2MatchedFramedExtAt img E2E.HooksE.A0 (cliExterns W) :=
  fun B S Scope y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_frame Q Qpan =>
    hP2 W img B S Scope y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_frame Q Qpan himg hh

/-- Contract-parameterized `(P, A, ext)` counterpart of `StageP2MatchedFramedCliStmt` under
`CliExternsOk P A ext` and `RunHooksExt img A (cliExternsWith ext)`. -/
def StageP2MatchedFramedExtStmt : Prop :=
  ∀ (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (_ : CliExternsOk P A ext) (img : Obj.Image),
    Obj.Loads libsignalSessionImage img →
    RunHooksExt img A (cliExternsWith ext) →
    StageP2MatchedFramedExtAt img A (cliExternsWith ext)

/-- Specializes `StageP2MatchedFramedExtStmt` at `(P, A, ext, img)`. -/
theorem stageP2MatchedFramedExtAt_of_extStmt
    (hP2 : StageP2MatchedFramedExtStmt)
    (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (hOk : CliExternsOk P A ext) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext)) :
    StageP2MatchedFramedExtAt img A (cliExternsWith ext) :=
  hP2 P A ext hOk img himg hh

/-- Stage-decoupled Path B Stage P3 (`+0x1778 → +0x34dc` / `x30`) contract at `(img, P, A, ext)`
(with `ctl = 0#64`, `C = P.C`, `K = P.Q.K`), free of 0-stack `AllocContracts`. -/
def StageP3GenPathBExtAt (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  ∀ (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
    (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop),
    initErrsPtr ≠ 0#64 →
    (st.remoteIdentity ≠ some st.localIdentity ∨
      WireEntries.DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
    SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
    img.FrozenLoaded s → s.symtab = img.symtab → s.pc = closureEntry img ext + 0x1778#64 →
    s.status = .Running → (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
    s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
    (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
        (s' : State) (P_s' : SepProp),
      st.version = msgVer → Record.CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
      (genP3S5Model P.C P.Q.K rem loc msg rest st).1 = .ok pt →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      Steps (tripleRatchetProgAtExt img.base ext) s s' →
      s'.pc = closureEntry img ext + 0x34dc#64 → s'.status = .Running →
      s'.sp = s.sp → s'.trace = s0.trace → calleeSavedVRegs s' = calleeSavedVRegs s0 →
      s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      img.FrozenLoaded s' → s'.symtab = img.symtab →
      (P_s' ⊢
        stageP3DispatchOkMidPrevEmpty A img.base s0 s coroPtr outPtr initErrsPtr
          ptCap ptPtr g pt b_2c0 G' (genP3S5Model P.C P.Q.K rem loc msg rest st).2 ∗
        genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (Coins.coinsAfter img.base cur rest
            (decryptDraws P.C st msg.senderRatchetKey rest))) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
        (genP3S5PanicProp P.C P.Q.K rem loc st msg msgVer rest s0)) →
    (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
      st.version = msgVer → Record.CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
      (genP3S5Model P.C P.Q.K rem loc msg rest st).1 = .error e → e ≠ .panic →
      (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr e ∗
        genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (Coins.coinsAfter img.base cur rest
            (decryptDraws P.C st msg.senderRatchetKey rest))) →
      sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → img.FrozenLoaded sf → sf.symtab = img.symtab →
      Q sf (P_f ∗ F_frame)) →
    (∀ (sf : State) (P_f : SepProp),
      st.version ≠ msgVer →
      (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) ∗
        genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (Coins.coinsAt img.base cur rest)) →
      sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → img.FrozenLoaded sf → sf.symtab = img.symtab →
      Q sf (P_f ∗ F_frame)) →
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
        F_frame) Q (genP3S5PanicProp P.C P.Q.K rem loc st msg msgVer rest s0)

/-- Instantiates `StageP3GenPathBExtAt` from `StageP3PrevEmptyVRegsStmt` and `PollPathBCallees`. -/
theorem stageP3GenPathBExtAt_of_callees {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (hP3 : StageP3PrevEmptyVRegsStmt) (hC : PollPathBCallees img P A B ext) :
    StageP3GenPathBExtAt img P A ext :=
  hP3 img ext P.C 0#64 P.Q.K hC.alloc hC.chainClone hC.senderChainClone hC.tryDecrypt hC.dropSs3

set_option maxHeartbeats 800000 in
/-- Stage-decoupled Path B top-level branch (`+0x0868 → s0.readReg64.x30`) over arbitrary
`(P, A, ext)` given `TraceFsSound`, `StageP2MatchedFramedExtAt`, `StageP3GenPathBExtAt`, and
`StageP4MatchedExtAt`. -/
theorem closure_pathB_ok_of_stages
    {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hP2B : StageP2MatchedFramedExtAt img A ext)
    (hP3B : StageP3GenPathBExtAt img P A ext)
    (hP4B : StageP4MatchedExtAt img A B ext)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsteps01 : Steps (tripleRatchetProgAtExt img.base ext) s0 s1)
    (htr1 : s1.trace = s0.trace) (hinv1 : ImgCallInv img s1)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = closureEntry img ext + 0x0868#64)
    (hrun1 : s1.status = .Running) (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img)) :
    let prog := tripleRatchetProgAtExt img.base ext
    let K := dpSlotPollKState A img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
         (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
         (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A y.fut (some r) ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗
       protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt A y.g.stores StoresGhost.opened ∗
       TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ∗ stageP1VtablesAt img kit ikit)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R)) := by
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
  obtain ⟨hloadS, hr_eq, hIn, hMatch, _, _, hSeeds, hRC, hPqLt⟩ :=
    pathB_scopeIn_and_match hinjK hsub hfPeer hdecOk hload_rel hcur
  subst hr_eq
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  let F_p2 : SepProp :=
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let Fr_tail : SepProp :=
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗ stageP1VtablesAt img kit ikit
  have hstores_in := storesAt_opened_entails_cliPollStoresKitsAt_ext (A := A) img.base σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hstk_split := stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub
  have hpre_split :
      stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
         (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
         (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗
       protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt A y.g.stores StoresGhost.opened ∗
       TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ∗ stageP1VtablesAt img kit ikit ⊢
      ((stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt Slots.scopeKit A y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A y.g.peer y.g.peerA ∗
        protocolAddressAt A y.g.me y.g.meA ∗
        coinsInstalled img y.g.coinsP y.g.coins ∗
        TokenInit img ∗ logOff img ∗ stackAt sp rootStack) ∗ F_p2) ∗ Fr_tail := by
    rw [hstk_split]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores_in))))))) ?_
    unfold cliPollStoresKitsAt F_p2 Fr_tail
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_ext (ext := ext) B S stk' y ?_)
  refine hP2B B S Slots.scopeKit y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_p2 _ _
    (cliBase_aligned himg) hcoins hMatch hinv1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hroot hpc1 hrun1 hsp_align1 hregs1 ?_ ?_ ?_
  · intro sf Pf hoom _ hm_pan
    have hm_pan' : sf.mem ⊨ (Pf ∗ (F_p2 ∗ Fr_tail)) ∗ R :=
      Arm64.Satisfies.mono (by sep_frame) hm_pan
    exact dpPollOnPanic_of_p3p4Oom stk' y hoom hm_pan'
  · intro hrem_ne sf Pf _ _ _ hsf_sp htr_f hcs_f hvregs_f _ hent_f
    let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_f)) hm_f
    have hdec_at := apiDecResultAt_proto_entails_decResAt A y.out
      (.invalidMessage .preKey .badCiphertext) err
    have hstores_out := cliPollStoresKitsAt_entails_storesAt (A := A) img.base
      (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    have hm2 : sf.mem ⊨
        apiDecResultAt A y.out (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        cliPollStoresKitsAt A img.base y.g.F Slots.scopeKit y.g.peer pid sid kid kbk σ
          y.g.stores StoresGhost.opened ∗
        (protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
          logOff img ∗ A.pool ∗
          (TokenInit img ∗ coinsInstalled img y.g.coinsP y.g.coins ∗ stageP1VtablesAt img kit ikit) ∗
          dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ memRegion sp 3280 ∗
          (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
            stackAt sp rootStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [cliPollStoresKitsAt, F_p2, Fr_tail]; sep_frame) hm1
    have hm3 := Arm64.Satisfies.mono (sepConj_mono hdec_at (sepConj_mono_left hstores_out)) hm2
    rw [← hstk_split] at hm3
    have hm4 : sf.mem ⊨
        (decResAt A y.out (.error err) ∗
          storesAt A y.g.stores StoresGhost.opened ∗
          protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
          logOff img ∗ A.pool ∗
          (TokenInit img ∗ coinsInstalled img y.g.coinsP y.g.coins ∗ stageP1VtablesAt img kit ikit) ∗
          dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by sep_frame) hm3
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS (err := err) nofun nofun
        (decPkDef_pathB_remId_ne X P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_ne)
    have hpost_goal := exit_entails_dpPollPost_ext B S stk' hneed hstk63 y s0 sf
      StoresGhost.opened (.error err)
      (TokenInit img ∗ coinsInstalled img y.g.coinsP y.g.coins ∗ stageP1VtablesAt img kit ikit)
      hFs hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm4
  · intro hrem_eq s2 g recG whisperMsgPtr whisperG preKeyMsgRem
      opkHi kyberPreKeyId signedPreKeyId hex hmsg_fold hsteps12 hpc2 hrun2
      hs2_sp hsp_align2 htr2 _ _ _ hvregs2 hinv2
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_ext hFs hsteps02 htr20).trans hf0
    have hpan_model : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error .panic →
        (dpSlotPollKState A img B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathB_panic X P Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS htrusted hMatch hrem_eq hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr
        (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
        (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
         ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗ memRegion (y.fut + 0x2a8#64) 4) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        (TokenInit img ∗
          genP3Pre A img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty A s0 s2 y.fut y.out 8#64 g 0#8 ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
            (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
            (y.g.stores + 0x78#64) (kyberVt img) rngPtr
            (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
            (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
             ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗ memRegion (y.fut + 0x2a8#64) 4) ∗
          stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem) ∗ F_p2 ⊢
        TokenInit img ∗
          genP3Pre A img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty A s0 s2 y.fut y.out 8#64 g 0#8 ∗ F_p3 := by
      dsimp only [F_p2, F_p3]; sep_frame
    refine sepWPp_conseq_pre hpre_p3
      (sepWPp_genP3_to_tailQpan_ext (ext := ext) (C := P.C) (K := P.Q.K) B S stk' y hpan_model ?_)
    refine hP3B himg
      s0 s2 y.fut y.cx y.out 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      g recG sess.state y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hinv2.1 hinv2.2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' pt ptCap ptPtr s' P_s' hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne
        hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
        hfz' hsym' hent_s'
      exact closure_pathB_p4_cont_of_stageP4 P A ext X B S Scope himg hFs hP4B hS stk' hneed hstk63
        y sess s0 s2 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R
        opkHi kyberPreKeyId signedPreKeyId g recG G₁ G' pt
        hfPeer hdecOk hIn hloadS htrusted hMatch hrem_eq hex hmsg_fold
        hs2_files htr20 hs2_sp hsp_sub hsp_align2 hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne
        hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
        hfz' hsym' hent_s'
    · intro G₁ G' e sf P_f hver _ _ herr hne_p hent_f hsf_sp htr_f hcs_f hvregs_f _ _
      exact stageP3_exit_prevEmpty_to_pollPost_ext (P := P) B S hFs hS stk' hneed hstk63
        y s0 s2 sf rngPtr whisperMsgPtr whisperG preKeyMsgRem _ P_f R
        opkHi kyberPreKeyId signedPreKeyId e hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_err X P Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS htrusted hMatch hrem_eq hver herr hne_p)
        hent_f hsf_sp htr_f hcs_f hvregs_f
    · intro sf P_f hver_ne hent_f hsf_sp htr_f hcs_f hvregs_f _ _
      exact stageP3_exit_prevEmpty_to_pollPost_ext (P := P) B S hFs hS stk' hneed hstk63
        y s0 s2 sf rngPtr whisperMsgPtr whisperG preKeyMsgRem _ P_f R
        opkHi kyberPreKeyId signedPreKeyId (.invalidMessage .preKey .decryptionFailed)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_ver_ne X P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_eq hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

/-- Callee-bundled corollary of `closure_pathB_ok_of_stages` from `StageP2MatchedFramedExtAt`,
`StageP3PrevEmptyVRegsStmt`, `StageP4MatchedExtStmt`, and `PollPathBCallees`. -/
theorem closure_pathB_ok_ext
    {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hP2 : StageP2MatchedFramedExtAt img A ext)
    (hP3 : StageP3PrevEmptyVRegsStmt)
    (hP4 : StageP4MatchedExtStmt)
    (hC : PollPathBCallees img P A B ext)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsteps01 : Steps (tripleRatchetProgAtExt img.base ext) s0 s1)
    (htr1 : s1.trace = s0.trace) (hinv1 : ImgCallInv img s1)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = closureEntry img ext + 0x0868#64)
    (hrun1 : s1.status = .Running) (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img)) :
    let prog := tripleRatchetProgAtExt img.base ext
    let K := dpSlotPollKState A img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
         (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
         (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A y.fut (some r) ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗
       protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt A y.g.stores StoresGhost.opened ∗
       TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ∗ stageP1VtablesAt img kit ikit)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R)) :=
  closure_pathB_ok_of_stages P A ext X B S Scope himg hFs hP2
    (stageP3GenPathBExtAt_of_callees hP3 hC) (stageP4MatchedExtAt_of_callees hP4 hC)
    hinjK hsub hS stk' hneed hstk63 y r sess s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel hcur hsteps01 htr1 hinv1
    hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-! ## 5. Fixed-Table Matched-Session Branch (`closure_pathB_ok`, `+0x0868 → s0.readReg64 .x30`) -/

theorem closure_pathB_ok
    (hP2 : StageP2MatchedFramedCliStmt)
    (hP3 : StageP3PrevEmptyVRegsStmt)
    (hP4 : StageP4MatchedExtStmt)
    {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsteps01 : Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hinv1 : ImgCallInv img s1)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = closureEntry img (cliExterns W) + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img)) :
    let prog := tripleRatchetProgAtExt img.base (cliExterns W)
    let K := dpSlotPollKState E2E.HooksE.A0 img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
         (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
         (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some r) ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ∗
       stageP1VtablesAt img kit ikit)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R)) := by
  have hC : PollPathBCallees img ⟨W.C, W.Q⟩ E2E.HooksE.A0 B (cliExterns W) :=
    { alloc := cliAllocContracts hh
      chainClone := cliChainClone3_ok hh
      senderChainClone := cliSenderChainClone3_ok hh
      tryDecrypt := cliTryDecryptPqV1_ok W 0#64 himg
      dropSs3 := cliDropSessionStructure3_ok hh
      sessKitOk := fun F0 peer =>
        cliPollSess_kitOkSE_of_deser W himg F0 Slots.scopeKit peer B hDeser
      idKitOk := fun F0 peer =>
        cliPollId_kitOkIE W himg F0 peer B }
  exact closure_pathB_ok_of_stages ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliExterns W) X B S Scope
    himg hh.toExt.fs (stageP2MatchedFramedExtAt_of_cli hP2 himg hh)
    (stageP3GenPathBExtAt_of_callees hP3 hC) (stageP4MatchedExtAt_of_callees hP4 hC)
    hinjK hsub hS stk' hneed hstk63 y r sess s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel hcur hsteps01 htr1 hinv1
    hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
