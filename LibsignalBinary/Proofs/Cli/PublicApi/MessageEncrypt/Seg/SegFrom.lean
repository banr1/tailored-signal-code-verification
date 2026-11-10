/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import ProofLib.RegChain

/-!
# CLI `SegFrom` Proof (`Cur` → `Otr`)

Proves `segFrom_okV` (`+0x20c..+0x2c8`), calling `OutgoingTripleRatchet::from_session_state` on
the current `SessionState` and branching to `Otr` (`+0x2c8`) on `Ok` or the error tail (`+0x49c`)
on `Err`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HKDF CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Encrypt

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

private theorem allocFailedIn_trans {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace) (hmf : allocFailedIn sm sf) :
    allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := h0m
  unfold allocFailedIn at hmf ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at hmf
  exact List.mem_of_mem_drop hmf

private theorem fromSessionState_error_ne_invalidState
    {st : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .error e) :
    e ≠ .invalidState ∧ e ≠ .panic := by
  unfold Mut.exec OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hs : st.senderChain with _ | sc <;> rcases hr : st.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq, Except.error.injEq] at h
  all_goals
    (try split_ifs at h) <;>
    (try simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.error.injEq] at h) <;>
    (subst h; decide)

private theorem execOk_fromSessionState_of_error
    {st : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .error e) :
    execOk OutgoingTripleRatchet.fromSessionState st = .error e := by
  unfold execOk
  rcases hm : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

private theorem execOk_fromSessionState_of_ok
    {st : SessionState (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .ok otr) :
    execOk OutgoingTripleRatchet.fromSessionState st =
      .ok (otr, (Mut.exec OutgoingTripleRatchet.fromSessionState st).2) := by
  unfold execOk
  rcases hm : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

private theorem model_of_fromSessionState_error
    {C : Crypto} {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {e : SignalProtocolError}
    (hcur : r.currentSession = some sess)
    (herr : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error e) :
    x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (.protocol e), [.loadSession x.rem.val]) ∧
    x.draws S (okAnswers r .newOrUnchanged) = 0 := by
  have hex : execOk OutgoingTripleRatchet.fromSessionState sess.state = .error e :=
    execOk_fromSessionState_of_error herr
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl (fromSessionState_error_ne_invalidState herr).2
  have hmod : x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol okAnswers
    simp only [hcur, hex, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      ExceptT.run, StateT.run, bind, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
      StateT.bind, StateT.map, Functor.map, liftM, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, pure, ExceptT.pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw, List.nil_append]
  refine ⟨by rw [hmod, hprot], ?_⟩
  unfold EncryptGhost.draws EncryptGhost.sendState loadedSession okAnswers
  simp only [hcur, hex]

open CryptoVerification.LibsignalPublicApi.StoreKit

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop} (h : next s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next :=
  fun _ => ⟨s, Steps.refl s, Or.inl h⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop} (h : next s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next :=
  fun _ => ⟨s, Steps.refl s, Or.inl h⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_false_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hfalse | hout⟩ := h hL
  · exact False.elim hfalse
  · exact ⟨sf, hsteps, Or.inr hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_false {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hfalse | hout⟩ := h hL
  · exact False.elim hfalse
  · exact ⟨sf, hsteps, Or.inr hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {mid : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R))
    (hwp : SepWP (trTrapProgAt img.base C abs) mid s P post)
    (hcont : ∀ sm Pm, (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      Steps (trTrapProgAt img.base C abs) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) →
      post sm Pm → CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {mid : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R))
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) mid s P post)
    (hcont : ∀ sm Pm, (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      Steps (tripleRatchetProgAt img.base C ctl abs) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) →
      post sm Pm → CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.call_trap {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (trTrapProgAt img.base C abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (trTrapProgAt img.base C abs) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0))
    (hnext : ∀ sm : State, (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      Steps (trTrapProgAt img.base C abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome xc (F ∗ R) s hpc hrun hm hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (hoom sm _ _hoom_st _hoom_post).elim

set_option linter.unusedVariables false in

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.call {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (tripleRatchetProgAt img.base C ctl abs) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0))
    (hnext : ∀ sm : State, (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      Steps (tripleRatchetProgAt img.base C ctl abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome xc (F ∗ R) s hpc hrun hm hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (hoom sm _ _hoom_st _hoom_post).elim

set_option linter.unusedVariables false in
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (_img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (sp : BitVec 64) (s0 : State) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
  memRegion (sp + 0x288#64) 0x1e0 ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
  memRegion x.ret 248 ∗
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter _img.base x.cur x.rest 0 ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - smallRootStack) ∗
  encSavedRegs s0.sp s0

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.curState_mem_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (sp : BitVec 64) (R : SepProp) (s0 : State) {m : Memory}
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hcur : r.currentSession = some sess)
    (hm : m ⊨ (sessionRecordAt A (sp + 0x110#64) g r ∗
      memRegion (sp + 0x280#64) 0x1e8 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R) :
    ∃ G u280,
      g.cur = some G ∧ sessionPure G sess ∧
      (m ⊨ ((sp + 0x280#64) ↦₆₄ u280) ∗
        ((sessionStateAt A (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x580#64) 200 ∗
          logOff img ∗
          stackAt sp smallRootStack ∗
          A.pool ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame ss_vt id_vt A ctl img x g sp s0) ∗ R)) := by
  simp only [sepConj_assoc] at hm
  obtain ⟨G, hgcur, hpure, hm⟩ := sessionRecordAt_cur_some A sp g r sess hcur hm
  have h280 : memRegion (sp + 0x280#64) 0x1e8 =
      memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x288#64) 0x1e0 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using mr_cut_add sp 0x280 8 0x1e0 (by decide)
  have h46a : memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 200 ∗
      memRegion (sp + 0x648#64) 0x538 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 200 0x538 (by decide)]
  rw [h280, ProofLib.memRegion_eight (sp + 0x280#64), h46a] at hm
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon at hm
  rw [hsp0, stackAt_sub sp encSubStack smallRootStack] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨u280, hm⟩ := hm
  refine ⟨G, u280, hgcur, hpure, ?_⟩
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_pre_frame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (sp : BitVec 64) (R Pm : SepProp) (s0 s1 : State)
    (hfl : img.FrozenLoaded s1) (hsym : s1.symtab = img.symtab)
    (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x128#64)
    (hx8 : s1.readReg64 .x8 = sp + 0x580#64)
    (hPm : Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))
    (hm : s1.mem ⊨ Pm ∗
      ((sessionStateAt A (sp + 0x128#64) G sess.state ∗
        memRegion (sp + 0x580#64) 200 ∗
        logOff img ∗
        stackAt sp smallRootStack ∗
        A.pool ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame ss_vt id_vt A ctl img x g sp s0) ∗ R)) :
    s1.mem ⊨ (otrFromSpec A img).pre ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ s1 ∗
      ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame ss_vt id_vt A ctl img x g sp s0) ∗ R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold otrFromSpec Spec.inImage
  dsimp only
  rw [hsp1]
  have hpure : (⌜img.FrozenLoaded s1 ∧ s1.symtab = img.symtab⌝ : SepProp) ∗
      ⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sessionStateAt A (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x580#64) 200 ∗
          logOff img ∗
          stackAt sp smallRootStack ∗
          A.pool ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame ss_vt id_vt A ctl img x g sp s0) ∗ R)) =
      (((⌜img.FrozenLoaded s1 ∧ s1.symtab = img.symtab⌝ ∗
        ⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
        sessionStateAt A (sp + 0x128#64) G sess.state ∗
        memRegion (sp + 0x580#64) 200 ∗
        logOff img ∗
        stackAt sp smallRootStack ∗
        A.pool) ∗
        ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame ss_vt id_vt A ctl img x g sp s0) ∗ R))) := by
    ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨⟨hfl, hsym⟩, ⟨hx0, hx8⟩, hm'⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_panic_bridge {img : Obj.Image} {A : RustAlloc}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64)
    (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (xc : OtrFromGhost) (F X R0 : SepProp) (s0 s1 sf : State)
    (hxc : xc.st = sess.state)
    (_ : r.currentSession = some sess)
    (htr1 : s1.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hpost : sf.mem ⊨ ((otrFromSpec A img).onPanic xc s1 sf ∗ F) ∗ (X ∗ R0)) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0 := by
  unfold otrFromSpec Spec.inImage at hpost
  dsimp only at hpost
  have h1 : sf.mem ⊨ ⌜(xc.model.1 = .error .panic ∨ allocFailedIn s1 sf) ∧ s1.trace <+: sf.trace⌝ ∗
      ((anyHeap ∗ F ∗ X) ∗ R0) :=
    Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hpan_or, hpref1⟩, hmem⟩
  have hany : anyHeap ∗ F ∗ X ⊢ anyHeap := entails_anyHeap _
  have hmem' : sf.mem ⊨ anyHeap ∗ R0 :=
    Satisfies.mono (sepConj_mono_left hany) hmem
  have hpref01 : s0.trace <+: s1.trace := by
    rw [htr1]
    exact List.prefix_append _ _
  have hpref0f : s0.trace <+: sf.trace := hpref01.trans hpref1
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV Spec.inImage
  dsimp only
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hpref0f, ?_⟩, hmem'⟩
  rcases hpan_or with herr | halloc
  · unfold OtrFromGhost.model at herr
    rw [hxc] at herr
    exact False.elim ((fromSessionState_error_ne_invalidState herr).2 rfl)
  · exact Or.inl (allocFailedIn_trans hpref01 halloc)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_post_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (xc : OtrFromGhost) (sp : BitVec 64) (R : SepProp)
    (s0 s1 s2 : State)
    (hxc : xc = ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpure : sessionPure G sess)
    (hpost : s2.mem ⊨ ((otrFromSpec A img).post xc s1 s2 ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame ss_vt id_vt A ctl img x g sp s0)) ∗ R) :
    ∃ G' : SessionGhost,
      xc.model.1 ≠ .error .panic ∧ s2.trace = s1.trace ∧
      (s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq xc.model.1 ∗
        sessionRecordAt A (sp + 0x110#64) { g with cur := some G' } (takenRecord sess xc.model.2) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        memRegion (sp + 0x288#64) 0x1e0 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
        curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
        memRegion x.ret 248 ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R) := by
  subst hxc
  let xc : OtrFromGhost := ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
  unfold otrFromSpec Spec.inImage at hpost
  dsimp only at hpost
  rw [hsp1] at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨G', hpost⟩ := hpost
  have h1 : s2.mem ⊨ ⌜xc.model.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
      ⌜G.AgreeExceptPq G'⌝ ∗
      ((sessionStateAt A (sp + 0x128#64) G' xc.model.2 ∗
        otrResultAt A (sp + 0x580#64) G.pq xc.model.1 ∗
        logOff img ∗ stackAt sp smallRootStack ∗ A.pool ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame ss_vt id_vt A ctl img x g sp s0) ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hne, htr⟩, hagr, hmem⟩
  refine ⟨G', hne, htr, ?_⟩
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.fromRestFrame at hmem
  have hrec := sessionRecordAt_taken_fold A sp g sess G G' xc.model.2 hpure hagr
  have hmem_rearr : s2.mem ⊨
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G' xc.model.2) ∗
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - smallRootStack) ∗
        stackAt sp smallRootStack) ∗
      otrResultAt A (sp + 0x580#64) G.pq xc.model.1 ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      memRegion (sp + 0x288#64) 0x1e0 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
      memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗
      encSavedRegs s0.sp s0 ∗ A.pool ∗ R :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack smallRootStack] at hmem_rearr
  have hmem_fold := Satisfies.mono (sepConj_mono_left hrec) hmem_rearr
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
  rw [hsp0]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem_fold

private theorem list_len6 {α : Type} (ws : List α) (h : ws.length = 6) :
    ∃ w0 w1 w2 w3 w4 w5, ws = [w0, w1, w2, w3, w4, w5] := by
  rcases ws with _ | ⟨w0, ws⟩; · nomatch h
  rcases ws with _ | ⟨w1, ws⟩; · nomatch h
  rcases ws with _ | ⟨w2, ws⟩; · nomatch h
  rcases ws with _ | ⟨w3, ws⟩; · nomatch h
  rcases ws with _ | ⟨w4, ws⟩; · nomatch h
  rcases ws with _ | ⟨w5, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨w0, w1, w2, w3, w4, w5, rfl⟩
  · nomatch h

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_err_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (g' : RecordGhost) (pq : VecPin)
    (sess : Session (List (BitVec 8))) (st' : SessionState (List (BitVec 8)))
    (p : SignalProtocolError) (sp : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hres : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error p)
    (hm : s2.mem ⊨ otrResultAt A (sp + 0x580#64) pq (.error p) ∗
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      memRegion (sp + 0x288#64) 0x1e0 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x648#64) 0x538 ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R) :
    ∃ w0 w1 w2 w3 w4 w5 H,
      SpeStaged A x.ret (.protocol p) [w0, w1, w2, w3, w4, w5] H ∧
      (s2.mem ⊨ ((sp + 0x580#64) ↦₆₄ errTag) ∗
        ((words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
          memRegion (sp + 0x5b8#64) 144 ∗ H ∗
          sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
          ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          memRegion (sp + 0x288#64) 0x1e0 ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
          curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
          memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
          memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0) ∗ R)) := by
  have hp_inv : p ≠ .invalidState := (fromSessionState_error_ne_invalidState hres).1
  have hp_pan : (ApiError.protocol p : ApiError AddrVal Unit) ≠ .panic := by
    intro h
    cases h
  unfold otrResultAt errResultAt at hm
  dsimp only at hm
  have h588 : (sp + 0x580#64) + 8#64 = sp + 0x588#64 := by bv_omega
  have h5b8 : (sp + 0x580#64) + 56#64 = sp + 0x5b8#64 := by bv_omega
  rw [h588, h5b8, speAt_fnName_eq A [] (utf8 "encrypt") (sp + 0x588#64) p hp_inv] at hm
  change s2.mem ⊨ (((sp + 0x580#64) ↦₆₄ errTag) ∗
      encErrAt A (sp + 0x588#64) (.protocol p) ∗
      memRegion (sp + 0x5b8#64) 144) ∗
    sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
    memRegion (sp + 0x288#64) 0x1e0 ∗
    ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
    curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
    memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R at hm
  have hstage := speStaged_of_encErrAt A (sp + 0x588#64) x.ret (.protocol p) hp_pan
  have hm_st := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hstage))) hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_st
  obtain ⟨ws, H, hm_st⟩ := hm_st
  have hm_pure : s2.mem ⊨ ⌜SpeStaged A x.ret (.protocol p) ws H⌝ ∗
      (((sp + 0x580#64) ↦₆₄ errTag) ∗
        ((words64At (sp + 0x588#64) ws ∗
          memRegion (sp + 0x5b8#64) 144 ∗ H ∗
          sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
          ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          memRegion (sp + 0x288#64) 0x1e0 ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
          curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
          memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
          memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0) ∗ R)) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm_st
  rw [satisfies_pure_sepConj] at hm_pure
  rcases hm_pure with ⟨hst, hm_out⟩
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ := list_len6 ws hst.2.1
  exact ⟨w0, w1, w2, w3, w4, w5, H, hst, hm_out⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_err_tail_mem {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (sess : Session (List (BitVec 8))) (st' : SessionState (List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (sp : BitVec 64) (H R Pm : SepProp) (s0 s3 : State)
    (hPm : Pm ⊢ (sp + 0x580#64) ↦₆₄ errTag)
    (hm : s3.mem ⊨ Pm ∗
      ((words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        memRegion (sp + 0x5b8#64) 144 ∗ H ∗
        sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        memRegion (sp + 0x288#64) 0x1e0 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
        curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x648#64) 0x538 ∗
        memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0) ∗ R)) :
    s3.mem ⊨ (curScratch sp ∗
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
      memRegion (sp + 0x280#64) 0x1ea ∗
      pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
      encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left (Entails.trans hPm (pointsTo64_entails_memRegion _ _))) hm
  have h280_1ea :
      memRegion (sp + 0x280#64) 0x1ea =
      memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x288#64) 0x1e0 ∗
        memRegion (sp + 0x468#64) 1 ∗ memRegion (sp + 0x469#64) 1 := by
    rw [show sp + 0x280#64 = sp + BitVec.ofNat 64 0x280 from rfl,
        mr_cut_add sp 0x280 8 0x1e2 (by decide),
        mr_cut_add sp (0x280 + 8) 0x1e0 2 (by decide),
        mr_cut_add sp (0x280 + 8 + 0x1e0) 1 1 (by decide)]
  have h280_ent :
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 0x1e0 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ⊢
      memRegion (sp + 0x280#64) 0x1ea := by
    rw [h280_1ea]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo8_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _)))
  have hpoll_eq :
      pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 ∗
        words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        memRegion (sp + 0x5b8#64) 144 ∗ memRegion (sp + 0x648#64) 0x538 := by
    have h1 : memRegion (sp + 0x46a#64) (0x588 - 0x46a) =
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 :=
      mr_cut_add sp 0x46a 0x116 8 (by decide)
    have h2 : memRegion (sp + BitVec.ofNat 64 (0x588 + 8 * 6)) (0xb80 - (0x588 + 8 * 6)) =
        memRegion (sp + 0x5b8#64) 144 ∗ memRegion (sp + 0x648#64) 0x538 :=
      mr_cut_add sp (0x588 + 8 * 6) 144 0x538 (by decide)
    unfold pollWith
    dsimp only [List.length_cons, List.length_nil]
    rw [h1, h2]
    ac_rfl
  have hm_rearr : s3.mem ⊨
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 0x1e0 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
      curScratch sp ∗
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 ∗
        words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        memRegion (sp + 0x5b8#64) 144 ∗ memRegion (sp + 0x648#64) 0x538) ∗
      H ∗ encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm1
  rw [← hpoll_eq] at hm_rearr
  have hm_out := Satisfies.mono (sepConj_mono_left h280_ent) hm_rearr
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm_out

private theorem memRegion_24_exists_words (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 24 ∗ R) :
    ∃ w0 w1 w2 : BitVec 64,
      m ⊨ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := memRegion_exists_words64At 3 a (by decide) hm
  rcases ws with _ | ⟨w0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hws
    exact ⟨w0, w1, w2, Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hws⟩
  · nomatch hlen

private theorem words_entails_memRegion_24 (a w0 w1 w2 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ⊢ memRegion a 24 := by
  have h := words64At_entails_memRegion [w0, w1, w2] a
    (by simp only [List.length_cons, List.length_nil]; decide)
  simpa only [words64At, List.length_cons, List.length_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

private theorem memRegion_200_exists_otrWords25 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 200 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
        BitVec 64,
      m ⊨ otrWords25 a d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20
        d21 d22 d23 d24 ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := memRegion_exists_words64At 25 a (by decide) hm
  rcases ws with _ | ⟨d0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d3, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d4, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d5, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d6, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d7, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d8, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d9, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d10, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d11, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d12, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d13, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d14, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d15, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d16, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d17, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d18, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d19, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d20, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d21, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d22, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d23, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d24, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · rw [← otrWords25_eq_words64At] at hws
    exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24, hws⟩
  · nomatch hlen

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.okStepFrame (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (g' : RecordGhost) (sess : Session (List (BitVec 8)))
    (st' : SessionState (List (BitVec 8))) (sp : BitVec 64) (H : SepProp) (s0 : State) : SepProp :=
  H ∗
  sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
  memRegion (sp + 0x350#64) 0x118 ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x648#64) 0x208 ∗
  memRegion (sp + 0x868#64) 0xe8 ∗
  memRegion (sp + 0x968#64) 0x218 ∗
  memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_ok_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (g' : RecordGhost) (pq : VecPin)
    (sess : Session (List (BitVec 8))) (st' : SessionState (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (sp : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hm : s2.mem ⊨ otrResultAt A (sp + 0x580#64) pq (.ok otr) ∗
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      memRegion (sp + 0x288#64) 0x1e0 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x648#64) 0x538 ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R) :
    ∃ (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
        BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
        BitVec 64)
      (u850 u858 u860 u950 u958 u960 : BitVec 64) (H : SepProp),
      pq.cap + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        otrWords25 dst pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
          w19 w20 w21 w22 w23 w24 ∗ H ⊢ otrAt A dst pq.cap pq.ptr otr) ∧
      (s2.mem ⊨ (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
            d18 d19 d20 d21 d22 d23 d24 ∗
          ((sp + 0x469#64) ↦₈ 0#8) ∗
          otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗ ((sp + 0x860#64) ↦₆₄ u860) ∗
          ((sp + 0x950#64) ↦₆₄ u950) ∗ ((sp + 0x958#64) ↦₆₄ u958) ∗ ((sp + 0x960#64) ↦₆₄ u960)) ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.okStepFrame ss_vt id_vt A ctl img x g' sess st' sp H s0 ∗ R)) := by
  unfold otrResultAt at hm
  dsimp only at hm
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
    w19, w20, w21, w22, w23, w24, H, hpq, hm, hpack⟩ :=
    otrAt_relocate A (sp + 0x580#64) pq.cap pq.ptr otr hm
  have h288 : memRegion (sp + 0x288#64) 0x1e0 =
      memRegion (sp + 0x288#64) 200 ∗ memRegion (sp + 0x350#64) 0x118 := by
    rw [show sp + 0x288#64 = sp + BitVec.ofNat 64 0x288 from rfl,
        mr_cut_add sp 0x288 200 0x118 (by decide)]
  have h648 : memRegion (sp + 0x648#64) 0x538 =
      memRegion (sp + 0x648#64) 0x208 ∗ memRegion (sp + 0x850#64) 24 ∗
      memRegion (sp + 0x868#64) 0xe8 ∗ memRegion (sp + 0x950#64) 24 ∗
      memRegion (sp + 0x968#64) 0x218 := by
    rw [show sp + 0x648#64 = sp + BitVec.ofNat 64 0x648 from rfl,
        mr_cut_add sp 0x648 0x208 0x330 (by decide),
        mr_cut_add sp (0x648 + 0x208) 24 0x318 (by decide),
        mr_cut_add sp (0x648 + 0x208 + 24) 0xe8 0x230 (by decide),
        mr_cut_add sp (0x648 + 0x208 + 24 + 0xe8) 24 0x218 (by decide)]
  rw [h288, h648] at hm
  have hm_d : s2.mem ⊨ memRegion (sp + 0x288#64) 200 ∗
      (memRegion (sp + 0x850#64) 24 ∗ memRegion (sp + 0x950#64) 24 ∗
        otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x469#64) ↦₈ 0#8) ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.okStepFrame ss_vt id_vt A ctl img x g' sess st' sp H s0 ∗ R) := by
    unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.okStepFrame
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
    d19, d20, d21, d22, d23, d24, hm_d⟩ := memRegion_200_exists_otrWords25 (sp + 0x288#64) hm_d
  have hm_850 : s2.mem ⊨ memRegion (sp + 0x850#64) 24 ∗
      (memRegion (sp + 0x950#64) 24 ∗
        otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
          d18 d19 d20 d21 d22 d23 d24 ∗
        otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x469#64) ↦₈ 0#8) ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.okStepFrame ss_vt id_vt A ctl img x g' sess st' sp H s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm_d
  obtain ⟨u850, u858, u860, hm_850⟩ := memRegion_24_exists_words (sp + 0x850#64) hm_850
  have hm_950 : s2.mem ⊨ memRegion (sp + 0x950#64) 24 ∗
      (((sp + 0x850#64) ↦₆₄ u850) ∗ (((sp + 0x850#64) + 8#64) ↦₆₄ u858) ∗
        (((sp + 0x850#64) + 16#64) ↦₆₄ u860) ∗
        otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
          d18 d19 d20 d21 d22 d23 d24 ∗
        otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x469#64) ↦₈ 0#8) ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.okStepFrame ss_vt id_vt A ctl img x g' sess st' sp H s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm_850
  obtain ⟨u950, u958, u960, hm_950⟩ := memRegion_24_exists_words (sp + 0x950#64) hm_950
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm_950
  refine ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
    w19, w20, w21, w22, w23, w24,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
    d19, d20, d21, d22, d23, d24,
    u850, u858, u860, u950, u958, u960, H, hpq, hpack, ?_⟩
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm_950

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_ok_pack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (g' : RecordGhost) (pq : VecPin)
    (sess : Session (List (BitVec 8))) (st' : SessionState (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64)
    (sp : BitVec 64) (H R Pm : SepProp) (s0 s3 : State)
    (hpack : ∀ dst : BitVec 64,
      otrWords25 dst pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
        w19 w20 w21 w22 w23 w24 ∗ H ⊢ otrAt A dst pq.cap pq.ptr otr)
    (hPm : Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      otrWords25 (sp + 0x288#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        w17 w18 w19 w20 w21 w22 w23 w24 ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        w17 w18 w19 w20 w21 w22 w23 w24 ∗
      ((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6) ∗
      ((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6))
    (hm : s3.mem ⊨ Pm ∗ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.okStepFrame ss_vt id_vt A ctl img x g' sess st' sp H s0 ∗ R)) :
    s3.mem ⊨ (takenSlots A sp sess st' ∗ otrAt A (sp + 0x288#64) pq.cap pq.ptr otr ∗
      memRegion (sp + 0x350#64) 0x118) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.okStepFrame at hm1
  have hotr_src :
      otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        w17 w18 w19 w20 w21 w22 w23 w24 ⊢ memRegion (sp + 0x580#64) 200 :=
    otrWords25_entails_memRegion (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12
      w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
  have h850 :
      ((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6) ⊢
      memRegion (sp + 0x850#64) 24 := by
    have h := words_entails_memRegion_24 (sp + 0x850#64) w4 w5 w6
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have h950 :
      ((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6) ⊢
      memRegion (sp + 0x950#64) 24 := by
    have h := words_entails_memRegion_24 (sp + 0x950#64) w4 w5 w6
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 200 ∗
        memRegion (sp + 0x648#64) 0x208 ∗ memRegion (sp + 0x850#64) 24 ∗
        memRegion (sp + 0x868#64) 0xe8 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0x968#64) 0x218 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 200 0x538 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 200) 0x208 0x330 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 200 + 0x208) 24 0x318 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 200 + 0x208 + 24) 0xe8 0x230 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 200 + 0x208 + 24 + 0xe8) 24 0x218 (by decide)]
  have hrec_ex :
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ⊢
      ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess st') :=
    Entails.sepExists_right g' (Entails.refl _)
  have hm_rearr : s3.mem ⊨
      ((otrWords25 (sp + 0x288#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗ H) ∗
        sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
        otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        (((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6)) ∗
        (((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6))) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x648#64) 0x208 ∗
      memRegion (sp + 0x868#64) 0xe8 ∗
      memRegion (sp + 0x968#64) 0x218 ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono_left
      (sepConj_mono (hpack (sp + 0x288#64))
        (sepConj_mono hrec_ex
          (sepConj_mono hotr_src (sepConj_mono h850 h950))))) hm_rearr
  have hm_poll : s3.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 200 ∗
        memRegion (sp + 0x648#64) 0x208 ∗ memRegion (sp + 0x850#64) 24 ∗
        memRegion (sp + 0x868#64) 0xe8 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0x968#64) 0x218) ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess st')) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pq.cap pq.ptr otr ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ R :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll
  unfold takenSlots
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm_poll

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_okV_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r g sess R0 s0 s hcurState
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hcurState with ⟨hcur, hsc, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx20, hx21, hx25, hx26, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 524#64 := by
    simpa only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.curPC, hentry] using hs_pc
  obtain ⟨G, u280, _, hpure, hm_unp⟩ := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.curState_mem_unpack A ctl img x r g sess sp R s0 hsp0 hcur hm
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP_trap hm_unp
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_pre_trap hs_pc' hrun hsp hal hx20 hx21 hx25 hx26 hx28) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x21, hs1_x24, hs1_x25, hs1_x26,
      hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have ⟨hfl1, hsym1⟩ := callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hs1_pc' : s1.pc = (trTrapProgAt img.base C abs).fnAddr otrFromName := by
    rw [hs1_pc, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_addr_eq_trap]
  have hm1_pre := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_pre_frame A ctl img x g G sess sp R Pm1 s0 s1
    hfl1 hsym1 hs1_sp hs1_x0 hs1_x8 hPm1 hm1
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.call_trap env.callees.otrFrom ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
    hs1_pc' hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (otrFromSpec A img).onExit ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_panic_bridge kit st0 ikit ist0 C ctl S encRecord x r sess
      ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ _ _ R0 s0 s1 sf rfl hcur (hs1_tr.trans htr) hpost)
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x20 : s2.readReg64 .x20 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x26 : s2.readReg64 .x26 = sp + 0x9d0#64 := by reg_chain
  have hs2_x27 : s2.readReg64 .x27 = sp + 0xc0#64 := by reg_chain
  have hs2_x28 : s2.readReg64 .x28 = sp + 0x4a0#64 := by reg_chain
  obtain ⟨G', _, hs2_tr, hm2⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_post_unpack A ctl img x g G sess ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
      sp R s0 s1 s2 rfl hsp0 hs1_sp hpure hpost2
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  rcases hres : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 with p | otr
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w0, w1, w2, w3, w4, w5, H, hst, hm2_err⟩ :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_err_unpack A ctl img x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 p sp R s0 s2 hres hm2
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP_trap hm2_err (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_err_trap hs2_pc hs2_run hs2_sp' hs2_al) ?_
    intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x21, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have ⟨hfl3, hsym3⟩ := callInv_steps hfl2 hsym2 hsteps23 hL2
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have ⟨hmod_res, hdraws0⟩ := model_of_fromSessionState_error (C := C) (S := S)
      (x := x) hcur hres
    have hm3_tail := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_err_tail_mem A ctl img x { g with cur := some G' } sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 w0 w1 w2 w3 w4 w5 sp H R Pm3
      s0 s3 hPm3 hm3
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_false_trap (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.tailFromSessionStateErr_ok_trap env x R0 s0 s3
      (okAnswers r .newOrUnchanged)
      (.protocol p) w0 w1 w2 w3 w4 w5 H { g with cur := some G' }
      (takenRecord sess (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2)
      ?_ hst ?_)
    · refine ⟨⟨by rw [hmod_res], by rw [hmod_res]; exact ⟨hsc.2, trivial⟩, by rw [hmod_res]; trivial⟩, ?_⟩
      rw [hs3_tr, hs2_tr', hmod_res]
      dsimp only [okAnswers]
      rw [ikit.traceOfWith_load]
    · refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
        by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
        ⟨by reg_chain, by reg_chain, by reg_chain, by reg_chain⟩, hstk, ?_⟩
      · rw [hs3_pc, hentry]
      · rw [hdraws0, hmod_res]
        exact hm3_tail
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
      w19, w20, w21, w22, w23, w24,
      d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24,
      u850, u858, u860, u950, u958, u960, H, hpq, hpack, hm2_ok⟩ :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_ok_unpack A ctl img x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr sp R s0 s2 hm2
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP_trap hm2_ok
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_ok_trap hs2_pc hs2_run hs2_sp' hs2_al hs2_x20 hs2_x24 hs2_x25 hs2_x26 hs2_x27
        hs2_x28 hpq) ?_
    intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25,
        hs3_x26, hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have ⟨hfl3, hsym3⟩ := callInv_steps hfl2 hsym2 hsteps23 hL2
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have hm3_ok := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_ok_pack A ctl img x { g with cur := some G' } G.pq sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr
      w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
      sp H R Pm3 s0 s3 hpack hPm3 hm3
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next_trap ⟨otr, (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2,
      G.pq.cap, G.pq.ptr, hcur, hsc, execOk_fromSessionState_of_ok hres, ?_⟩
    refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
      by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
      hs3_tr.trans hs2_tr',
      ⟨hs3_x0, hs3_x8, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25, hs3_x26, hs3_x27, hs3_x28⟩,
      hpt, hrest, hloc, hnow, hstk, hm3_ok⟩
    rw [hs3_pc, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrPC, hentry]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_okV {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r g sess R0 s0 s hcurState
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hcurState with ⟨hcur, hsc, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx20, hx21, hx25, hx26, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName
  have hs_pc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 524#64 := by
    simpa only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.curPC, hentry] using hs_pc
  obtain ⟨G, u280, _, hpure, hm_unp⟩ := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.curState_mem_unpack A ctl img x r g sess sp R s0 hsp0 hcur hm
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP hm_unp
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_pre hs_pc' hrun hsp hal hx20 hx21 hx25 hx26 hx28) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x21, hs1_x24, hs1_x25, hs1_x26,
      hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have ⟨hfl1, hsym1⟩ := callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hs1_pc' : s1.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr otrFromName := by
    rw [hs1_pc, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_addr_eq]
  have hm1_pre := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_pre_frame A ctl img x g G sess sp R Pm1 s0 s1
    hfl1 hsym1 hs1_sp hs1_x0 hs1_x8 hPm1 hm1
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.call env.callees.otrFrom ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
    hs1_pc' hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (otrFromSpec A img).onExit ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_panic_bridge kit st0 ikit ist0 C ctl S encRecord x r sess
      ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ _ _ R0 s0 s1 sf rfl hcur (hs1_tr.trans htr) hpost)
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x20 : s2.readReg64 .x20 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x26 : s2.readReg64 .x26 = sp + 0x9d0#64 := by reg_chain
  have hs2_x27 : s2.readReg64 .x27 = sp + 0xc0#64 := by reg_chain
  have hs2_x28 : s2.readReg64 .x28 = sp + 0x4a0#64 := by reg_chain
  obtain ⟨G', _, hs2_tr, hm2⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_post_unpack A ctl img x g G sess ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
      sp R s0 s1 s2 rfl hsp0 hs1_sp hpure hpost2
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  rcases hres : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 with p | otr
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w0, w1, w2, w3, w4, w5, H, hst, hm2_err⟩ :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_err_unpack A ctl img x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 p sp R s0 s2 hres hm2
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP hm2_err (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_err hs2_pc hs2_run hs2_sp' hs2_al) ?_
    intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x21, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have ⟨hfl3, hsym3⟩ := callInv_steps hfl2 hsym2 hsteps23 hL2
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have ⟨hmod_res, hdraws0⟩ := model_of_fromSessionState_error (C := C) (S := S)
      (x := x) hcur hres
    have hm3_tail := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_err_tail_mem A ctl img x { g with cur := some G' } sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 w0 w1 w2 w3 w4 w5 sp H R Pm3
      s0 s3 hPm3 hm3
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_false (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.tailFromSessionStateErr_ok env x R0 s0 s3
      (okAnswers r .newOrUnchanged)
      (.protocol p) w0 w1 w2 w3 w4 w5 H { g with cur := some G' }
      (takenRecord sess (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2)
      ?_ hst ?_)
    · refine ⟨⟨by rw [hmod_res], by rw [hmod_res]; exact ⟨hsc.2, trivial⟩, by rw [hmod_res]; trivial⟩, ?_⟩
      rw [hs3_tr, hs2_tr', hmod_res]
      dsimp only [okAnswers]
      rw [ikit.traceOfWith_load]
    · refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
        by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
        ⟨by reg_chain, by reg_chain, by reg_chain, by reg_chain⟩, hstk, ?_⟩
      · rw [hs3_pc, hentry]
      · rw [hdraws0, hmod_res]
        exact hm3_tail
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
      w19, w20, w21, w22, w23, w24,
      d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24,
      u850, u858, u860, u950, u958, u960, H, hpq, hpack, hm2_ok⟩ :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_ok_unpack A ctl img x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr sp R s0 s2 hm2
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP hm2_ok
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_ok hs2_pc hs2_run hs2_sp' hs2_al hs2_x20 hs2_x24 hs2_x25 hs2_x26 hs2_x27
        hs2_x28 hpq) ?_
    intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25,
        hs3_x26, hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have ⟨hfl3, hsym3⟩ := callInv_steps hfl2 hsym2 hsteps23 hL2
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have hm3_ok := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_ok_pack A ctl img x { g with cur := some G' } G.pq sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr
      w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
      sp H R Pm3 s0 s3 hpack hPm3 hm3
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next ⟨otr, (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2,
      G.pq.cap, G.pq.ptr, hcur, hsc, execOk_fromSessionState_of_ok hres, ?_⟩
    refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
      by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
      hs3_tr.trans hs2_tr',
      ⟨hs3_x0, hs3_x8, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25, hs3_x26, hs3_x27, hs3_x28⟩,
      hpt, hrest, hloc, hnow, hstk, hm3_ok⟩
    rw [hs3_pc, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrPC, hentry]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_ok_trap {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpec_trap Scope Q C ctl uuidTryParse S encRecord abs (img := img) (A := A) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_ok {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpec Scope Q C ctl uuidTryParse S encRecord abs (img := img) (A := A) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_okV

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
