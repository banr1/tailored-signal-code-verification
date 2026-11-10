/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Model
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Root

/-!
# Root Seam Composition for CLI `try_decrypt_with_state::<Coins>`

Composes segment contracts `S0Spec` .. `S9Spec` and `ErrTailSpec` into `TryDecryptOk` and
`TryDecryptRunStmt` (general, empty-PQ, and SPQR v1 specializations) for
`try_decrypt_with_state::<signal_session_handshake::Coins>` in `libsignalSessionImage`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalTripleRatchet.DecryptPq.Model

/-! ## `SeedsLen32` Preservation and Panic Lifts -/

/-- Extract `SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat`
from `(CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.seedsLen32_of_pre {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat := by
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at hpre
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.ss ∧ s0.readReg64 .x2 = x.remA ∧
        s0.readReg64 .x3 = x.locA ∧ s0.readReg64 .x4 = x.msgA ∧
        (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
        x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
        x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat⌝ ∗
      (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
       sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
       memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗
       A.pool ∗ R) :=
    Satisfies.of_eq hpre
  rw [satisfies_pure_sepConj] at hpre'
  exact hpre'.1.2.2.2.2.2.2.2

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic {P : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R) :
    reaches_outcome P (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s :=
  reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic
      (spec := CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) hpan hq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_of_cmk_panic {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {e : SignalProtocolError} {R : SepProp} {s0 s' : State}
    (hm1 : (x.model C S uuidTryParse).1 = .error e)
    (hp : (e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace)
    (hmem : s'.mem ⊨ anyHeap ∗ R) :
    s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R := by
  have hcond : ((x.model C S uuidTryParse).1 = .error .panic ∨
      S.recvPanics x.st.pqRatchetState x.msg.pqRatchet ∨ allocFailedIn s0 s') ∧
      s0.trace <+: s'.trace := by
    refine ⟨?_, hp.2⟩
    rcases hp.1 with rfl | halloc
    · exact Or.inl hm1
    · exact Or.inr (Or.inr halloc)
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hcond, hmem⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF {P : Program} {Q : List (BitVec 8) → Prop}
    {F : SepProp} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x (F ∗ R) s0 s) :
    reaches_outcome P (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF Q F C A ctl parse S img) x R s0 s := by
  refine h.mono_outcome (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨_, _, hqe⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hhalted, hcs, ?_⟩
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF]
    rw [sepConj_assoc, sepConj_left_comm]
    exact hpost
  · exact Or.inr (Or.inl ⟨hpan, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame hqp⟩)
  · exact (not_satisfies_false_sepConj hqe).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF {P : Program} {Q : List (BitVec 8) → Prop}
    {F : SepProp} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R) :
    reaches_outcome P (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF Q F C A ctl uuidTryParse S img) x R s0 s :=
  reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic
      (spec := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF Q F C A ctl uuidTryParse S img) hpan hq)

/-! ## Post-`ensureReceiverChain` Composition (`S4` .. `S9` and `ErrTail`) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_s4QF
    {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOkQF Q Pstk F C A ctl S abs img)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF Q Pstk F img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec img C A ctl uuidTryParse S abs)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : Q x.st.pqRatchetState)
    (hPstk : Pstk (s0.sp - 1504#64).toNat)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG { tr0 with ratchet := r1 } st1 ck draws (F ∗ R) s0 s4)
    (hL4 : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s4.mem) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF Q F C A ctl uuidTryParse S img) x R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := fromSessionState_ok_inv htr
  have hs4_step :=
    hs4 hloads hhooks hcallees.cmk x trG { tr0 with ratchet := r1 } st1 ck draws (F ∗ R) s0 s4
    hs4_state hL4
  dsimp only at hs4_step
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    rw [hcmk] at hs4_step
    cases cmkRes with
    | error e =>
      have hmodel := model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne, trG', herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        exact reaches_outcome_steps hsteps4
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF
            (herr hloads hhooks hcallees.dropChain x trG' { tr0 with ratchet := r2 } st1 e
              (F ∗ R) s0 s4' hne hm1 hm2 herr_st))
      · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps4 hpan
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_of_cmk_panic hm1 hp hmem))
    | ok mkg =>
      rcases hs4_step with ⟨s5, hsteps5, ⟨trG5, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        have hs5_step :=
          hs5 hloads hhooks hrecv x trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
          hQ hpqr0 hPstk hs5_state hL5
        dsimp only at hs5_step
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          rw [hspqr] at hs5_step
          let e : SignalProtocolError :=
            if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
          have hne : e ≠ .panic := by subst e; cases sd <;> nofun
          rcases hs5_step with ⟨s5', hsteps5', ⟨herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · have hmodel := model_of_spqr_error htr herc hcmk hspqr hnp5
            have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
            subst hdraws
            exact reaches_outcome_steps hsteps5'
              (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF
                (herr hloads hhooks hcallees.dropChain x trG5
                  { tr0 with ratchet := r2 } st1 e (F ∗ R) s0 s5'
                  hne hm1 hm2 herr_st))
          · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps5' hpan hq
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s6, hsteps6, ⟨hs6_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · refine reaches_outcome_steps hsteps6 (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF ?_)
            have hL6 := hsteps6.codeLoaded hL5
            have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
            obtain ⟨s7, hsteps7, ⟨_, _, hs7_state⟩ | ⟨_, hoom⟩⟩ :=
              hs6 hloads hcallees.genKeys x trG5 { tr0 with ratchet := r2 } st1 mkg
                newPqrState pqrKey draws (F ∗ R) s0 s6 hseed32 hs6_state hL6
            rotate_left; · exact False.elim hoom
            refine reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL6
            let mks := mkg.generateKeys C.F pqrKey
            have hs7_step := hs7 hloads hhooks hcallees.verifyMac x trG5 { tr0 with ratchet := r2 }
              st1 mks newPqrState draws (F ∗ R) s0 s7 hs7_state hL7
            dsimp only at hs7_step
            cases hmac : x.msg.verifyMacWithAddresses C.F
                (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
            | false =>
              rw [hmac] at hs7_step
              simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
              have hmodel := model_of_verifyMac_false htr herc hcmk hspqr hmac hnp5
              have hm1 : (x.model C S uuidTryParse).1 =
                  .error (.invalidMessage x.msgType .macFailed) := by
                rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
              rcases hs7_step with ⟨s7', hsteps7', herr_st | ⟨hpan, hq⟩⟩
              · subst hdraws
                exact reaches_outcome_steps hsteps7'
                  (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1
                    (.invalidMessage x.msgType .macFailed) (F ∗ R) s0 s7' hne hm1 hm2 herr_st)
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic hsteps7' hpan hq
            | true =>
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, hs8_state | ⟨hpan, hq⟩⟩
              · refine reaches_outcome_steps hsteps8 ?_
                have hL8 := hsteps8.codeLoaded hL7
                have hs8_step := hs8 hloads hhooks x trG5 { tr0 with ratchet := r2 }
                  st1 mks newPqrState draws (F ∗ R) s0 s8 hs8_state hL8
                cases haes : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
                | none =>
                  rw [haes] at hs8_step
                  have hmodel := model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 =
                      .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
                  have hne : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic :=
                    nofun
                  rcases hs8_step with ⟨s8', hsteps8', herr_st | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact reaches_outcome_steps hsteps8'
                      (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1
                        (.invalidMessage x.msgType .badCiphertext) (F ∗ R) s0 s8' hne hm1 hm2 herr_st)
                  · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic hsteps8' hpan hq
                | some pt =>
                  rw [haes] at hs8_step
                  have hmodel := model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 =
                      (({ { tr0 with ratchet := r2 }
                          with pqrState := newPqrState }).applyToSessionState
                        st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
                  rcases hs8_step with ⟨s9, hsteps9, hs9_state | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact reaches_outcome_steps hsteps9
                      (hs9 hloads hhooks hcallees.trApply hcallees.clearUpk x trG5
                        { tr0 with ratchet := r2 } st1 newPqrState pt (F ∗ R) s0 s9 hm1 hm2 hs9_state)
                  · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic hsteps9 hpan hq
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic hsteps8 hpan hq
          · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps6 hpan hq
      · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps5 hpan (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame hq)

/-- Compose `S4Spec` .. `S9Spec` and `ErrTailSpec` from `S4State` into `reaches_outcome` for `tryDecryptSpec`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_s4
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOkQ Q C A ctl S abs img)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5Spec Q img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec img C A ctl uuidTryParse S abs)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : Q x.st.pqRatchetState)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG { tr0 with ratchet := r1 } st1 ck draws R s0 s4)
    (hL4 : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s4.mem) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s4 := by
  have hs4' : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG { tr0 with ratchet := r1 } st1 ck draws
      (emp ∗ R) s0 s4 := by rwa [emp_sepConj]
  have hs5' : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF Q (fun _ => True) emp img C A ctl uuidTryParse S abs := by
    intro hloads' hhooks' _ x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' _ h5' hL'
    rw [emp_sepConj] at h5'
    have h := hs5 hloads' hhooks' hrecv x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' h5' hL'
    simpa only [emp_sepConj] using h
  refine (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_s4QF hloads hhooks (spqrRecvOkQF_of_okQ hrecv) hcallees
      hs4 hs5' hs6 hs7 hs8 hs9 herr hseeds hQ trivial htr herc hdraws hs4' hL4).mono_outcome
    (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨code, hex, hqe⟩ | ⟨_, hoom⟩
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF] at hpost
    rw [emp_sepConj] at hpost
    exact Or.inl ⟨hhalted, hcs, hpost⟩
  · exact Or.inr (Or.inl ⟨hpan, hqp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hqe⟩))
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Full Root Composition (`S0` .. `S9` and `ErrTail`) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok_of_seamsQF
    {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hPstk : ∀ sp0 : BitVec 64, rootStack ≤ sp0.toNat → Pstk (sp0 - 1504#64).toNat)
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOkQF Q Pstk F C A ctl S abs img)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec img C A ctl uuidTryParse S abs)
    (hs1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec img C A ctl uuidTryParse S abs)
    (hs2 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec img C A ctl abs)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec img C A ctl uuidTryParse S abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF Q Pstk F img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOkQF Q F img C A ctl uuidTryParse S abs := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm] at hpre
  obtain ⟨hseeds, hchains, hstk⟩ := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.seedsLen32_of_pre hpre
  have hPstk0 : Pstk (s0.sp - 1504#64).toNat := hPstk s0.sp hstk
  obtain ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hoom⟩⟩ :=
    hs0 hloads hcallees.localIk hcallees.remoteIk hcallees.sameAcc x (F ∗ R) s0 hpc hrun hsp hpre hL
  rotate_left; · exact False.elim hoom
  refine reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 hloads hcallees.trFrom x (F ∗ R) s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error e =>
      exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF hs1_step
    | ok tr0 =>
      rcases hs1_step with ⟨s2, hsteps2, trG2, hs2_state⟩
      refine reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      have hs2_step :=
        hs2 hloads hcallees.findReceiverChainKey x trG2 tr0 st1 (F ∗ R) s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        rw [hf] at hs2_step
        obtain ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
        rotate_left; · exact False.elim hoom
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
          ensureReceiverChain_of_find_error hf
        have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
        have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne : e ≠ .panic := by
          have he := findReceiverChainKey_error_eq hf
          subst he
          decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        exact reaches_outcome_steps hsteps2'
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF
            (herr hloads hhooks hcallees.dropChain x trG2 tr0 st1 e (F ∗ R) s0 s2'
              hne hm1 hm2 herr_st))
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          obtain ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
          rotate_left; · exact False.elim hoom
          refine reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (decryptDraws_of_find_some x.rest htr hf).symm
          exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_s4QF hloads hhooks hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr
            hseeds hQ hPstk0 htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          obtain ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
          rotate_left; · exact False.elim hoom
          refine reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(fromSessionState_ok_inv htr).2.1]
            exact hchains
          have hs3_step := hs3 hloads hhooks hcallees.createChain hcallees.derivePk
            hcallees.pkSer hcallees.chainKeyToPb hcallees.growOne hcallees.dropChain
            x trG2 tr0 st1 (F ∗ R) s0 s3 htr hf htr_chains hstk hs3_state hL3
          dsimp only at hs3_step
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            rw [hdh] at hs3_step
            cases dhRes with
            | error e =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : e ≠ .panic := dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨trG3, r1', herr_st⟩ | ⟨hpan, hq⟩⟩
              · exact reaches_outcome_steps hsteps3'
                  (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF
                    (herr hloads hhooks hcallees.dropChain x trG3 { tr0 with ratchet := r1' } st1 e
                      (F ∗ R) s0 s3' hne hm1 hm2 herr_st))
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps3' hpan (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame hq)
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_s4QF
                  hloads hhooks hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr
                  hseeds hQ hPstk0 htr herc rfl hs4_state hL4
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps4 hpan (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame hq)

/-- Compose `S0Spec` .. `S9Spec`, `ErrTailSpec`, `SpqrRecvOkQ Q`, and `TryDecryptCallees` into `TryDecryptOk Q`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok_of_seams
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOkQ Q C A ctl S abs img)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec img C A ctl uuidTryParse S abs)
    (hs1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec img C A ctl uuidTryParse S abs)
    (hs2 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec img C A ctl abs)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec img C A ctl uuidTryParse S abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5Spec Q img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk Q img C A ctl uuidTryParse S abs := by
  have hs5' : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF Q (fun _ => True) emp img C A ctl uuidTryParse S abs := by
    intro hloads' hhooks' _ x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' _ h5' hL'
    rw [emp_sepConj] at h5'
    have h := hs5 hloads' hhooks' hrecv x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' h5' hL'
    simpa only [emp_sepConj] using h
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptOk_of_okQF
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok_of_seamsQF (fun _ _ => trivial) hloads hhooks (spqrRecvOkQF_of_okQ hrecv)
      hcallees hs0 hs1 hs2 hs3 hs4 hs5' hs6 hs7 hs8 hs9 herr)

/-- Top-level run statement for `try_decrypt_with_state::<signal_session_handshake::Coins>` against `tryDecryptSpec`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → SpqrRecvOk C A ctl S abs img →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img)

/-- Top-level run statement restricted to an empty post-quantum ratchet state. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).restrictPre (·.st.pqRatchetState = []))

/-- Derive `TryDecryptRunStmt` from `S0Spec` .. `S9Spec`, `ErrTailSpec`, and `TryDecryptCallees`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecrypt_run_of_seams
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec img C A ctl uuidTryParse S abs)
    (hs1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec img C A ctl uuidTryParse S abs)
    (hs2 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec img C A ctl abs)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec img C A ctl uuidTryParse S abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5Spec (fun _ => True) img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqRunStmt C A ctl S abs img := by
  intro hhooks hrecv hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  have h := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok_of_seams (Q := fun _ => True) hloads hhooks
    (spqrRecvOkQ_of_recvOk hrecv) (hcallees hhooks hloads)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 herr
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk at h
  rwa [Spec.restrictPre_true] at h

/-- Derive `TryDecryptEmptyRunStmt` at `Q := (· = [])` from `SpqrRecvEmptyRunStmt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEmpty_run_of_seams
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvEmpty : SpqrRecvEmptyRunStmt C A ctl S abs img)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec img C A ctl uuidTryParse S abs)
    (hs1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec img C A ctl uuidTryParse S abs)
    (hs2 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec img C A ctl abs)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec img C A ctl uuidTryParse S abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5Spec (· = []) img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqEmptyRunStmt C A ctl S abs img := by
  intro hhooks hempty hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok_of_seams (Q := (· = [])) hloads hhooks
    (spqrRecvOkQ_empty hrecvEmpty hhooks hempty hloads) (hcallees hhooks hloads)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 herr

/-- Top-level run statement restricted to SPQR v1 states (`pqRatchetState.length < 2 ^ 32`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
    LibsignalSpqrV1.SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) img)

/-- Derive `TryDecryptPqV1RunStmt` at `Q := (·.length < 2 ^ 32)` from `SpqrRecvV1Stmt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptV1_run_of_seams
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvV1 : LibsignalSpqrV1.SpqrRecvV1Stmt C A ctl K abs img)
    (hcallees : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
      Obj.Loads libsignalSessionImage img →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs2 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec img C A ctl abs)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF (·.length < 2 ^ 32) (spqrRecvStack ≤ ·) (LibsignalSpqrV1.TokenInit img)
      img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmt C A ctl K abs img := by
  intro hhooks hspqr hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  have hrecv : SpqrRecvOkQF (·.length < 2 ^ 32) (spqrRecvStack ≤ ·) (LibsignalSpqrV1.TokenInit img)
      C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img :=
    LibsignalSpqrV1.spqrRecvSpecXT_imp_spqrRecvSpec _ _ A C.F K img (hrecvV1 hhooks hspqr hloads)
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok_of_seamsQF (fun _ h => spqrRecvStack_le_sub_of_rootStack h)
    hloads hhooks hrecv (hcallees hhooks hloads)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 herr

alias _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.try_decrypt_ok_of_seams
alias _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecrypt_ok := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecrypt_run_of_seams

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
