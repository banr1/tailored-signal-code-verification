/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Root
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.Callees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackS7
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackS8
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackS9
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegDhMain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ErrTailProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S0B
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S1Proof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S2B
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS6
import LibsignalBinary.Proofs.ConsumeMessageKey.Seams
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Model
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Root
import LibsignalBinary.Proofs.TripleRatchet.InImage.Spqr

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.DecryptPqTrapBridge

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.Model

set_option maxHeartbeats 1200000 in
theorem reaches_outcome_of_s4QF_trap
    {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap Q Pstk F C A S abs img)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_trap img C A uuidTryParse abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec_trap img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF_trap Q Pstk F img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec_trap img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec_trap img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec_trap img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec_trap img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec_trap img C A ctl uuidTryParse S abs)
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
    (hL4 : (trTrapProgAt img.base C abs).CodeLoaded s4.mem) :
    reaches_outcome (trTrapProgAt img.base C abs)
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
        exact LibsignalSession.reaches_outcome_steps hsteps4
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF
            (herr hloads hhooks hcallees.dropChain x trG' { tr0 with ratchet := r2 } st1 e
              (F ∗ R) s0 s4' hne hm1 hm2 herr_st))
      · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps4 hpan
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame
            (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_of_cmk_panic hm1 hp hmem))
    | ok mkg =>
      rcases hs4_step with ⟨s5, hsteps5, ⟨trG5, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine LibsignalSession.reaches_outcome_steps hsteps5 ?_
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
            exact LibsignalSession.reaches_outcome_steps hsteps5'
              (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF
                (herr hloads hhooks hcallees.dropChain x trG5
                  { tr0 with ratchet := r2 } st1 e (F ∗ R) s0 s5'
                  hne hm1 hm2 herr_st))
          · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps5' hpan hq
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s6, hsteps6, ⟨hs6_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · refine LibsignalSession.reaches_outcome_steps hsteps6 (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF ?_)
            have hL6 := hsteps6.codeLoaded hL5
            have hseed32 : mkg.seed.length = 32 := CryptoVerification.LibsignalTripleRatchet.DecryptPq.decrypt_mkg_seed hseeds htr herc hcmk
            obtain ⟨s7, hsteps7, ⟨_, _, hs7_state⟩ | ⟨_, hoom⟩⟩ :=
              hs6 hloads hcallees.genKeys x trG5 { tr0 with ratchet := r2 } st1 mkg
                newPqrState pqrKey draws (F ∗ R) s0 s6 hseed32 hs6_state hL6
            rotate_left; · exact False.elim hoom
            refine LibsignalSession.reaches_outcome_steps hsteps7 ?_
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
                exact LibsignalSession.reaches_outcome_steps hsteps7'
                  (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1
                    (.invalidMessage x.msgType .macFailed) (F ∗ R) s0 s7' hne hm1 hm2 herr_st)
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic hsteps7' hpan hq
            | true =>
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, hs8_state | ⟨hpan, hq⟩⟩
              · refine LibsignalSession.reaches_outcome_steps hsteps8 ?_
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
                    exact LibsignalSession.reaches_outcome_steps hsteps8'
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
                    exact LibsignalSession.reaches_outcome_steps hsteps9
                      (hs9 hloads hhooks hcallees.trApply hcallees.clearUpk x trG5
                        { tr0 with ratchet := r2 } st1 newPqrState pt (F ∗ R) s0 s9 hm1 hm2 hs9_state)
                  · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic hsteps9 hpan hq
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic hsteps8 hpan hq
          · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps6 hpan hq
      · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps5 hpan
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame hq)

theorem spqrRecvOkQF_of_okQ_pq_trap {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQ_trap Q C A S abs img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap Q (fun _ => True) emp C A S abs img := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun x R s0 sf hp => ?_) (fun _ _ _ _ _ he => he)
  · dsimp only [DecryptPq.spqrRecvSpecQF, Spec.restrictPre] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hQ, _⟩, hpre⟩
    rw [emp_sepConj] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hQ, hpre⟩
  · dsimp only [DecryptPq.spqrRecvSpecQF, Spec.restrictPre] at hpost ⊢
    rwa [emp_sepConj]
  · dsimp only [DecryptPq.spqrRecvSpecQF, Spec.restrictPre] at hp ⊢
    exact hp

theorem spqrRecvOkQ_empty_pq_trap {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {abs : String → Option (State → State)} {img : Obj.Image}
    (hhooks : TripleRatchetHooks C A S abs)
    (hempty : S.RecvEmptyOk) (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQ_trap (· = []) C A S abs img :=
  spqrRecvEmpty_run_trap C A S abs img hhooks hempty hloads

theorem reaches_outcome_of_s4_trap
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQ_trap Q C A S abs img)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_trap img C A uuidTryParse abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec_trap img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5Spec_trap Q img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec_trap img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec_trap img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec_trap img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec_trap img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec_trap img C A ctl uuidTryParse S abs)
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
    (hL4 : (trTrapProgAt img.base C abs).CodeLoaded s4.mem) :
    reaches_outcome (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s4 := by
  have hs4' : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG { tr0 with ratchet := r1 } st1 ck draws
      (emp ∗ R) s0 s4 := by rwa [emp_sepConj]
  have hs5' : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF_trap Q (fun _ => True) emp img C A ctl uuidTryParse S abs := by
    intro hloads' hhooks' _ x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' _ h5' hL'
    rw [emp_sepConj] at h5'
    have h := hs5 hloads' hhooks' hrecv x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' h5' hL'
    simpa only [emp_sepConj] using h
  refine (reaches_outcome_of_s4QF_trap hloads hhooks (spqrRecvOkQF_of_okQ_pq_trap hrecv) hcallees
      hs4 hs5' hs6 hs7 hs8 hs9 herr hseeds hQ trivial htr herc hdraws hs4' hL4).mono_outcome
    (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨code, hex, hqe⟩ | ⟨_, hoom⟩
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF] at hpost
    rw [emp_sepConj] at hpost
    exact Or.inl ⟨hhalted, hcs, hpost⟩
  · exact Or.inr (Or.inl ⟨hpan, hqp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hqe⟩))
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
theorem try_decrypt_ok_of_seamsQF_trap
    {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hPstk : ∀ sp0 : BitVec 64, rootStack ≤ sp0.toNat → Pstk (sp0 - 1504#64).toNat)
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap Q Pstk F C A S abs img)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_trap img C A uuidTryParse abs)
    (hs0 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec_trap img C A ctl uuidTryParse S abs)
    (hs1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec_trap img C A ctl uuidTryParse S abs)
    (hs2 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec_trap img C A ctl abs)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec_trap img C A ctl uuidTryParse S abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec_trap img C A ctl uuidTryParse S abs)
    (hs5 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF_trap Q Pstk F img C A ctl uuidTryParse S abs)
    (hs6 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec_trap img C A ctl abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec_trap img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec_trap img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec_trap img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec_trap img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOkQF_trap Q F img C A ctl uuidTryParse S abs := by
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
  refine LibsignalSession.reaches_outcome_steps hsteps1 ?_
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
      refine LibsignalSession.reaches_outcome_steps hsteps2 ?_
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
        exact LibsignalSession.reaches_outcome_steps hsteps2'
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF
            (herr hloads hhooks hcallees.dropChain x trG2 tr0 st1 e (F ∗ R) s0 s2'
              hne hm1 hm2 herr_st))
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          obtain ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
          rotate_left; · exact False.elim hoom
          refine LibsignalSession.reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (decryptDraws_of_find_some x.rest htr hf).symm
          exact reaches_outcome_of_s4QF_trap hloads hhooks hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr
            hseeds hQ hPstk0 htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          obtain ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
          rotate_left; · exact False.elim hoom
          refine LibsignalSession.reaches_outcome_steps hsteps3 ?_
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
              · exact LibsignalSession.reaches_outcome_steps hsteps3'
                  (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_tryDecryptSpecQF
                    (herr hloads hhooks hcallees.dropChain x trG3 { tr0 with ratchet := r1' } st1 e
                      (F ∗ R) s0 s3' hne hm1 hm2 herr_st))
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps3' hpan
                  (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame hq)
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine LibsignalSession.reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact reaches_outcome_of_s4QF_trap
                  hloads hhooks hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr
                  hseeds hQ hPstk0 htr herc rfl hs4_state hL4
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panicQF hsteps4 hpan
                  (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.onPanic_drop_frame hq)

theorem tryDecryptPqEmpty_ok_trap {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image}
    (hH : TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk)
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk_trap (· = []) img C A ctl uuidTryParse S abs := by
  have hrecv := spqrRecvOkQ_empty_pq_trap hH hempty himg
  have hs5' : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF_trap (· = []) (fun _ => True) emp img C A ctl uuidTryParse S abs := by
    intro hloads' hhooks' _ x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' _ h5' hL'
    rw [emp_sepConj] at h5'
    have h := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s5_ok_trap (Q := (· = [])) img C A ctl S abs
      hloads' hhooks' hrecv x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' h5' hL'
    simpa only [emp_sepConj] using h
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptOk_of_okQF_trap
    (try_decrypt_ok_of_seamsQF_trap (fun _ _ => trivial) himg hH (spqrRecvOkQF_of_okQ_pq_trap hrecv)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqCallees_trap C A S abs img hH himg)
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_ok_trap
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_trap
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_trap
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_ok_trap img C A ctl S abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s4_ok_trap img C A ctl S abs)
      hs5'
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s6_ok_trap img C A ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok_trap img C A ctl S abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_ok_trap img C A ctl S abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s9_ok_trap img C A ctl S abs)
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_ok_trap)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.DecryptPqTrapBridge
