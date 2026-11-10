/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvTrapV1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
public import LibsignalBinary.Proofs.E2E.HooksE.Common
public import LibsignalBinary.Specifications.SignalSession.CliRun
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrap
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.FindChain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.OnPanicTightModel
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Root
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root

/-!
# Trap-at-RNG and CLI `try_decrypt_with_state` under `DistinctSid` and Tight `onPanic`

Proves `tryDecryptTPTight_run_of_seamW_trap`, `tryDecryptV1_ok_PTight_trap`, and CLI corollaries
(`tryDecryptV1_ok_PTight_cli_of_hooks`, `tryDecryptV1_ok_PTight_cli`) against
`tryDecryptSpecTPTight`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalSpqrV1.M4

private theorem tdp_reaches_outcome_specTPTight_trap {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      x (TokenInit img ∗ R) s0 s) :
    reaches_outcome prog
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)
      x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hexit, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight] at hpost ⊢
    have heq : (TokenInit img ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf) ∗ R =
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf ∗
          (TokenInit img ∗ R) := by ac_rfl
    exact heq ▸ hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight,
      tryDecryptOnPanicTight] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hq2 := hq.2
    rw [← sepConj_assoc] at hq2
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq2
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem tdp_reaches_outcome_weaken_tight_trap {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      x R s0 s) :
    reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img)
      x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight_weaken hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem tdp_reaches_outcome_of_panic_tight_trap {P : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 s' ∗ R) :
    reaches_outcome P
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      x R s0 s :=
  Decrypt.reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic
      (spec := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      hpan hq)

private theorem tdp_onPanicTight_of_cmk_panic_trap {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {e : SignalProtocolError} {R : SepProp} {s0 s' : State}
    (hm1 : (x.model C S uuidTryParse).1 = .error e)
    (hp : (e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace)
    (hmem : s'.mem ⊨ anyHeap ∗ R) :
    s'.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 s' ∗ R := by
  have hcond : ((x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 s') ∧
      s0.trace <+: s'.trace := by
    refine ⟨?_, hp.2⟩
    rcases hp.1 with rfl | halloc
    · exact Or.inl hm1
    · exact Or.inr halloc
  simp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hcond, hmem⟩

private theorem tdp_reaches_outcome_tight_of_afterCmk_trap {P : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost}
    {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {ck : ChainKey} {r1 r2 : RatchetState} {mkg : MessageKeyGenerator} {R : SepProp}
    {s0 s : State}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (h : reaches_outcome P
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s) :
    reaches_outcome P
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecrypt_onPanicTight_of_afterCmk
        htr herc hcmk hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem tdp_reaches_outcome_of_consumeMsgKey_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hS2 : Stage2Contracts_trap img.base C A uuidTryParse S (trTrapExterns C abs))
    (hRecv : SpqrRecvOkWT_trap img C A S abs)
    (hGK : GenerateKeysOkW_trap img C A abs)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCalleesExt
      img C A uuidTryParse (trTrapExterns C abs))
    (hSeam : CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT_trap img C A ctl uuidTryParse S abs)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hstk : rootStack ≤ s0.sp.toNat)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img
      x trG { tr0 with ratchet := r1 } st1 ck draws (TokenInit img ∗ R) s0 s4)
    (hL4 : (trTrapProgAt img.base C abs).CodeLoaded s4.mem) :
    reaches_outcome (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)
      x R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := Model.fromSessionState_ok_inv htr
  have hs4_step := consumeMsgKey_ok_trap img C A ctl S (trTrapExterns C abs)
    hloads hS2 hcallees.cmk x trG { tr0 with ratchet := r1 } st1 ck draws
    (TokenInit img ∗ R) s0 s4 hs4_state hL4
  dsimp only at hs4_step
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    rw [hcmk] at hs4_step
    cases cmkRes with
    | error e =>
      apply tdp_reaches_outcome_specTPTight_trap
      have hmodel := Model.model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne, trG', herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        exact Decrypt.reaches_outcome_steps hsteps4
          (errTail_ok_tight_alloc hloads hS2.toAllocContracts hcallees.dropChain
            x trG' { tr0 with ratchet := r2 } st1 e
            (TokenInit img ∗ R) s0 s4' hne hm1 hm2 herr_st)
      · exact tdp_reaches_outcome_of_panic_tight_trap hsteps4 hpan
          (tdp_onPanicTight_of_cmk_panic_trap hm1 hp hmem)
    | ok mkg =>
      rcases hs4_step with ⟨s5, hsteps5, ⟨trG5, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine Decrypt.reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
        have hs56_step := hSeam hloads hhooks hRecv hGK x trG5 { tr0 with ratchet := r2 } st1 mkg
          draws R s0 s5 hQ hstk hseed32 hpqr0 hs5_state hL5
        dsimp only at hs56_step
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          rw [hspqr] at hs56_step
          rcases hs56_step with ⟨s5', hsteps5', ⟨herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · have hmodel := Model.model_of_spqr_error htr herc hcmk hspqr hnp5
            let e : SignalProtocolError :=
              if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
            have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
            have hne : e ≠ .panic := by subst e; cases sd <;> nofun
            apply tdp_reaches_outcome_specTPTight_trap
            subst hdraws
            exact Decrypt.reaches_outcome_steps hsteps5'
              (errTail_ok_tight_alloc hloads hS2.toAllocContracts hcallees.dropChain
                x trG5 { tr0 with ratchet := r2 } st1 e
                (TokenInit img ∗ R) s0 s5' hne hm1 hm2 herr_st)
          · exact Decrypt.reaches_outcome_steps hsteps5'
              (reaches_outcome_refl_panic
                (spec := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)
                hpan
                (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecrypt_onPanicTight_of_afterCmk
                  htr herc hcmk hq))
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          rw [hspqr] at hs56_step
          rcases hs56_step with ⟨s7, hsteps7, ⟨hs7_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · apply tdp_reaches_outcome_specTPTight_trap
            apply tdp_reaches_outcome_tight_of_afterCmk_trap htr herc hcmk
            refine Decrypt.reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL5
            let mks := mkg.generateKeys C.F pqrKey
            have hs7_step := verifyMac_ok_trap img C A ctl S (trTrapExterns C abs)
              hloads hS2 hcallees.verifyMac x trG5 { tr0 with ratchet := r2 }
              st1 mks newPqrState draws (TokenInit img ∗ R) s0 s7 hs7_state hL7
            dsimp only at hs7_step
            cases hmac : x.msg.verifyMacWithAddresses C.F
                (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
            | false =>
              rw [hmac] at hs7_step
              simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
              have hmodel := Model.model_of_verifyMac_false htr herc hcmk hspqr hmac hnp5
              have hm1 : (x.model C S uuidTryParse).1 = .error (.invalidMessage x.msgType .macFailed) := by
                rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
              rcases hs7_step with ⟨s7', hsteps7', herr_st | ⟨hpan, hq⟩⟩
              · subst hdraws
                exact Decrypt.reaches_outcome_steps hsteps7'
                  (tdp_reaches_outcome_weaken_tight_trap
                    (errTail_ok_tight_alloc hloads hS2.toAllocContracts hcallees.dropChain
                      x trG5 { tr0 with ratchet := r2 } st1
                      (.invalidMessage x.msgType .macFailed) (TokenInit img ∗ R) s0 s7' hne hm1 hm2 herr_st))
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic
                  hsteps7' hpan hq
            | true =>
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, hs8_state | ⟨hpan, hq⟩⟩
              · refine Decrypt.reaches_outcome_steps hsteps8 ?_
                have hL8 := hsteps8.codeLoaded hL7
                have hs8_step := aesDecrypt_ok_trap img C A ctl S (trTrapExterns C abs)
                  hloads hS2 x trG5 { tr0 with ratchet := r2 }
                  st1 mks newPqrState draws (TokenInit img ∗ R) s0 s8 hs8_state hL8
                cases haes : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
                | none =>
                  rw [haes] at hs8_step
                  have hmodel := Model.model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 =
                      .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
                  have hne : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic :=
                    nofun
                  rcases hs8_step with ⟨s8', hsteps8', herr_st | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Decrypt.reaches_outcome_steps hsteps8'
                      (tdp_reaches_outcome_weaken_tight_trap
                        (errTail_ok_tight_alloc hloads hS2.toAllocContracts hcallees.dropChain
                          x trG5 { tr0 with ratchet := r2 } st1
                          (.invalidMessage x.msgType .badCiphertext) (TokenInit img ∗ R) s0 s8' hne hm1 hm2 herr_st))
                  · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic
                      hsteps8' hpan hq
                | some pt =>
                  rw [haes] at hs8_step
                  have hmodel := Model.model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 =
                      (({ { tr0 with ratchet := r2 } with pqrState := newPqrState }).applyToSessionState
                        st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
                  rcases hs8_step with ⟨s9, hsteps9, hs9_state | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Decrypt.reaches_outcome_steps hsteps9
                      (applyRatchet_ok_trap img C A ctl S (trTrapExterns C abs)
                        hloads hS2 hcallees.trApply hcallees.clearUpk x trG5
                        { tr0 with ratchet := r2 } st1 newPqrState pt (TokenInit img ∗ R) s0 s9 hm1 hm2 hs9_state)
                  · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic
                      hsteps9 hpan hq
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic
                  hsteps8 hpan hq
          · exact Decrypt.reaches_outcome_steps hsteps7
              (reaches_outcome_refl_panic
                (spec := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)
                hpan
                (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecrypt_onPanicTight_of_afterCmk
                  htr herc hcmk hq))
      · exact tdp_reaches_outcome_specTPTight_trap
          (tdp_reaches_outcome_tight_of_afterCmk_trap htr herc hcmk
            (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic hsteps5 hpan hq))

private theorem tdp_try_decrypt_ok_of_seamW_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hRecv : SpqrRecvOkWT_trap img C A S abs)
    (hGK : GenerateKeysOkW_trap img C A abs)
    (hSeam : CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT_trap img C A ctl uuidTryParse S abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img) := by
  have hS2 : Stage2Contracts_trap img.base C A uuidTryParse S (trTrapExterns C abs) :=
    Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A S abs hhooks
  have hcallees := tryDecryptCallees_trap C A S abs img hhooks hloads
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' := (tryDecryptSpecTPTight_pre_iff C A ctl S img x R s0).mp hpre
  rcases hpre' with ⟨hQ, hpre⟩
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨hseeds, hchains, hstk⟩ :=
    CryptoVerification.Cli.E2E.Pqxdh.WireEntries.seedsLen32_of_pre_P hpre
  rcases s0_ok_P_trap hloads hhooks hcallees x (TokenInit img ∗ R) s0
      hpc hrun hsp hpre hL with
    ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hfalse⟩⟩
  swap; · exact hfalse.elim
  refine Decrypt.reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := loadRatchet_okT_ext (C := C) (S := S) (ext := trTrapExterns C abs)
    hloads hcallees.trFrom x (TokenInit img ∗ R) s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error e =>
      exact tdp_reaches_outcome_specTPTight_trap hs1_step
    | ok tr0 =>
      rcases hs1_step with ⟨s2, hsteps2, trG2, hs2_state⟩
      refine Decrypt.reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      have hs2_step := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_ext
        (ext := trTrapExterns C abs)
        hloads hcallees.findReceiverChainKey x trG2 tr0 st1
        (TokenInit img ∗ R) s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        rw [hf] at hs2_step
        rcases hs2_step hL2 with ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hfalse⟩⟩
        swap; · exact hfalse.elim
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
          Model.ensureReceiverChain_of_find_error hf
        have hmodel := Model.model_of_ensureReceiverChain_error (S := S) htr herc
        have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne : e ≠ .panic := by
          have he := Model.findReceiverChainKey_error_eq hf
          subst he
          decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          Model.decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        apply tdp_reaches_outcome_specTPTight_trap
        exact Decrypt.reaches_outcome_steps hsteps2'
          (errTail_ok_tight_alloc hloads hS2.toAllocContracts hcallees.dropChain
            x trG2 tr0 st1 e (TokenInit img ∗ R) s0 s2' hne hm1 hm2 herr_st)
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Decrypt.reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            Model.ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (Model.decryptDraws_of_find_some x.rest htr hf).symm
          exact tdp_reaches_outcome_of_consumeMsgKey_trap hloads hhooks hS2 hRecv hGK hcallees
            hSeam hseeds hQ hstk htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Decrypt.reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(Model.fromSessionState_ok_inv htr).2.1]
            exact hchains
          have hs3_step := dhStep_okT_trap hloads hS2
            hcallees.createChain hcallees.derivePk hcallees.pkSer hcallees.chainKeyToPb
            hcallees.growOne hcallees.dropChain
            x trG2 tr0 st1 (TokenInit img ∗ R) s0 s3 htr hf htr_chains hstk hs3_state hL3
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            rw [hdh] at hs3_step
            cases dhRes with
            | error e =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [Model.ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := Model.model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : e ≠ .panic := Model.dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨trG3, r1', herr_st⟩ | ⟨hpan, hq⟩⟩
              · apply tdp_reaches_outcome_specTPTight_trap
                exact Decrypt.reaches_outcome_steps hsteps3'
                  (errTail_ok_tight_alloc hloads hS2.toAllocContracts hcallees.dropChain
                    x trG3 { tr0 with ratchet := r1' } st1 e
                    (TokenInit img ∗ R) s0 s3' hne hm1 hm2 herr_st)
              · exact tdp_reaches_outcome_specTPTight_trap
                  (tdp_reaches_outcome_of_panic_tight_trap hsteps3' hpan hq)
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [Model.ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine Decrypt.reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact tdp_reaches_outcome_of_consumeMsgKey_trap hloads hhooks hS2 hRecv hGK hcallees
                  hSeam hseeds hQ hstk htr herc rfl hs4_state hL4
              · exact tdp_reaches_outcome_specTPTight_trap
                  (tdp_reaches_outcome_of_panic_tight_trap hsteps4 hpan hq)

/-- Parametric-`S` tight-`onPanic`, weak-`pre` (`DistinctSid`) `try_decrypt_with_state` theorem
at `trTrapProgAt` / `fnAddr`. -/
theorem tryDecryptTPTight_run_of_seamW_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hRecv : SpqrRecvOkWT_trap img C A S abs)
    (hGK : GenerateKeysOkW_trap img C A abs)
    (hSeam : CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT_trap img C A ctl uuidTryParse S abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img) := by
  rw [← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.tryDecryptEntry_eq_fnAddr
    (ext := trTrapExterns C abs) himg]
  exact tdp_try_decrypt_ok_of_seamW_trap himg hHooks hRecv hGK hSeam

/-- SPQR V1 `try_decrypt_with_state::<signal_session_ratchet::Coins>` contract `tryDecryptSpecTPTight`
on `trTrapProgAt img.base C abs`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hQ : LibsignalSpqrV1.SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) :=
  tryDecryptTPTight_run_of_seamW_trap C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg
    (spqrRecvOkWT_of_v1_trap C A K abs img hH hQ himg)
    (generateKeys_okW_trap C A (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg)
    (CryptoVerification.Cli.LibsignalSpqrV1.M4.pqRecvDerive_okWT_trap img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)

/-- CLI corollary of `tryDecryptV1_ok_PTight_trap` over arbitrary `RustAlloc` / `MlKem` hooks on `cliExterns W`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_cli_of_hooks
    (W : CryptoVerification.SignalSession.CliHooks) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (img : Obj.Image)
    (hH : TripleRatchetHooks W.C A (LibsignalSpqrV1.spqrV1 W.C.F K)
      (CryptoVerification.SignalSession.cliExterns W))
    (hQ : LibsignalSpqrV1.SpqrHooks W.C A K
      (CryptoVerification.SignalSession.cliExterns W))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      ((tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight W.C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F K) img) :=
  CryptoVerification.SignalSession.Cli.Slots.subroutine_ok_cli_of_trTrap
    (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_trap
      W.C A ctl K (CryptoVerification.SignalSession.cliExterns W) img hH hQ himg)

/-- CLI corollary of `tryDecryptV1_ok_PTight_trap` discharged with `cliExterns_tripleRatchetHooks` and `cliExterns_spqrHooks`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_cli
    (W : CryptoVerification.SignalSession.CliHooks) (ctl : BitVec 64) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      ((tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight W.C
        CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) img) :=
  CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_cli_of_hooks
    W CryptoVerification.E2E.HooksE.A0 ctl W.Q.K img
    (CryptoVerification.SignalSession.Cli.Slots.cliExterns_tripleRatchetHooks W
      (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K))
    (CryptoVerification.SignalSession.Cli.Slots.cliExterns_spqrHooks W)
    himg

end CryptoVerification.Cli.LibsignalSpqrV1.M4
