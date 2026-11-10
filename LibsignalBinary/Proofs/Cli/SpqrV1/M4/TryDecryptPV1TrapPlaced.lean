/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Root
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model

/-!
# Relocatable `try_decrypt_with_state` Tight-Panic Assembly on CLI Block `433`

Assembles all 11 Block-`433` segment seams into `tryDecrypt_placed_ok_of_seams` and
`tryDecryptV1_placed_ok_PTight_cli` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.SpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet hiding memRegion_eight
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  decrypt_mkg_seed tryDecryptOnPanicTight_weaken
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.CliRatchet.DecPlaced
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

private theorem tdp_reaches_outcome_weaken_tight_placed [LibsignalPlacement]
    {P : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (cliTryDecryptTightSpecPlaced C A ctl uuidTryParse S) x R s0 s) :
    reaches_outcome P (cliTryDecryptSpecPlaced C A ctl uuidTryParse S) x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [cliTryDecryptTightSpecPlaced, tryDecryptPlacedTightSpec,
      cliTryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptOnPanicTight,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1.elim Or.inl (Or.inr ∘ Or.inr), hq.1.2⟩, hq.2⟩
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem tdp_reaches_outcome_of_panic_placed [LibsignalPlacement]
    {P : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R) :
    reaches_outcome P (cliTryDecryptSpecPlaced C A ctl uuidTryParse S) x R s0 s :=
  Arm64.reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic
      (spec := cliTryDecryptSpecPlaced C A ctl uuidTryParse S) hpan hq)

private theorem tdp_pre_iff_placed [LibsignalPlacement]
    {Q : List (BitVec 8) → Prop} {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight
          Q F0 C A ctl uuidTryParse S)).pre x s0 ∗ R) :
    Q x.st.pqRatchetState ∧
      (s0.mem ⊨ (cliTryDecryptSpecPPlaced C A ctl uuidTryParse S).pre x s0 ∗ (F0 ∗ R)) := by
  dsimp only [withLsCodeRoLoaded,
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight,
    cliTryDecryptSpecPPlaced] at hpre ⊢
  have h1 : s0.mem ⊨ ⌜Q x.st.pqRatchetState⌝ ∗
      (((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP
          C A ctl uuidTryParse S).pre x s0 ∗
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ (F0 ∗ R)) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rwa [satisfies_pure_sepConj] at h1

private theorem tdp_reaches_outcome_of_verifyMac_placed [LibsignalPlacement]
    {P : Program} {entry : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    (herr : ErrTailTightSeamPlaced P entry C A ctl uuidTryParse S)
    (hs7 : S7SeamPlaced P entry C A ctl uuidTryParse S)
    (hs8 : S8SeamPlaced P entry C A ctl uuidTryParse S)
    (hs9 : S9SeamPlaced P entry C A ctl uuidTryParse S)
    {x : TryDecryptGhost} {trG5 : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState : List (BitVec 8)} {pqrKey : Salt}
    {draws : Nat} {R : SepProp} {s0 s7 : State}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr0.pqrState x.msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hnp5 : S.recvPanics tr0.pqrState x.msg.pqRatchet = false)
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs7_state : VerifyMacStatePlaced entry A ctl x trG5 { tr0 with ratchet := r2 } st1
      (mkg.generateKeys C.F pqrKey) newPqrState draws R s0 s7)
    (hL7 : P.CodeLoaded s7.mem) :
    reaches_outcome P (cliTryDecryptSpecPlaced C A ctl uuidTryParse S) x R s0 s7 := by
  let mks := mkg.generateKeys C.F pqrKey
  have hs7_step := hs7 x trG5 { tr0 with ratchet := r2 } st1 mks newPqrState draws R s0 s7
    hs7_state hL7
  dsimp only at hs7_step
  cases hmac : x.msg.verifyMacWithAddresses C.F
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
  | false =>
    rw [hmac] at hs7_step
    simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
    have hmodel := Decrypt.Model.model_of_verifyMac_false htr herc hcmk hspqr hmac hnp5
    have hm1 : (x.model C S uuidTryParse).1 = .error (.invalidMessage x.msgType .macFailed) := by
      rw [hmodel]
    have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
    have hne : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
    rcases hs7_step with ⟨s7', hsteps7', herr_st | ⟨hpan, hq⟩⟩
    · subst hdraws
      exact Arm64.reaches_outcome_steps hsteps7'
        (tdp_reaches_outcome_weaken_tight_placed
          (herr x trG5 { tr0 with ratchet := r2 } st1
            (.invalidMessage x.msgType .macFailed) R s0 s7' hne hm1 hm2 herr_st))
    · exact tdp_reaches_outcome_of_panic_placed hsteps7' hpan hq
  | true =>
    rw [hmac] at hs7_step
    simp only [↓reduceIte] at hs7_step
    rcases hs7_step with ⟨s8, hsteps8, hs8_state | ⟨hpan, hq⟩⟩
    · refine Arm64.reaches_outcome_steps hsteps8 ?_
      have hL8 := hsteps8.codeLoaded hL7
      have hs8_step := hs8 x trG5 { tr0 with ratchet := r2 } st1 mks newPqrState draws R s0 s8
        hs8_state hL8
      cases haes : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | none =>
        rw [haes] at hs8_step
        have hmodel := Decrypt.Model.model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
        have hm1 : (x.model C S uuidTryParse).1 =
            .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic := nofun
        rcases hs8_step with ⟨s8', hsteps8', herr_st | ⟨hpan, hq⟩⟩
        · subst hdraws
          exact Arm64.reaches_outcome_steps hsteps8'
            (tdp_reaches_outcome_weaken_tight_placed
              (herr x trG5 { tr0 with ratchet := r2 } st1
                (.invalidMessage x.msgType .badCiphertext) R s0 s8' hne hm1 hm2 herr_st))
        · exact tdp_reaches_outcome_of_panic_placed hsteps8' hpan hq
      | some pt =>
        rw [haes] at hs8_step
        have hmodel := Decrypt.Model.model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
        have hm1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 =
            (({ { tr0 with ratchet := r2 } with pqrState := newPqrState }).applyToSessionState
              st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
        rcases hs8_step with ⟨s9, hsteps9, hs9_state | ⟨hpan, hq⟩⟩
        · subst hdraws
          exact Arm64.reaches_outcome_steps hsteps9
            (hs9 x trG5 { tr0 with ratchet := r2 } st1 newPqrState pt R s0 s9 hm1 hm2 hs9_state)
        · exact tdp_reaches_outcome_of_panic_placed hsteps9 hpan hq
    · exact tdp_reaches_outcome_of_panic_placed hsteps8 hpan hq

private theorem tdp_reaches_outcome_of_consumeMsgKey_placed [LibsignalPlacement]
    {P : Program} {entry : BitVec 64} {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    (herr : ErrTailTightSeamPlaced P entry C A ctl uuidTryParse S)
    (hs4 : S4SeamPlaced P entry C A ctl uuidTryParse S)
    (hs5 : S5WTSeamPlaced P entry F0 C A ctl uuidTryParse S)
    (hs6 : S6SeamPlaced P entry C A ctl)
    (hs7 : S7SeamPlaced P entry C A ctl uuidTryParse S)
    (hs8 : S8SeamPlaced P entry C A ctl uuidTryParse S)
    (hs9 : S9SeamPlaced P entry C A ctl uuidTryParse S)
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
    (hs4_state : ConsumeMsgKeyStatePlaced entry A ctl x trG { tr0 with ratchet := r1 } st1 ck draws
      (F0 ∗ R) s0 s4)
    (hL4 : P.CodeLoaded s4.mem) :
    reaches_outcome P
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight
        (·.length < 2 ^ 32) F0 C A ctl uuidTryParse S)
      x R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := Decrypt.Model.fromSessionState_ok_inv htr
  have hs4_step := hs4 x trG { tr0 with ratchet := r1 } st1 ck draws (F0 ∗ R) s0 s4 hs4_state hL4
  dsimp only at hs4_step
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    rw [hcmk] at hs4_step
    cases cmkRes with
    | error e =>
      have hmodel := Decrypt.Model.model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne, trG', herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        exact Arm64.reaches_outcome_steps hsteps4
          (reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed
            (herr x trG' { tr0 with ratchet := r2 } st1 e (F0 ∗ R) s0 s4' hne hm1 hm2 herr_st))
      · exact reaches_outcome_of_panicQF_PTight_placed hsteps4 hpan
          (onPanicTight_drop_frame (onPanicTight_of_cmk_panic hm1 hp hmem))
    | ok mkg =>
      rcases hs4_step with ⟨s5, hsteps5, ⟨trG5, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine Arm64.reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
        have hs5_step := hs5 x trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
          hQ hstk hpqr0 hs5_state hL5
        dsimp only at hs5_step
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s5', hsteps5', ⟨herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · have hmodel := Decrypt.Model.model_of_spqr_error htr herc hcmk hspqr hnp5
            let e : SignalProtocolError :=
              if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
            have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
            have hne : e ≠ .panic := by subst e; cases sd <;> nofun
            subst hdraws
            exact Arm64.reaches_outcome_steps hsteps5'
              (reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed
                (herr x trG5 { tr0 with ratchet := r2 } st1 e (F0 ∗ R) s0 s5' hne hm1 hm2 herr_st))
          · exact reaches_outcome_of_panicQF_PTight_placed hsteps5' hpan
              (tryDecrypt_onPanicTight_of_afterCmk_placed (A := A) (ctl := ctl) htr herc hcmk hq)
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s6, hsteps6, ⟨hs6_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · refine Arm64.reaches_outcome_steps hsteps6 ?_
            have hL6 := hsteps6.codeLoaded hL5
            rcases hs6 x trG5 { tr0 with ratchet := r2 } st1 mkg newPqrState pqrKey draws
                (F0 ∗ R) s0 s6 hseed32 hs6_state hL6 with
              ⟨s7, hsteps7, ⟨_, _, hs7_state⟩ | ⟨_, hfalse⟩⟩
            swap; · exact hfalse.elim
            refine Arm64.reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL6
            exact reaches_outcome_tryDecryptSpecQF_PTight_of_afterCmk_placed htr herc hcmk
              (tdp_reaches_outcome_of_verifyMac_placed herr hs7 hs8 hs9
                htr herc hcmk hspqr hnp5 hdraws hs7_state hL7)
          · exact reaches_outcome_of_panicQF_PTight_placed hsteps6 hpan
              (tryDecrypt_onPanicTight_of_afterCmk_placed (A := A) (ctl := ctl) htr herc hcmk hq)
      · exact reaches_outcome_of_panicQF_PTight_placed hsteps5 hpan
          (onPanicTight_drop_frame
            (tryDecrypt_onPanicTight_of_afterCmk_placed (A := A) (ctl := ctl) htr herc hcmk hq))

/-- Assemble all 11 Block-`433` seams into `subroutine_ok P entry` for
`withLsCodeRoLoaded lsmpl (tryDecryptPlacedSpecQF_PTight (·.length < 2 ^ 32) F0 ...)`. -/
theorem tryDecrypt_placed_ok_of_seams [LibsignalPlacement]
    {P : Program} {entry : BitVec 64} {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    (herr : ErrTailTightSeamPlaced P entry C A ctl uuidTryParse S)
    (hs0 : S0PSeamPlaced P entry C A ctl uuidTryParse S)
    (hs1 : S1TightSeamPlaced P entry C A ctl uuidTryParse S)
    (hs2 : S2SeamPlaced P entry A ctl)
    (hs3 : S3TightSeamPlaced P entry C A ctl uuidTryParse S)
    (hs4 : S4SeamPlaced P entry C A ctl uuidTryParse S)
    (hs5 : S5WTSeamPlaced P entry F0 C A ctl uuidTryParse S)
    (hs6 : S6SeamPlaced P entry C A ctl)
    (hs7 : S7SeamPlaced P entry C A ctl uuidTryParse S)
    (hs8 : S8SeamPlaced P entry C A ctl uuidTryParse S)
    (hs9 : S9SeamPlaced P entry C A ctl uuidTryParse S) :
    subroutine_ok P entry
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight
          (·.length < 2 ^ 32) F0 C A ctl uuidTryParse S)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  rcases tdp_pre_iff_placed hpre with ⟨hQ, hpreP⟩
  have hpre_raw : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP
        C A ctl uuidTryParse S).pre x s0 ∗
        (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ (F0 ∗ R)) := by
    dsimp only [cliTryDecryptSpecPPlaced, withLsCodeRoLoaded] at hpreP
    rwa [sepConj_assoc] at hpreP
  obtain ⟨hseeds, hchains, hstk⟩ := seedsLen32_of_pre_P_placed hpre_raw
  have hrest := restLen_of_pre_P_placed hpre_raw
  change reaches_outcome P
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight
      (·.length < 2 ^ 32) F0 C A ctl uuidTryParse S) x R s0 s0
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  rcases hs0 x (F0 ∗ R) s0 hpc hrun hsp hpreP hL with
    ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hfalse⟩⟩
  swap; · exact hfalse.elim
  refine Arm64.reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 x (F0 ∗ R) s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error e =>
      exact reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed hs1_step
    | ok tr0 =>
      rcases hs1_step with ⟨s2, hsteps2, trG2, hs2_state⟩
      refine Arm64.reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      have hs2_step := hs2 x trG2 tr0 st1 (F0 ∗ R) s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        rw [hf] at hs2_step
        rcases hs2_step hL2 with ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hfalse⟩⟩
        swap; · exact hfalse.elim
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
          Decrypt.Model.ensureReceiverChain_of_find_error hf
        have hmodel := Decrypt.Model.model_of_ensureReceiverChain_error (S := S) htr herc
        have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne : e ≠ .panic := by
          have he := Decrypt.Model.findReceiverChainKey_error_eq hf
          subst he; decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          Decrypt.Model.decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        exact Arm64.reaches_outcome_steps hsteps2'
          (reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed
            (herr x trG2 tr0 st1 e (F0 ∗ R) s0 s2' hne hm1 hm2 herr_st))
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Arm64.reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            Decrypt.Model.ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (Decrypt.Model.decryptDraws_of_find_some x.rest htr hf).symm
          exact tdp_reaches_outcome_of_consumeMsgKey_placed herr hs4 hs5 hs6 hs7 hs8 hs9
            hseeds hQ hstk htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Arm64.reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(Decrypt.Model.fromSessionState_ok_inv htr).2.1]
            exact hchains
          have hs3_step := hs3 x trG2 tr0 st1 (F0 ∗ R) s0 s3
            htr hf htr_chains hstk hrest hs3_state hL3
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            rw [hdh] at hs3_step
            cases dhRes with
            | error e =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [Decrypt.Model.ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := Decrypt.Model.model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : e ≠ .panic := Decrypt.Model.dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨trG3, r1', herr_st⟩ | ⟨hpan, hq⟩⟩
              · exact Arm64.reaches_outcome_steps hsteps3'
                  (reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed
                    (herr x trG3 { tr0 with ratchet := r1' } st1 e
                      (F0 ∗ R) s0 s3' hne hm1 hm2 herr_st))
              · exact reaches_outcome_of_panicQF_PTight_placed hsteps3' hpan
                  (onPanicTight_drop_frame hq)
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [Decrypt.Model.ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine Arm64.reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact tdp_reaches_outcome_of_consumeMsgKey_placed herr hs4 hs5 hs6 hs7 hs8 hs9
                  hseeds hQ hstk htr herc rfl hs4_state hL4
              · exact reaches_outcome_of_panicQF_PTight_placed hsteps4 hpan
                  (onPanicTight_drop_frame hq)

/-- Relocatable `[LibsignalPlacement]` CLI `try_decrypt_with_state::<Coins>` (Block `433`)
against `tryDecryptSpecTPTightAt` at `S := spqrV1 W.C.F W.Q.K`. -/
theorem tryDecryptV1_placed_ok_PTight_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks)
    (W : CliHooks) (ctl : BitVec 64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hAesDec : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 434)
      (tryDecryptSpecTPTightAt W.C E2E.HooksE.A0 ctl uuidTryParse (spqrV1 W.C.F W.Q.K)) :=
  tryDecrypt_placed_ok_of_seams
    (errTail_433_cli mmpl gh W hG ctl (spqrV1 W.C.F W.Q.K))
    (s0_433_cli mmpl gh W ctl (spqrV1 W.C.F W.Q.K))
    (s1_433_cli mmpl gh W hG ctl (spqrV1 W.C.F W.Q.K))
    (s2_433_cli mmpl gh W ctl)
    (dhStep_433_cli mmpl gh W hG ctl (spqrV1 W.C.F W.Q.K))
    (s4_433_cli mmpl gh W hG ctl (spqrV1 W.C.F W.Q.K))
    (pqRecv_433_cli mmpl gh W hG hSpqr ctl)
    (s6_433_cli mmpl gh W hG ctl)
    (s7_433_cli mmpl gh W hG ctl (spqrV1 W.C.F W.Q.K))
    (aesDecrypt_433_cli mmpl gh W hG hAesDec ctl (spqrV1 W.C.F W.Q.K))
    (s9_433_cli mmpl gh W hG ctl (spqrV1 W.C.F W.Q.K))

end CryptoVerification.Cli.SpqrV1.M4
