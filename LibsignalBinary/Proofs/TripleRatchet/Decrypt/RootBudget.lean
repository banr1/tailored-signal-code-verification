/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model

/-!
# Budget-Threaded Relocatable Root Composition for `try_decrypt_with_state`

Re-exports seam envelopes and precondition helpers from `RootBudgetAux`, and composes the
budget-threaded segment seams (`S0SeamPlaced` .. `S9SeamPlaced` and `ErrTailSeamPlaced`, plus
`decFn` `X` variants) into `try_decrypt_placed_ok_of_seams` and `try_decrypt_placed_ok_of_seams_x`
over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudget

open Arm64 ProofLib
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  ChainKey Crypto MessageKeyGenerator MessageKeys Mut RatchetState
  SessionState SignalMessage SignalProtocolError TripleRatchet aesCbcDecrypt
)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser coinsOf decryptDraws serializeAddresses serviceIdParse uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  SeedsLen32 SpqrModel TrGhost TryDecryptGhost rootStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (decrypt_mkg_seed)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.Model (
  decryptDraws_of_find_error decryptDraws_of_find_some
  dhRatchetStep_error_ne_panic
  ensureReceiverChain_of_find_error ensureReceiverChain_of_find_none
  ensureReceiverChain_of_find_some findReceiverChainKey_error_eq
  fromSessionState_ok_inv
  model_of_aesDec_none model_of_aesDec_some model_of_cmk_error
  model_of_ensureReceiverChain_error model_of_spqr_error model_of_verifyMac_false
  modelFn_of_aesDec_none modelFn_of_aesDec_some modelFn_of_cmk_error
  modelFn_of_ensureReceiverChain_error modelFn_of_spqr_error modelFn_of_verifyMac_false
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  ConsumeMsgKeyStatePlaced ErrTailSeamPlaced ErrTailSeamXPlaced
  S0SeamPlaced S0SeamXPlaced
  S2SeamPlaced S2SeamXPlaced S4SeamPlaced S4SeamXPlaced
  S5SeamPlaced S5SeamXPlaced S6SeamPlaced S6SeamXPlaced S7SeamPlaced S7SeamXPlaced
  S8SeamPlaced S8SeamXPlaced S9SeamPlaced S9SeamXPlaced
  tryDecryptFnSpecPlaced tryDecryptSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (
  FromS1GenEnv FromS2GenEnv FromS3GenEnv FromS4GenEnv
  FromS5GenEnv FromS6GenEnv FromS7GenEnv FromS8GenEnv
  S1SeamPinnedPlaced S1SeamPinnedXPlaced S3SeamPinnedPlaced S3SeamPinnedXPlaced
  caps_trGhostOfCaps fnAesOpt freeOnlyEvs_nil
  fromS2GenEnv_caps fromS2GenEnv_ne fromS3GenEnv_ne
  fromS4GenEnv_caps fromS4GenEnv_ne fromS5GenEnv_ne fromS5GenEnv_trG
  fromS6GenEnv_ne fromS7GenEnv_ne fromS8GenEnv_ne
  s1InitTrGhost s3AfterTrGhost seqEnv_append stdAesOpt trGhostCaps
)

abbrev FromS4EnvsInhabited :=
  LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4EnvsInhabited
abbrev SeamEnvsInhabited :=
  LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.SeamEnvsInhabited
abbrev S1SeamPinnedPlaced :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.S1SeamPinnedPlaced
abbrev S3SeamPinnedPlaced :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.S3SeamPinnedPlaced
abbrev S1SeamPinnedXPlaced :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.S1SeamPinnedXPlaced
abbrev S3SeamPinnedXPlaced :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.S3SeamPinnedXPlaced
abbrev FromS4Env := LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4Env
abbrev FromS1Env := LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS1Env
abbrev FromS4FnEnv := LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4FnEnv
abbrev FromS1FnEnv := LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS1FnEnv
abbrev fitsEnv_of_pre_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.fitsEnv_of_pre_placed
abbrev seedsLen32_of_pre_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.seedsLen32_of_pre_placed
abbrev restLen_of_pre_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.restLen_of_pre_placed
abbrev reaches_outcome_of_panic_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.reaches_outcome_of_panic_placed
abbrev onPanic_of_cmk_panic_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.onPanic_of_cmk_panic_placed
abbrev tryDecryptFnSpecPlaced_pre_eq :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.tryDecryptFnSpecPlaced_pre_eq
abbrev fitsEnv_of_pre_fn_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.fitsEnv_of_pre_fn_placed
abbrev seedsLen32_of_pre_fn_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.seedsLen32_of_pre_fn_placed
abbrev restLen_of_pre_fn_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.restLen_of_pre_fn_placed
abbrev reaches_outcome_of_panic_fn_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.reaches_outcome_of_panic_fn_placed
abbrev onPanic_of_cmk_panic_fn_placed :=
  @LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.onPanic_of_cmk_panic_fn_placed

/-! ## 1. Budget-Threaded Standard Root Composition (`reaches_outcome_of_s4_placed`, `try_decrypt_placed_ok_of_seams`) -/

/-- Post-`ensureReceiverChain` budget-threaded composition (`S4` → `S5` → `S6` → `S7` → `S8` →
`S9` / `ErrTail`). -/
theorem reaches_outcome_of_s4_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    {s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    (hs4 : S4SeamPlaced prog entry C A lim ctl uuidTryParse S s4Env)
    (hs5 : S5SeamPlaced prog entry C A lim ctl uuidTryParse S s5Env)
    (hs6 : S6SeamPlaced prog entry C A lim ctl s6Env)
    (hs7 : S7SeamPlaced prog entry C A lim ctl uuidTryParse S s7Env)
    (hs8 : S8SeamPlaced prog entry C A lim ctl uuidTryParse S s8Env)
    (hs9 : S9SeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv s9Env)
    (herr : ErrTailSeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv)
    {x : TryDecryptGhost} {st_init st4 : M.σ} {trG : TrGhost}
    {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hb4 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st4
      (FromS4Env C uuidTryParse S s4Env s5Env s6Env s7Env s8Env s9Env
        x trG { tr0 with ratchet := r1 } st1 ck))
    (hs4_state : ConsumeMsgKeyStatePlaced entry A lim st4 ctl x trG
      { tr0 with ratchet := r1 } st1 ck draws R s0 s4)
    (hL4 : prog.CodeLoaded s4.mem) :
    reaches_outcome prog (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv)
      (x, st_init) R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := fromSessionState_ok_inv htr
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    have hb4' := hb4
    unfold FromS4Env LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4Env
      FromS4GenEnv at hb4'
    dsimp only at hb4'
    rw [hcmk] at hb4'
    cases cmkRes with
    | error e =>
      have hfits4 : FitsEnv M lim st4 (s4Env x trG { tr0 with ratchet := r1 } ck) :=
        hb4'.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
      have hs4_step := hs4 x st4 trG { tr0 with ratchet := r1 } st1 ck draws R s0 s4
        hfits4 hs4_state hL4
      dsimp only at hs4_step
      rw [hcmk] at hs4_step
      have hmodel := model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne_e, evs4, trG', hevs4, herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        have hberr := hb4'.step (fun _ _ => seqEnv_append) hevs4
        exact reaches_outcome_steps hsteps4
          (herr x st_init (M.stepEvents evs4 st4) trG' { tr0 with ratchet := r2 } st1 e R s0 s4'
            hne_e hm1 hm2 hberr herr_st)
      · exact reaches_outcome_of_panic_placed hsteps4 hpan
          (onPanic_of_cmk_panic_placed hm1 hp hmem)
    | ok mkg =>
      have hne5 : ∃ evs_rem,
          FromS5GenEnv C uuidTryParse S (stdAesOpt C) s5Env s6Env s7Env s8Env s9Env
            x trG { tr0 with ratchet := r2 } st1 mkg evs_rem :=
        fromS5GenEnv_ne (C := C) (parse := uuidTryParse) (S := S) (aesOpt := stdAesOpt C)
          hne x trG { tr0 with ratchet := r2 } st1 mkg
      have hfits4 : FitsEnv M lim st4 (s4Env x trG { tr0 with ratchet := r1 } ck) :=
        hb4'.fitsSeg (fun _ _ => seqEnv_append) hne5
      have hs4_step := hs4 x st4 trG { tr0 with ratchet := r1 } st1 ck draws R s0 s4
        hfits4 hs4_state hL4
      dsimp only at hs4_step
      rw [hcmk] at hs4_step
      rcases hs4_step with ⟨s5, hsteps5, ⟨evs4, trG5, hevs4, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        set st5 := M.stepEvents evs4 st4
        have hb5 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st5
            (FromS5GenEnv C uuidTryParse S (stdAesOpt C) s5Env s6Env s7Env s8Env s9Env
              x trG5 { tr0 with ratchet := r2 } st1 mkg) :=
          (hb4'.step (fun _ _ => seqEnv_append) hevs4).weaken (fun _ he => fromS5GenEnv_trG hne he)
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          unfold FromS5GenEnv at hb5
          dsimp only at hb5
          rw [hspqr] at hb5
          have hfits5 : FitsEnv M lim st5 (s5Env x { tr0 with ratchet := r2 }) :=
            hb5.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
          have hs5_step := hs5 x st5 trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
            hfits5 hpqr0 hs5_state hL5
          dsimp only at hs5_step
          rw [hspqr] at hs5_step
          let e : SignalProtocolError :=
            if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
          have hne_e : e ≠ .panic := by subst e; cases sd <;> nofun
          rcases hs5_step with ⟨s5', hsteps5', ⟨evs5, hevs5, herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · have hmodel := model_of_spqr_error htr herc hcmk hspqr hnp5
            have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
            subst hdraws
            have hberr := hb5.step (fun _ _ => seqEnv_append) hevs5
            exact reaches_outcome_steps hsteps5'
              (herr x st_init (M.stepEvents evs5 st5) trG5 { tr0 with ratchet := r2 } st1 e R s0 s5'
                hne_e hm1 hm2 hberr herr_st)
          · exact reaches_outcome_of_panic_placed hsteps5' hpan hq
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          unfold FromS5GenEnv at hb5
          dsimp only at hb5
          rw [hspqr] at hb5
          have hfits5 : FitsEnv M lim st5 (s5Env x { tr0 with ratchet := r2 }) :=
            hb5.fitsSeg (fun _ _ => seqEnv_append)
              (fromS6GenEnv_ne hne x trG5 { tr0 with ratchet := r2 } st1 mkg newPqrState pqrKey)
          have hs5_step := hs5 x st5 trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
            hfits5 hpqr0 hs5_state hL5
          dsimp only at hs5_step
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s6, hsteps6, ⟨evs5, hevs5, hs6_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · refine reaches_outcome_steps hsteps6 ?_
            have hL6 := hsteps6.codeLoaded hL5
            set st6 := M.stepEvents evs5 st5
            have hb6 := hb5.step (fun _ _ => seqEnv_append) hevs5
            unfold FromS6GenEnv at hb6
            let mks := mkg.generateKeys C.F pqrKey
            have hfits6 : FitsEnv M lim st6 (s6Env mkg) :=
              hb6.fitsSeg (fun _ _ => seqEnv_append)
                (fromS7GenEnv_ne hne x trG5 { tr0 with ratchet := r2 } st1 mks newPqrState)
            have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
            rcases hs6 x st6 trG5 { tr0 with ratchet := r2 } st1 mkg
                newPqrState pqrKey draws R s0 s6 hseed32 hfits6 hs6_state hL6 with
              ⟨s7, hsteps7, ⟨_, _, evs6, hevs6, hs7_state⟩ | ⟨_, hfalse⟩⟩
            swap; · exact hfalse.elim
            refine reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL6
            set st7 := M.stepEvents evs6 st6
            have hb7 := hb6.step (fun _ _ => seqEnv_append) hevs6
            cases hmac : x.msg.verifyMacWithAddresses C.F
                (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
            | false =>
              unfold FromS7GenEnv at hb7
              dsimp only at hb7
              rw [hmac] at hb7
              simp only [Bool.false_eq_true, ↓reduceIte] at hb7
              have hfits7 : FitsEnv M lim st7
                  (s7Env x { tr0 with ratchet := r2 } mks newPqrState) :=
                hb7.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
              have hs7_step := hs7 x st7 trG5 { tr0 with ratchet := r2 }
                st1 mks newPqrState draws R s0 s7 hfits7 hs7_state hL7
              dsimp only at hs7_step
              rw [hmac] at hs7_step
              simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
              have hmodel := model_of_verifyMac_false htr herc hcmk hspqr hmac hnp5
              have hm1 : (x.model C S uuidTryParse).1 =
                  .error (.invalidMessage x.msgType .macFailed) := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne_e : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
              rcases hs7_step with ⟨s7', hsteps7', ⟨evs7, hevs7, herr_st⟩ | ⟨hpan, hq⟩⟩
              · subst hdraws
                have hberr := hb7.step (fun _ _ => seqEnv_append) hevs7
                exact reaches_outcome_steps hsteps7'
                  (herr x st_init (M.stepEvents evs7 st7) trG5 { tr0 with ratchet := r2 } st1
                    (.invalidMessage x.msgType .macFailed) R s0 s7' hne_e hm1 hm2 hberr herr_st)
              · exact reaches_outcome_of_panic_placed hsteps7' hpan hq
            | true =>
              unfold FromS7GenEnv at hb7
              dsimp only at hb7
              rw [hmac] at hb7
              simp only [↓reduceIte] at hb7
              have hfits7 : FitsEnv M lim st7
                  (s7Env x { tr0 with ratchet := r2 } mks newPqrState) :=
                hb7.fitsSeg (fun _ _ => seqEnv_append)
                  (fromS8GenEnv_ne hne x trG5 { tr0 with ratchet := r2 } st1 mks newPqrState)
              have hs7_step := hs7 x st7 trG5 { tr0 with ratchet := r2 }
                st1 mks newPqrState draws R s0 s7 hfits7 hs7_state hL7
              dsimp only at hs7_step
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, ⟨evs7, hevs7, hs8_state⟩ | ⟨hpan, hq⟩⟩
              · refine reaches_outcome_steps hsteps8 ?_
                have hL8 := hsteps8.codeLoaded hL7
                set st8 := M.stepEvents evs7 st7
                have hb8 := hb7.step (fun _ _ => seqEnv_append) hevs7
                unfold FromS8GenEnv stdAesOpt at hb8
                cases haes : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
                | none =>
                  rw [haes] at hb8
                  have hfits8 : FitsEnv M lim st8 (s8Env x mks newPqrState) :=
                    hb8.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
                  have hs8_step := hs8 x st8 trG5 { tr0 with ratchet := r2 }
                    st1 mks newPqrState draws R s0 s8 hfits8 hs8_state hL8
                  rw [haes] at hs8_step
                  have hmodel := model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 =
                      .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
                  have hne_e : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic :=
                    nofun
                  rcases hs8_step with ⟨s8', hsteps8', ⟨evs8, hevs8, herr_st⟩ | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    have hberr := hb8.step (fun _ _ => seqEnv_append) hevs8
                    exact reaches_outcome_steps hsteps8'
                      (herr x st_init (M.stepEvents evs8 st8) trG5 { tr0 with ratchet := r2 } st1
                        (.invalidMessage x.msgType .badCiphertext) R s0 s8'
                        hne_e hm1 hm2 hberr herr_st)
                  · exact reaches_outcome_of_panic_placed hsteps8' hpan hq
                | some pt =>
                  rw [haes] at hb8
                  have hfits8 : FitsEnv M lim st8 (s8Env x mks newPqrState) :=
                    hb8.fitsSeg (fun _ _ => seqEnv_append)
                      (hne.s9 x trG5 { tr0 with ratchet := r2 } st1 newPqrState)
                  have hs8_step := hs8 x st8 trG5 { tr0 with ratchet := r2 }
                    st1 mks newPqrState draws R s0 s8 hfits8 hs8_state hL8
                  rw [haes] at hs8_step
                  have hmodel := model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 =
                      (({ { tr0 with ratchet := r2 } with pqrState := newPqrState }).applyToSessionState
                        st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
                  rcases hs8_step with ⟨s9, hsteps9, ⟨evs8, hevs8, hs9_state⟩ | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    have hb9 := hb8.step (fun _ _ => seqEnv_append) hevs8
                    exact reaches_outcome_steps hsteps9
                      (hs9 x st_init (M.stepEvents evs8 st8) trG5 { tr0 with ratchet := r2 }
                        st1 newPqrState pt R s0 s9 hm1 hm2 hb9 hs9_state)
                  · exact reaches_outcome_of_panic_placed hsteps9 hpan hq
              · exact reaches_outcome_of_panic_placed hsteps8 hpan hq
          · exact reaches_outcome_of_panic_placed hsteps6 hpan hq
      · exact reaches_outcome_of_panic_placed hsteps5 hpan hq

/-- Budget-threaded relocatable `[LibsignalPlacement]` root composition on any `prog : Program` and
`entry : BitVec 64`. -/
theorem try_decrypt_placed_ok_of_seams [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    {s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (htdEnv : ∀ x evs,
      FromS1Env C uuidTryParse S s1OkEnv s3Env s4Env s5Env s6Env s7Env s8Env s9Env x evs →
      tdEnv (tryDecryptEnvArgs x) evs)
    (hne : SeamEnvsInhabited s3Env s4Env s5Env s6Env s7Env s8Env s9Env)
    (hs0 : S0SeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv)
    (hs1 : S1SeamPinnedPlaced prog entry C A lim ctl uuidTryParse S tdEnv s1OkEnv)
    (hs2 : S2SeamPlaced prog entry A lim ctl)
    (hs3 : S3SeamPinnedPlaced prog entry C A lim ctl uuidTryParse S s3Env)
    (hs4 : S4SeamPlaced prog entry C A lim ctl uuidTryParse S s4Env)
    (hs5 : S5SeamPlaced prog entry C A lim ctl uuidTryParse S s5Env)
    (hs6 : S6SeamPlaced prog entry C A lim ctl s6Env)
    (hs7 : S7SeamPlaced prog entry C A lim ctl uuidTryParse S s7Env)
    (hs8 : S8SeamPlaced prog entry C A lim ctl uuidTryParse S s8Env)
    (hs9 : S9SeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv s9Env)
    (herr : ErrTailSeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv) :
    subroutine_ok prog entry (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre hsp
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  have hfits0 : FitsEnv M lim st_init (tdEnv (tryDecryptEnvArgs x)) :=
    fitsEnv_of_pre_placed hpre
  have hb0 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st_init
      (FromS1Env C uuidTryParse S s1OkEnv s3Env s4Env s5Env s6Env s7Env s8Env s9Env x) :=
    (SeamBudget.init hfits0).weaken (htdEnv x)
  obtain ⟨hseeds, hchains, hstk⟩ := seedsLen32_of_pre_placed hpre
  have hrest : x.rest.length < 2 ^ 63 := restLen_of_pre_placed hpre
  rcases hs0 x st_init R s0 hpc hrun hsp hpre hL with
    ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hfalse⟩⟩
  swap; · exact hfalse.elim
  refine reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 x st_init st_init R s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    unfold FromS1Env LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS1Env
      FromS1GenEnv at hb0
    rw [htr] at hs1_step hb0
    cases trRes with
    | error _ =>
      exact hs1_step hb0
    | ok tr0 =>
      have hne2 : ∃ evs_rem,
          FromS2GenEnv C uuidTryParse S (stdAesOpt C) s3Env s4Env s5Env s6Env s7Env s8Env s9Env
            x (s1InitTrGhost x.G) tr0 st1 evs_rem :=
        fromS2GenEnv_ne (C := C) (parse := uuidTryParse) (S := S) (aesOpt := stdAesOpt C)
          hne x (s1InitTrGhost x.G) tr0 st1
      have hfits1 : FitsEnv M lim st_init (s1OkEnv x) :=
        hb0.fitsSeg (fun _ _ => seqEnv_append) hne2
      rcases hs1_step hfits1 with ⟨s2, hsteps2, evs1, trG2, hevs1, hcaps2, hs2_state⟩
      refine reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      set st2 := M.stepEvents evs1 st_init
      have hcaps2' : trGhostCaps trG2 = trGhostCaps (s1InitTrGhost x.G) :=
        hcaps2.trans (caps_trGhostOfCaps _).symm
      have hb2 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st2
          (FromS2GenEnv C uuidTryParse S (stdAesOpt C) s3Env s4Env s5Env s6Env s7Env s8Env s9Env
            x trG2 tr0 st1) :=
        (hb0.step (fun _ _ => seqEnv_append) hevs1).weaken
          (fun _ he => fromS2GenEnv_caps hne hcaps2' he)
      have hs2_step := hs2 x st2 trG2 tr0 st1 R s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        unfold FromS2GenEnv at hb2
        rw [hf] at hs2_step hb2
        rcases hs2_step hL2 with ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hfalse⟩⟩
        swap; · exact hfalse.elim
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
          ensureReceiverChain_of_find_error hf
        have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
        have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne_e : e ≠ .panic := by
          have he := findReceiverChainKey_error_eq hf
          subst he
          decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        exact reaches_outcome_steps hsteps2'
          (herr x st_init st2 trG2 tr0 st1 e R s0 s2' hne_e hm1 hm2 hb2 herr_st)
      | ok optCk =>
        cases optCk with
        | some ck =>
          unfold FromS2GenEnv at hb2
          rw [hf] at hs2_step hb2
          rcases hs2_step hL2 with ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (decryptDraws_of_find_some x.rest htr hf).symm
          have htr0_eta : ({ tr0 with ratchet := tr0.ratchet } : TripleRatchet (List (BitVec 8))) = tr0 := by
            cases tr0; rfl
          have hs4_state' : ConsumeMsgKeyStatePlaced entry A lim st2 ctl x trG2
              { tr0 with ratchet := tr0.ratchet } st1 ck 0 R s0 s4 := by
            rw [htr0_eta]; exact hs4_state
          have hb4 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st2
              (FromS4Env C uuidTryParse S s4Env s5Env s6Env s7Env s8Env s9Env
                x trG2 { tr0 with ratchet := tr0.ratchet } st1 ck) := by
            unfold FromS4Env LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4Env
            rw [htr0_eta]; exact hb2
          exact reaches_outcome_of_s4_placed hne.toFromS4EnvsInhabited
            hs4 hs5 hs6 hs7 hs8 hs9 herr hseeds htr herc hdraws hb4 hs4_state' hL4
        | none =>
          unfold FromS2GenEnv at hb2
          rw [hf] at hs2_step hb2
          rcases hs2_step hL2 with ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(fromSessionState_ok_inv htr).2.1]
            exact hchains
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            unfold FromS3GenEnv at hb2
            rw [hdh] at hb2
            cases dhRes with
            | error e =>
              have hfits3 : FitsEnv M lim st2 (s3Env x trG2 tr0) :=
                hb2.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
              have hs3_step := hs3 x st2 trG2 tr0 st1 R s0 s3 htr hf htr_chains hstk hrest
                hfits3 hs3_state hL3
              dsimp only at hs3_step
              rw [hdh] at hs3_step
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne_e : e ≠ .panic := dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨evs3, trG3, r1', hevs3, herr_st⟩ | ⟨hpan, hq⟩⟩
              · have hberr := hb2.step (fun _ _ => seqEnv_append) hevs3
                exact reaches_outcome_steps hsteps3'
                  (herr x st_init (M.stepEvents evs3 st2) trG3 { tr0 with ratchet := r1' } st1 e
                    R s0 s3' hne_e hm1 hm2 hberr herr_st)
              · exact reaches_outcome_of_panic_placed hsteps3' hpan hq
            | ok ck =>
              have hne4 : ∃ evs_rem,
                  FromS4GenEnv C uuidTryParse S (stdAesOpt C) s4Env s5Env s6Env s7Env s8Env s9Env
                    x (s3AfterTrGhost trG2 tr0.ratchet.receiverChains.length)
                    { tr0 with ratchet := r1 } st1 ck evs_rem :=
                fromS4GenEnv_ne (C := C) (parse := uuidTryParse) (S := S) (aesOpt := stdAesOpt C)
                  hne.toFromS4EnvsInhabited
                  x (s3AfterTrGhost trG2 tr0.ratchet.receiverChains.length)
                  { tr0 with ratchet := r1 } st1 ck
              have hfits3 : FitsEnv M lim st2 (s3Env x trG2 tr0) :=
                hb2.fitsSeg (fun _ _ => seqEnv_append) hne4
              have hs3_step := hs3 x st2 trG2 tr0 st1 R s0 s3 htr hf htr_chains hstk hrest
                hfits3 hs3_state hL3
              dsimp only at hs3_step
              rw [hdh] at hs3_step
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨evs3, trG4, hevs3, hcaps4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                have hcaps4' :
                    trGhostCaps trG4 =
                      trGhostCaps (s3AfterTrGhost trG2 tr0.ratchet.receiverChains.length) :=
                  hcaps4.trans (caps_trGhostOfCaps _).symm
                have hb4 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init
                    (M.stepEvents evs3 st2)
                    (FromS4Env C uuidTryParse S s4Env s5Env s6Env s7Env s8Env s9Env
                      x trG4 { tr0 with ratchet := r1 } st1 ck) :=
                  (hb2.step (fun _ _ => seqEnv_append) hevs3).weaken
                    (fun _ he => fromS4GenEnv_caps hne.toFromS4EnvsInhabited hcaps4' he)
                exact reaches_outcome_of_s4_placed hne.toFromS4EnvsInhabited
                  hs4 hs5 hs6 hs7 hs8 hs9 herr hseeds htr herc rfl hb4 hs4_state hL4
              · exact reaches_outcome_of_panic_placed hsteps4 hpan hq

/-! ## 2. Budget-Threaded `Stage2ContractsX` (`decFn` / `X`) Root Composition -/

/-- Post-`ensureReceiverChain` budget-threaded `decFn` (`X`) composition (`S4X` → `S5X` → `S6X` →
`S7X` → `S8X` → `S9X` / `ErrTailX`). -/
theorem reaches_outcome_of_s4_x_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    {s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    (hs4 : S4SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S s4Env)
    (hs5 : S5SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S s5Env)
    (hs6 : S6SeamXPlaced prog entry C A lim ctl s6Env)
    (hs7 : S7SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S s7Env)
    (hs8 : S8SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S s8Env)
    (hs9 : S9SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S tdEnv s9Env)
    (herr : ErrTailSeamXPlaced prog entry C decFn A lim ctl uuidTryParse S tdEnv)
    {x : TryDecryptGhost} {st_init st4 : M.σ} {trG : TrGhost}
    {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hb4 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st4
      (FromS4FnEnv C decFn uuidTryParse S s4Env s5Env s6Env s7Env s8Env s9Env
        x trG { tr0 with ratchet := r1 } st1 ck))
    (hs4_state : ConsumeMsgKeyStatePlaced entry A lim st4 ctl x trG
      { tr0 with ratchet := r1 } st1 ck draws R s0 s4)
    (hL4 : prog.CodeLoaded s4.mem) :
    reaches_outcome prog (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv)
      (x, st_init) R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := fromSessionState_ok_inv htr
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    have hb4' := hb4
    unfold FromS4FnEnv LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4FnEnv
      FromS4GenEnv at hb4'
    dsimp only at hb4'
    rw [hcmk] at hb4'
    cases cmkRes with
    | error e =>
      have hfits4 : FitsEnv M lim st4 (s4Env x trG { tr0 with ratchet := r1 } ck) :=
        hb4'.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
      have hs4_step := hs4 x st4 trG { tr0 with ratchet := r1 } st1 ck draws R s0 s4
        hfits4 hs4_state hL4
      dsimp only at hs4_step
      rw [hcmk] at hs4_step
      have hmodel := modelFn_of_cmk_error (decFn := decFn) (S := S) htr herc hcmk
      have hm1 : (x.modelFn C decFn S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.modelFn C decFn S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne_e, evs4, trG', hevs4, herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        have hberr := hb4'.step (fun _ _ => seqEnv_append) hevs4
        exact reaches_outcome_steps hsteps4
          (herr x st_init (M.stepEvents evs4 st4) trG' { tr0 with ratchet := r2 } st1 e R s0 s4'
            hne_e hm1 hm2 hberr herr_st.toX)
      · exact reaches_outcome_of_panic_fn_placed hsteps4 hpan
          (onPanic_of_cmk_panic_fn_placed hm1 hp hmem)
    | ok mkg =>
      have hne5 : ∃ evs_rem,
          FromS5GenEnv C uuidTryParse S (fnAesOpt decFn) s5Env s6Env s7Env s8Env s9Env
            x trG { tr0 with ratchet := r2 } st1 mkg evs_rem :=
        fromS5GenEnv_ne (C := C) (parse := uuidTryParse) (S := S) (aesOpt := fnAesOpt decFn)
          hne x trG { tr0 with ratchet := r2 } st1 mkg
      have hfits4 : FitsEnv M lim st4 (s4Env x trG { tr0 with ratchet := r1 } ck) :=
        hb4'.fitsSeg (fun _ _ => seqEnv_append) hne5
      have hs4_step := hs4 x st4 trG { tr0 with ratchet := r1 } st1 ck draws R s0 s4
        hfits4 hs4_state hL4
      dsimp only at hs4_step
      rw [hcmk] at hs4_step
      rcases hs4_step with ⟨s5, hsteps5, ⟨evs4, trG5, hevs4, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        set st5 := M.stepEvents evs4 st4
        have hb5 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st5
            (FromS5GenEnv C uuidTryParse S (fnAesOpt decFn) s5Env s6Env s7Env s8Env s9Env
              x trG5 { tr0 with ratchet := r2 } st1 mkg) :=
          (hb4'.step (fun _ _ => seqEnv_append) hevs4).weaken (fun _ he => fromS5GenEnv_trG hne he)
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          unfold FromS5GenEnv at hb5
          dsimp only at hb5
          rw [hspqr] at hb5
          have hfits5 : FitsEnv M lim st5 (s5Env x { tr0 with ratchet := r2 }) :=
            hb5.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
          have hs5_step := hs5 x st5 trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
            hfits5 hpqr0 hs5_state hL5
          dsimp only at hs5_step
          rw [hspqr] at hs5_step
          let e : SignalProtocolError :=
            if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
          have hne_e : e ≠ .panic := by subst e; cases sd <;> nofun
          rcases hs5_step with ⟨s5', hsteps5', ⟨evs5, hevs5, herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · have hmodel := modelFn_of_spqr_error (decFn := decFn) htr herc hcmk hspqr hnp5
            have hm1 : (x.modelFn C decFn S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.modelFn C decFn S uuidTryParse).2 = st1 := by rw [hmodel]
            subst hdraws
            have hberr := hb5.step (fun _ _ => seqEnv_append) hevs5
            exact reaches_outcome_steps hsteps5'
              (herr x st_init (M.stepEvents evs5 st5) trG5 { tr0 with ratchet := r2 } st1 e R s0 s5'
                hne_e hm1 hm2 hberr herr_st.toX)
          · exact reaches_outcome_of_panic_fn_placed hsteps5' hpan hq
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          unfold FromS5GenEnv at hb5
          dsimp only at hb5
          rw [hspqr] at hb5
          have hfits5 : FitsEnv M lim st5 (s5Env x { tr0 with ratchet := r2 }) :=
            hb5.fitsSeg (fun _ _ => seqEnv_append)
              (fromS6GenEnv_ne hne x trG5 { tr0 with ratchet := r2 } st1 mkg newPqrState pqrKey)
          have hs5_step := hs5 x st5 trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
            hfits5 hpqr0 hs5_state hL5
          dsimp only at hs5_step
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s6, hsteps6, ⟨evs5, hevs5, hs6_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · refine reaches_outcome_steps hsteps6 ?_
            have hL6 := hsteps6.codeLoaded hL5
            set st6 := M.stepEvents evs5 st5
            have hb6 := hb5.step (fun _ _ => seqEnv_append) hevs5
            unfold FromS6GenEnv at hb6
            let mks := mkg.generateKeys C.F pqrKey
            have hfits6 : FitsEnv M lim st6 (s6Env mkg) :=
              hb6.fitsSeg (fun _ _ => seqEnv_append)
                (fromS7GenEnv_ne hne x trG5 { tr0 with ratchet := r2 } st1 mks newPqrState)
            have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
            rcases hs6 x st6 trG5 { tr0 with ratchet := r2 } st1 mkg
                newPqrState pqrKey draws R s0 s6 hseed32 hfits6 hs6_state hL6 with
              ⟨s7, hsteps7, ⟨_, _, evs6, hevs6, hs7_state⟩ | ⟨_, hfalse⟩⟩
            swap; · exact hfalse.elim
            refine reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL6
            set st7 := M.stepEvents evs6 st6
            have hb7 := hb6.step (fun _ _ => seqEnv_append) hevs6
            cases hmac : x.msg.verifyMacWithAddresses C.F
                (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
            | false =>
              unfold FromS7GenEnv at hb7
              dsimp only at hb7
              rw [hmac] at hb7
              simp only [Bool.false_eq_true, ↓reduceIte] at hb7
              have hfits7 : FitsEnv M lim st7
                  (s7Env x { tr0 with ratchet := r2 } mks newPqrState) :=
                hb7.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
              have hs7_step := hs7 x st7 trG5 { tr0 with ratchet := r2 }
                st1 mks newPqrState draws R s0 s7 hfits7 hs7_state hL7
              dsimp only at hs7_step
              rw [hmac] at hs7_step
              simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
              have hmodel := modelFn_of_verifyMac_false (decFn := decFn) htr herc hcmk hspqr hmac hnp5
              have hm1 : (x.modelFn C decFn S uuidTryParse).1 =
                  .error (.invalidMessage x.msgType .macFailed) := by rw [hmodel]
              have hm2 : (x.modelFn C decFn S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne_e : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
              rcases hs7_step with ⟨s7', hsteps7', ⟨evs7, hevs7, herr_st⟩ | ⟨hpan, hq⟩⟩
              · subst hdraws
                have hberr := hb7.step (fun _ _ => seqEnv_append) hevs7
                exact reaches_outcome_steps hsteps7'
                  (herr x st_init (M.stepEvents evs7 st7) trG5 { tr0 with ratchet := r2 } st1
                    (.invalidMessage x.msgType .macFailed) R s0 s7'
                    hne_e hm1 hm2 hberr herr_st.toX)
              · exact reaches_outcome_of_panic_fn_placed hsteps7' hpan hq
            | true =>
              unfold FromS7GenEnv at hb7
              dsimp only at hb7
              rw [hmac] at hb7
              simp only [↓reduceIte] at hb7
              have hfits7 : FitsEnv M lim st7
                  (s7Env x { tr0 with ratchet := r2 } mks newPqrState) :=
                hb7.fitsSeg (fun _ _ => seqEnv_append)
                  (fromS8GenEnv_ne hne x trG5 { tr0 with ratchet := r2 } st1 mks newPqrState)
              have hs7_step := hs7 x st7 trG5 { tr0 with ratchet := r2 }
                st1 mks newPqrState draws R s0 s7 hfits7 hs7_state hL7
              dsimp only at hs7_step
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, ⟨evs7, hevs7, hs8_state⟩ | ⟨hpan, hq⟩⟩
              · refine reaches_outcome_steps hsteps8 ?_
                have hL8 := hsteps8.codeLoaded hL7
                set st8 := M.stepEvents evs7 st7
                have hb8 := hb7.step (fun _ _ => seqEnv_append) hevs7
                unfold FromS8GenEnv fnAesOpt at hb8
                cases haes : decFn x.msg.ciphertext
                    (keyToBytes32 mks.cipherKey) (blockToBytesLE mks.iv) with
                | none =>
                  rw [haes] at hb8
                  have hfits8 : FitsEnv M lim st8 (s8Env x mks newPqrState) :=
                    hb8.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
                  have hs8_step := hs8 x st8 trG5 { tr0 with ratchet := r2 }
                    st1 mks newPqrState draws R s0 s8 hfits8 hs8_state hL8
                  rw [haes] at hs8_step
                  have hmodel := modelFn_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.modelFn C decFn S uuidTryParse).1 =
                      .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
                  have hm2 : (x.modelFn C decFn S uuidTryParse).2 = st1 := by rw [hmodel]
                  have hne_e : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic :=
                    nofun
                  rcases hs8_step with ⟨s8', hsteps8', ⟨evs8, hevs8, herr_st⟩ | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    have hberr := hb8.step (fun _ _ => seqEnv_append) hevs8
                    exact reaches_outcome_steps hsteps8'
                      (herr x st_init (M.stepEvents evs8 st8) trG5 { tr0 with ratchet := r2 } st1
                        (.invalidMessage x.msgType .badCiphertext) R s0 s8'
                        hne_e hm1 hm2 hberr herr_st)
                  · exact reaches_outcome_of_panic_fn_placed hsteps8' hpan hq
                | some pt =>
                  rw [haes] at hb8
                  have hfits8 : FitsEnv M lim st8 (s8Env x mks newPqrState) :=
                    hb8.fitsSeg (fun _ _ => seqEnv_append)
                      (hne.s9 x trG5 { tr0 with ratchet := r2 } st1 newPqrState)
                  have hs8_step := hs8 x st8 trG5 { tr0 with ratchet := r2 }
                    st1 mks newPqrState draws R s0 s8 hfits8 hs8_state hL8
                  rw [haes] at hs8_step
                  have hmodel := modelFn_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.modelFn C decFn S uuidTryParse).1 = .ok pt := by rw [hmodel]
                  have hm2 : (x.modelFn C decFn S uuidTryParse).2 =
                      (({ { tr0 with ratchet := r2 } with pqrState := newPqrState }).applyToSessionState
                        st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
                  rcases hs8_step with ⟨s9, hsteps9, ⟨evs8, hevs8, hs9_state⟩ | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    have hb9 := hb8.step (fun _ _ => seqEnv_append) hevs8
                    exact reaches_outcome_steps hsteps9
                      (hs9 x st_init (M.stepEvents evs8 st8) trG5 { tr0 with ratchet := r2 }
                        st1 newPqrState pt R s0 s9 hm1 hm2 hb9 hs9_state)
                  · exact reaches_outcome_of_panic_fn_placed hsteps9 hpan hq
              · exact reaches_outcome_of_panic_fn_placed hsteps8 hpan hq
          · exact reaches_outcome_of_panic_fn_placed hsteps6 hpan hq
      · exact reaches_outcome_of_panic_fn_placed hsteps5 hpan hq

/-- Budget-threaded relocatable `[LibsignalPlacement]` `decFn` root composition on any
`prog : Program` and `entry : BitVec 64`. -/
theorem try_decrypt_placed_ok_of_seams_x [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    {s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (htdEnv : ∀ x evs,
      FromS1FnEnv C decFn uuidTryParse S s1OkEnv s3Env s4Env s5Env s6Env s7Env s8Env s9Env x evs →
      tdEnv (tryDecryptEnvArgs x) evs)
    (hne : SeamEnvsInhabited s3Env s4Env s5Env s6Env s7Env s8Env s9Env)
    (hs0 : S0SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S tdEnv)
    (hs1 : S1SeamPinnedXPlaced prog entry C decFn A lim ctl uuidTryParse S tdEnv s1OkEnv)
    (hs2 : S2SeamXPlaced prog entry A lim ctl)
    (hs3 : S3SeamPinnedXPlaced prog entry C decFn A lim ctl uuidTryParse S s3Env)
    (hs4 : S4SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S s4Env)
    (hs5 : S5SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S s5Env)
    (hs6 : S6SeamXPlaced prog entry C A lim ctl s6Env)
    (hs7 : S7SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S s7Env)
    (hs8 : S8SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S s8Env)
    (hs9 : S9SeamXPlaced prog entry C decFn A lim ctl uuidTryParse S tdEnv s9Env)
    (herr : ErrTailSeamXPlaced prog entry C decFn A lim ctl uuidTryParse S tdEnv) :
    subroutine_ok prog entry (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre hsp
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  have hfits0 : FitsEnv M lim st_init (tdEnv (tryDecryptEnvArgs x)) :=
    fitsEnv_of_pre_fn_placed hpre
  have hb0 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st_init
      (FromS1FnEnv C decFn uuidTryParse S s1OkEnv s3Env s4Env s5Env s6Env s7Env s8Env s9Env x) :=
    (SeamBudget.init hfits0).weaken (htdEnv x)
  obtain ⟨hseeds, hchains, hstk⟩ := seedsLen32_of_pre_fn_placed hpre
  have hrest : x.rest.length < 2 ^ 63 := restLen_of_pre_fn_placed hpre
  rcases hs0 x st_init R s0 hpc hrun hsp hpre hL with
    ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hfalse⟩⟩
  swap; · exact hfalse.elim
  refine reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 x st_init st_init R s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    unfold FromS1FnEnv LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS1FnEnv
      FromS1GenEnv at hb0
    rw [htr] at hs1_step hb0
    cases trRes with
    | error _ =>
      exact hs1_step hb0
    | ok tr0 =>
      have hne2 : ∃ evs_rem,
          FromS2GenEnv C uuidTryParse S (fnAesOpt decFn) s3Env s4Env s5Env s6Env s7Env s8Env s9Env
            x (s1InitTrGhost x.G) tr0 st1 evs_rem :=
        fromS2GenEnv_ne (C := C) (parse := uuidTryParse) (S := S) (aesOpt := fnAesOpt decFn)
          hne x (s1InitTrGhost x.G) tr0 st1
      have hfits1 : FitsEnv M lim st_init (s1OkEnv x) :=
        hb0.fitsSeg (fun _ _ => seqEnv_append) hne2
      rcases hs1_step hfits1 with ⟨s2, hsteps2, evs1, trG2, hevs1, hcaps2, hs2_state⟩
      refine reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      set st2 := M.stepEvents evs1 st_init
      have hcaps2' : trGhostCaps trG2 = trGhostCaps (s1InitTrGhost x.G) :=
        hcaps2.trans (caps_trGhostOfCaps _).symm
      have hb2 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st2
          (FromS2GenEnv C uuidTryParse S (fnAesOpt decFn) s3Env s4Env s5Env s6Env s7Env s8Env s9Env
            x trG2 tr0 st1) :=
        (hb0.step (fun _ _ => seqEnv_append) hevs1).weaken
          (fun _ he => fromS2GenEnv_caps hne hcaps2' he)
      have hs2_step := hs2 x st2 trG2 tr0 st1 R s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        unfold FromS2GenEnv at hb2
        rw [hf] at hs2_step hb2
        rcases hs2_step hL2 with ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hfalse⟩⟩
        swap; · exact hfalse.elim
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
          ensureReceiverChain_of_find_error hf
        have hmodel := modelFn_of_ensureReceiverChain_error (decFn := decFn) (S := S) htr herc
        have hm1 : (x.modelFn C decFn S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.modelFn C decFn S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne_e : e ≠ .panic := by
          rw [findReceiverChainKey_error_eq hf]
          nofun
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        exact reaches_outcome_steps hsteps2'
          (herr x st_init st2 trG2 tr0 st1 e R s0 s2' hne_e hm1 hm2 hb2 herr_st.toX)
      | ok optCk =>
        cases optCk with
        | some ck =>
          unfold FromS2GenEnv at hb2
          rw [hf] at hs2_step hb2
          rcases hs2_step hL2 with ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (decryptDraws_of_find_some x.rest htr hf).symm
          have htr0_eta : ({ tr0 with ratchet := tr0.ratchet } : TripleRatchet (List (BitVec 8))) = tr0 := by
            cases tr0; rfl
          have hs4_state' : ConsumeMsgKeyStatePlaced entry A lim st2 ctl x trG2
              { tr0 with ratchet := tr0.ratchet } st1 ck 0 R s0 s4 := by
            rw [htr0_eta]; exact hs4_state
          have hb4 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st2
              (FromS4FnEnv C decFn uuidTryParse S s4Env s5Env s6Env s7Env s8Env s9Env
                x trG2 { tr0 with ratchet := tr0.ratchet } st1 ck) := by
            unfold FromS4FnEnv LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4FnEnv
            rw [htr0_eta]; exact hb2
          exact reaches_outcome_of_s4_x_placed hne.toFromS4EnvsInhabited
            hs4 hs5 hs6 hs7 hs8 hs9 herr hseeds htr herc hdraws hb4 hs4_state' hL4
        | none =>
          unfold FromS2GenEnv at hb2
          rw [hf] at hs2_step hb2
          rcases hs2_step hL2 with ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(fromSessionState_ok_inv htr).2.1]
            exact hchains
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            unfold FromS3GenEnv at hb2
            rw [hdh] at hb2
            cases dhRes with
            | error e =>
              have hfits3 : FitsEnv M lim st2 (s3Env x trG2 tr0) :=
                hb2.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
              have hs3_step := hs3 x st2 trG2 tr0 st1 R s0 s3 htr hf htr_chains hstk hrest
                hfits3 hs3_state hL3
              dsimp only at hs3_step
              rw [hdh] at hs3_step
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := modelFn_of_ensureReceiverChain_error (decFn := decFn) (S := S) htr herc
              have hm1 : (x.modelFn C decFn S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.modelFn C decFn S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne_e : e ≠ .panic := dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨evs3, trG3, r1', hevs3, herr_st⟩ | ⟨hpan, hq⟩⟩
              · have hberr := hb2.step (fun _ _ => seqEnv_append) hevs3
                exact reaches_outcome_steps hsteps3'
                  (herr x st_init (M.stepEvents evs3 st2) trG3 { tr0 with ratchet := r1' } st1 e
                    R s0 s3' hne_e hm1 hm2 hberr herr_st.toX)
              · exact reaches_outcome_of_panic_fn_placed hsteps3' hpan hq
            | ok ck =>
              have hne4 : ∃ evs_rem,
                  FromS4GenEnv C uuidTryParse S (fnAesOpt decFn) s4Env s5Env s6Env s7Env s8Env s9Env
                    x (s3AfterTrGhost trG2 tr0.ratchet.receiverChains.length)
                    { tr0 with ratchet := r1 } st1 ck evs_rem :=
                fromS4GenEnv_ne (C := C) (parse := uuidTryParse) (S := S) (aesOpt := fnAesOpt decFn)
                  hne.toFromS4EnvsInhabited
                  x (s3AfterTrGhost trG2 tr0.ratchet.receiverChains.length)
                  { tr0 with ratchet := r1 } st1 ck
              have hfits3 : FitsEnv M lim st2 (s3Env x trG2 tr0) :=
                hb2.fitsSeg (fun _ _ => seqEnv_append) hne4
              have hs3_step := hs3 x st2 trG2 tr0 st1 R s0 s3 htr hf htr_chains hstk hrest
                hfits3 hs3_state hL3
              dsimp only at hs3_step
              rw [hdh] at hs3_step
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨evs3, trG4, hevs3, hcaps4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                have hcaps4' :
                    trGhostCaps trG4 =
                      trGhostCaps (s3AfterTrGhost trG2 tr0.ratchet.receiverChains.length) :=
                  hcaps4.trans (caps_trGhostOfCaps _).symm
                have hb4 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init
                    (M.stepEvents evs3 st2)
                    (FromS4FnEnv C decFn uuidTryParse S s4Env s5Env s6Env s7Env s8Env s9Env
                      x trG4 { tr0 with ratchet := r1 } st1 ck) :=
                  (hb2.step (fun _ _ => seqEnv_append) hevs3).weaken
                    (fun _ he => fromS4GenEnv_caps hne.toFromS4EnvsInhabited hcaps4' he)
                exact reaches_outcome_of_s4_x_placed hne.toFromS4EnvsInhabited
                  hs4 hs5 hs6 hs7 hs8 hs9 herr hseeds htr herc rfl hb4 hs4_state hL4
              · exact reaches_outcome_of_panic_fn_placed hsteps4 hpan hq

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudget
