/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model

/-!
# Budget-Threaded Relocatable `try_decrypt_with_state` Assembly on CLI Block `433`

Defines pointer-free `TryDecryptCliEnvOf` / `TryDecryptCliEnv` allocation-event envelopes and
assembles the 11 budget-threaded Block-`433` segment seams into `tryDecrypt_placed_ok_of_seams` and
`tryDecryptV1_placed_ok_PTight_cli` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget

open Arm64 ProofLib
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair MessageKeyGenerator MessageKeys Mut PublicKey RatchetState
  SessionState SignalMessage SignalProtocolError TripleRatchet aesCbcDecrypt rootCreateChain
)
open CryptoVerification (
  LibsignalPlacement lsmpl
)
open CryptoVerification.E2E (aesDecHookMallocng)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded SeedsLen32 SendCall SpqrModel TrGhost TryDecryptGhost rootStack
  withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (blkPC_434 blkPl_434 decrypt_mkg_seed)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.Model (
  decryptDraws_of_find_error decryptDraws_of_find_some dhRatchetStep_error_ne_panic
  ensureReceiverChain_of_find_error ensureReceiverChain_of_find_none
  ensureReceiverChain_of_find_some findReceiverChainKey_error_eq fromSessionState_ok_inv
  model_of_aesDec_none model_of_aesDec_some model_of_cmk_error
  model_of_ensureReceiverChain_error model_of_spqr_error model_of_verifyMac_false
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  coinsOf decryptDraws serializeAddresses serviceIdParse uuidTryParse
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsFmtWriteSym lsFormatInnerSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec formatInnerBudgetEnvSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget (
  fitsEnv_of_pre_P_placed onPanicTight_drop_frame onPanicTight_of_cmk_panic
  reaches_outcome_of_panicQF_PTight_placed reaches_outcome_tryDecryptSpecQF_PTight_of_afterCmk_placed
  reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed restLen_of_pre_P_placed
  seedsLen32_of_pre_P_placed tryDecryptPlacedSpecP tryDecryptPlacedSpecQF_PTight
  tryDecryptPlacedTightSpec tryDecrypt_onPanicTight_of_afterCmk_placed
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget (
  CmkSeg4Env CmkStepEnv s4DefaultEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudget (
  aesDecrypt_433_cli dhStep_pinned_433_cli errTail_433_cli pqRecv_433_cli pqRecv_433_cli_ofEnv
  s0_433_cli s1_pinned_433_cli s2_433_cli s4_433_cli s4_433_cli_ofEnv
  s6_433_cli s7_433_cli s9_433_cli
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget (s8Env s9Env)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (s7Env vmacEvents)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlacedBudget (
  S1TightSeamPinnedFreePlaced
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ConsumeMsgKeyStatePlaced ErrTailTightSeamPlaced S0PSeamPlaced S2SeamPlaced
  S3TightSeamPinnedPlaced S4SeamPlaced S5WTSeamPlaced S6SeamPlaced S7SeamPlaced
  S8SeamPlaced S9SeamPlaced VerifyMacStatePlaced cliTryDecryptSpecPPlaced
  cliTryDecryptSpecPlaced cliTryDecryptTightSpecPlaced reaches_outcome_weaken_tight_placed
  tryDecryptRawSpecTPTightAt tryDecryptSpecTPTightAt
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  cmkLoopAdvanceEvs_nonempty
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrRecvBytesEnv SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv spqrRecvBytesEnv_nonempty
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (AesDecCtEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux (s9From6d0Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (
  DhCommitEnv dhCommitAllocEvents s3CommitDefaultEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv s3EnvOf)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (
  FromS2GenEnv FromS3GenEnv FromS4EnvsInhabited FromS4GenEnv FromS5GenEnv FromS6GenEnv
  FromS7GenEnv FromS8GenEnv SeamEnvsInhabited TrGhostCaps caps_trGhostOfCaps freeOnlyEvs_nil
  fromS2GenEnv_caps fromS2GenEnv_ne fromS4GenEnv_caps fromS4GenEnv_ne fromS5GenEnv_ne
  fromS5GenEnv_trG fromS6GenEnv_ne fromS7GenEnv_ne fromS8GenEnv_ne s1InitTrGhost
  s3AfterTrGhost seqEnv_append seqEnv_mono seqEnv_ne stdAesOpt trGhostCaps
)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget (trApplyEnv_senderSome_mem)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)

/-! ## 1. Deterministic Pointer-Free `TryDecryptCliEnv` (`TryDecryptEnvArgs → List AllocEvent → Prop`) -/

/-- Canonical zero-pointer lift of `TryDecryptEnvArgs` to `TryDecryptGhost`
    (`tryDecryptEnvArgs (envArgsToGhost a) = a` definitionally). -/
def envArgsToGhost (a : TryDecryptEnvArgs) : TryDecryptGhost where
  ret := 0#64
  ss := 0#64
  G := a.G
  st := a.st
  remA := 0#64
  rem := a.rem
  locA := 0#64
  loc := a.loc
  msgA := 0#64
  msgG := a.msgG
  msg := a.msg
  msgType := a.msgType
  cur := 0#64
  rest := a.rest

theorem tryDecryptEnvArgs_envArgsToGhost (a : TryDecryptEnvArgs) :
    tryDecryptEnvArgs (envArgsToGhost a) = a := rfl

/-- Full seam-composed `try_decrypt_with_state` CLI allocation-event envelope on
    `TryDecryptEnvArgs`, parameterized by `(fmtWriteEnv, RecvBytesEnv, fmtEnv)`.
    Uses `FreeOnlyEvs` on both `S1` outcomes (`fromSessionState = .error _` and `.ok _`), matching
    `ChainLookupS1ErrPlacedBudget.S1TightSeamPinnedFreePlaced` with zero existential witnesses. -/
def TryDecryptCliEnvOf (C : Crypto) (S : SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (a : TryDecryptEnvArgs) : List AllocEvent → Prop :=
  match Mut.exec TripleRatchet.fromSessionState a.st with
  | (.error _, _) => FreeOnlyEvs
  | (.ok tr0, st1) =>
    SeqEnv FreeOnlyEvs
      (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
        (s3DefaultEnv C) (CmkSeg4Env fmtWriteEnv) (PqRecvEnv S RecvBytesEnv fmtEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
        (envArgsToGhost a) (s1InitTrGhost a.G) tr0 st1)

/-- Default CLI `try_decrypt_with_state` allocation-event envelope at
    `(FmtWriteEnv, SpqrRecvBytesEnv, FormatInnerEnv)`. -/
abbrev TryDecryptCliEnv (C : Crypto) (S : SpqrModel) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  TryDecryptCliEnvOf C S FmtWriteEnv SpqrRecvBytesEnv FormatInnerEnv

example (C : Crypto) (S : SpqrModel) (a : TryDecryptEnvArgs)
    (herr : (Mut.exec TripleRatchet.fromSessionState a.st).1.isOk = false) :
    TryDecryptCliEnv C S a [] := by
  unfold TryDecryptCliEnv TryDecryptCliEnvOf
  rcases h : Mut.exec TripleRatchet.fromSessionState a.st with ⟨_ | _, _⟩
  · exact FreeOnlyEvs.nil
  · rw [h] at herr
    cases herr

/-! ## 2. Parametric Seam Composition & CLI Block-`433` Specializations -/

private theorem reaches_outcome_withLsCodeRoLoaded [LibsignalPlacement] {α : Type}
    {P : Program} {spec : Spec α} {z : α} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P spec z R s0 s) :
    reaches_outcome P (withLsCodeRoLoaded lsmpl spec) z R s0 s :=
  h.mono_outcome (fun _ hout => hout)

private theorem reaches_outcome_of_withLsCodeRoLoaded [LibsignalPlacement] {α : Type}
    {P : Program} {spec : Spec α} {z : α} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (withLsCodeRoLoaded lsmpl spec) z R s0 s) :
    reaches_outcome P spec z R s0 s :=
  h.mono_outcome (fun _ hout => hout)

private theorem tdp_reaches_outcome_of_panic_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨
      (cliTryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv).onPanic (x, st_init) s0 s' ∗ R) :
    reaches_outcome P (cliTryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv)
      (x, st_init) R s0 s :=
  Arm64.reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic
      (spec := cliTryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv) hpan hq)

private theorem tdp_pre_iff_placed [LibsignalPlacement] {M : AllocCostModel}
    {Q : List (BitVec 8) → Prop} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (tryDecryptPlacedSpecQF_PTight Q F0 C A lim ctl uuidTryParse S tdEnv)).pre
          (x, st_init) s0 ∗ R) :
    Q x.st.pqRatchetState ∧
      (s0.mem ⊨
        (cliTryDecryptSpecPPlaced C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗
          (F0 ∗ R)) := by
  dsimp only [withLsCodeRoLoaded, tryDecryptPlacedSpecQF_PTight, cliTryDecryptSpecPPlaced]
    at hpre ⊢
  have h1 : s0.mem ⊨ ⌜Q x.st.pqRatchetState⌝ ∗
      (((tryDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ (F0 ∗ R)) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rwa [satisfies_pure_sepConj] at h1

private theorem tdp_reaches_outcome_of_verifyMac_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    {s7Env_ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8Env_ : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env_ : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env_ s8Env_ s9Env_)
    (herr : ErrTailTightSeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv)
    (hs7 : S7SeamPlaced prog entry C A lim ctl uuidTryParse S s7Env_)
    (hs8 : S8SeamPlaced prog entry C A lim ctl uuidTryParse S s8Env_)
    (hs9 : S9SeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv s9Env_)
    {x : TryDecryptGhost} {st_init st7 : M.σ} {trG5 : TrGhost}
    {tr0 : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {ck : ChainKey} {r1 r2 : RatchetState} {mkg : MessageKeyGenerator}
    {newPqrState : List (BitVec 8)} {pqrKey : Salt} {draws : Nat}
    {R : SepProp} {s0 s7 : State}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr0.pqrState x.msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hnp5 : S.recvPanics tr0.pqrState x.msg.pqRatchet = false)
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hb7 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st7
      (FromS7GenEnv C uuidTryParse (stdAesOpt C) s7Env_ s8Env_ s9Env_
        x trG5 { tr0 with ratchet := r2 } st1 (mkg.generateKeys C.F pqrKey) newPqrState))
    (hs7_state : VerifyMacStatePlaced entry A lim st7 ctl x trG5 { tr0 with ratchet := r2 } st1
      (mkg.generateKeys C.F pqrKey) newPqrState draws R s0 s7)
    (hL7 : prog.CodeLoaded s7.mem) :
    reaches_outcome prog (cliTryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv)
      (x, st_init) R s0 s7 := by
  let mks := mkg.generateKeys C.F pqrKey
  cases hmac : x.msg.verifyMacWithAddresses C.F
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
  | false =>
    unfold FromS7GenEnv at hb7
    dsimp only at hb7
    rw [hmac] at hb7
    simp only [Bool.false_eq_true, ↓reduceIte] at hb7
    have hfits7 : FitsEnv M lim st7
        (s7Env_ x { tr0 with ratchet := r2 } mks newPqrState) :=
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
      exact Arm64.reaches_outcome_steps hsteps7'
        (reaches_outcome_weaken_tight_placed
          (herr x st_init (M.stepEvents evs7 st7) trG5 { tr0 with ratchet := r2 } st1
            (.invalidMessage x.msgType .macFailed) R s0 s7' hne_e hm1 hm2 hberr herr_st))
    · exact tdp_reaches_outcome_of_panic_placed hsteps7' hpan hq
  | true =>
    unfold FromS7GenEnv at hb7
    dsimp only at hb7
    rw [hmac] at hb7
    simp only [↓reduceIte] at hb7
    have hfits7 : FitsEnv M lim st7
        (s7Env_ x { tr0 with ratchet := r2 } mks newPqrState) :=
      hb7.fitsSeg (fun _ _ => seqEnv_append)
        (fromS8GenEnv_ne hne x trG5 { tr0 with ratchet := r2 } st1 mks newPqrState)
    have hs7_step := hs7 x st7 trG5 { tr0 with ratchet := r2 }
      st1 mks newPqrState draws R s0 s7 hfits7 hs7_state hL7
    dsimp only at hs7_step
    rw [hmac] at hs7_step
    simp only [↓reduceIte] at hs7_step
    rcases hs7_step with ⟨s8, hsteps8, ⟨evs7, hevs7, hs8_state⟩ | ⟨hpan, hq⟩⟩
    · refine Arm64.reaches_outcome_steps hsteps8 ?_
      have hL8 := hsteps8.codeLoaded hL7
      set st8 := M.stepEvents evs7 st7
      have hb8 := hb7.step (fun _ _ => seqEnv_append) hevs7
      unfold FromS8GenEnv stdAesOpt at hb8
      cases haes : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | none =>
        rw [haes] at hb8
        have hfits8 : FitsEnv M lim st8 (s8Env_ x mks newPqrState) :=
          hb8.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
        have hs8_step := hs8 x st8 trG5 { tr0 with ratchet := r2 }
          st1 mks newPqrState draws R s0 s8 hfits8 hs8_state hL8
        rw [haes] at hs8_step
        have hmodel := model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
        have hm1 : (x.model C S uuidTryParse).1 =
            .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne_e : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic := nofun
        rcases hs8_step with ⟨s8', hsteps8', ⟨evs8, hevs8, herr_st⟩ | ⟨hpan, hq⟩⟩
        · subst hdraws
          have hberr := hb8.step (fun _ _ => seqEnv_append) hevs8
          exact Arm64.reaches_outcome_steps hsteps8'
            (reaches_outcome_weaken_tight_placed
              (herr x st_init (M.stepEvents evs8 st8) trG5 { tr0 with ratchet := r2 } st1
                (.invalidMessage x.msgType .badCiphertext) R s0 s8'
                hne_e hm1 hm2 hberr herr_st))
        · exact tdp_reaches_outcome_of_panic_placed hsteps8' hpan hq
      | some pt =>
        rw [haes] at hb8
        have hfits8 : FitsEnv M lim st8 (s8Env_ x mks newPqrState) :=
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
          exact Arm64.reaches_outcome_steps hsteps9
            (hs9 x st_init (M.stepEvents evs8 st8) trG5 { tr0 with ratchet := r2 }
              st1 newPqrState pt R s0 s9 hm1 hm2 hb9 hs9_state)
        · exact tdp_reaches_outcome_of_panic_placed hsteps9 hpan hq
    · exact tdp_reaches_outcome_of_panic_placed hsteps8 hpan hq

private theorem tdp_reaches_outcome_of_s4_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    {s7Env_ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8Env_ : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env_ : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env_ s8Env_ s9Env_)
    (herr : ErrTailTightSeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv)
    (hs4 : S4SeamPlaced prog entry C A lim ctl uuidTryParse S s4Env)
    (hs5 : S5WTSeamPlaced prog entry F0 C A lim ctl uuidTryParse S s5Env)
    (hs6 : S6SeamPlaced prog entry C A lim ctl s6Env)
    (hs7 : S7SeamPlaced prog entry C A lim ctl uuidTryParse S s7Env_)
    (hs8 : S8SeamPlaced prog entry C A lim ctl uuidTryParse S s8Env_)
    (hs9 : S9SeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv s9Env_)
    {x : TryDecryptGhost} {st_init st4 : M.σ} {trG : TrGhost}
    {tr0 : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {ck : ChainKey} {r1 : RatchetState} {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hstk : rootStack ≤ s0.sp.toNat)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hb4 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st4
      (FromS4GenEnv C uuidTryParse S (stdAesOpt C) s4Env s5Env s6Env s7Env_ s8Env_ s9Env_
        x trG { tr0 with ratchet := r1 } st1 ck))
    (hs4_state : ConsumeMsgKeyStatePlaced entry A lim st4 ctl x trG
      { tr0 with ratchet := r1 } st1 ck draws (F0 ∗ R) s0 s4)
    (hL4 : prog.CodeLoaded s4.mem) :
    reaches_outcome prog
      (tryDecryptPlacedSpecQF_PTight (·.length < 2 ^ 32) F0 C A lim ctl uuidTryParse S tdEnv)
      (x, st_init) R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := fromSessionState_ok_inv htr
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    have hb4' := hb4
    unfold FromS4GenEnv at hb4'
    dsimp only at hb4'
    rw [hcmk] at hb4'
    cases cmkRes with
    | error e =>
      have hfits4 : FitsEnv M lim st4 (s4Env x trG { tr0 with ratchet := r1 } ck) :=
        hb4'.fitsSeg (fun _ _ => seqEnv_append) ⟨[], freeOnlyEvs_nil⟩
      have hs4_step := hs4 x st4 trG { tr0 with ratchet := r1 } st1 ck draws (F0 ∗ R) s0 s4
        hfits4 hs4_state hL4
      dsimp only at hs4_step
      rw [hcmk] at hs4_step
      have hmodel := model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne_e, evs4, trG', hevs4, herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        have hberr := hb4'.step (fun _ _ => seqEnv_append) hevs4
        exact Arm64.reaches_outcome_steps hsteps4
          (reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed
            (reaches_outcome_of_withLsCodeRoLoaded
              (herr x st_init (M.stepEvents evs4 st4) trG' { tr0 with ratchet := r2 } st1 e
                (F0 ∗ R) s0 s4' hne_e hm1 hm2 hberr herr_st)))
      · exact reaches_outcome_of_panicQF_PTight_placed hsteps4 hpan
          (onPanicTight_drop_frame (onPanicTight_of_cmk_panic hm1 hp hmem))
    | ok mkg =>
      have hne5 : ∃ evs_rem,
          FromS5GenEnv C uuidTryParse S (stdAesOpt C) s5Env s6Env s7Env_ s8Env_ s9Env_
            x trG { tr0 with ratchet := r2 } st1 mkg evs_rem :=
        fromS5GenEnv_ne (C := C) (parse := uuidTryParse) (S := S) (aesOpt := stdAesOpt C)
          hne x trG { tr0 with ratchet := r2 } st1 mkg
      have hfits4 : FitsEnv M lim st4 (s4Env x trG { tr0 with ratchet := r1 } ck) :=
        hb4'.fitsSeg (fun _ _ => seqEnv_append) hne5
      have hs4_step := hs4 x st4 trG { tr0 with ratchet := r1 } st1 ck draws (F0 ∗ R) s0 s4
        hfits4 hs4_state hL4
      dsimp only at hs4_step
      rw [hcmk] at hs4_step
      rcases hs4_step with ⟨s5, hsteps5, ⟨evs4, trG5, hevs4, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine Arm64.reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
        set st5 := M.stepEvents evs4 st4
        have hb5 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st5
            (FromS5GenEnv C uuidTryParse S (stdAesOpt C) s5Env s6Env s7Env_ s8Env_ s9Env_
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
            hQ hstk hfits5 hpqr0 hs5_state hL5
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
            exact Arm64.reaches_outcome_steps hsteps5'
              (reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed
                (reaches_outcome_of_withLsCodeRoLoaded
                  (herr x st_init (M.stepEvents evs5 st5) trG5 { tr0 with ratchet := r2 } st1 e
                    (F0 ∗ R) s0 s5' hne_e hm1 hm2 hberr herr_st)))
          · exact reaches_outcome_of_panicQF_PTight_placed hsteps5' hpan
              (tryDecrypt_onPanicTight_of_afterCmk_placed
                (A := A) (lim := lim) (ctl := ctl) (tdEnv := tdEnv) (st := st_init)
                htr herc hcmk hq)
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          unfold FromS5GenEnv at hb5
          dsimp only at hb5
          rw [hspqr] at hb5
          have hfits5 : FitsEnv M lim st5 (s5Env x { tr0 with ratchet := r2 }) :=
            hb5.fitsSeg (fun _ _ => seqEnv_append)
              (fromS6GenEnv_ne hne x trG5 { tr0 with ratchet := r2 } st1 mkg newPqrState pqrKey)
          have hs5_step := hs5 x st5 trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
            hQ hstk hfits5 hpqr0 hs5_state hL5
          dsimp only at hs5_step
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s6, hsteps6, ⟨evs5, hevs5, hs6_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · refine Arm64.reaches_outcome_steps hsteps6 ?_
            have hL6 := hsteps6.codeLoaded hL5
            set st6 := M.stepEvents evs5 st5
            have hb6 := hb5.step (fun _ _ => seqEnv_append) hevs5
            unfold FromS6GenEnv at hb6
            let mks := mkg.generateKeys C.F pqrKey
            have hfits6 : FitsEnv M lim st6 (s6Env mkg) :=
              hb6.fitsSeg (fun _ _ => seqEnv_append)
                (fromS7GenEnv_ne hne x trG5 { tr0 with ratchet := r2 } st1 mks newPqrState)
            rcases hs6 x st6 trG5 { tr0 with ratchet := r2 } st1 mkg
                newPqrState pqrKey draws (F0 ∗ R) s0 s6 hseed32 hfits6 hs6_state hL6 with
              ⟨s7, hsteps7, ⟨_, _, evs6, hevs6, hs7_state⟩ | ⟨_, hfalse⟩⟩
            swap; · exact hfalse.elim
            refine Arm64.reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL6
            have hb7 := hb6.step (fun _ _ => seqEnv_append) hevs6
            exact reaches_outcome_tryDecryptSpecQF_PTight_of_afterCmk_placed htr herc hcmk
              (reaches_outcome_of_withLsCodeRoLoaded
                (tdp_reaches_outcome_of_verifyMac_placed hne herr hs7 hs8 hs9
                  htr herc hcmk hspqr hnp5 hdraws hb7 hs7_state hL7))
          · exact reaches_outcome_of_panicQF_PTight_placed hsteps6 hpan
              (tryDecrypt_onPanicTight_of_afterCmk_placed
                (A := A) (lim := lim) (ctl := ctl) (tdEnv := tdEnv) (st := st_init)
                htr herc hcmk hq)
      · exact reaches_outcome_of_panicQF_PTight_placed hsteps5 hpan
          (onPanicTight_drop_frame
            (tryDecrypt_onPanicTight_of_afterCmk_placed
              (A := A) (lim := lim) (ctl := ctl) (tdEnv := tdEnv) (st := st_init)
              htr herc hcmk hq))

/-- Tight-panic `try_decrypt_with_state` composition over any `[LibsignalPlacement]` block program
    `(prog, entry)` from the 11 budget-threaded segment seams (`S0..S9` + `ErrTail`). -/
theorem tryDecrypt_placed_ok_of_seams [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    {s7Env_ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8Env_ : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env_ : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hs1Err_td : ∀ x evs,
      (Mut.exec TripleRatchet.fromSessionState x.st).1.isOk = false →
      FreeOnlyEvs evs → tdEnv (tryDecryptEnvArgs x) evs)
    (hs1Ok_td : ∀ x tr0 st1 evs,
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1) →
      SeqEnv (s1OkEnv x)
        (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
          s3Env s4Env s5Env s6Env s7Env_ s8Env_ s9Env_
          x (s1InitTrGhost x.G) tr0 st1) evs →
      tdEnv (tryDecryptEnvArgs x) evs)
    (hne : SeamEnvsInhabited s3Env s4Env s5Env s6Env s7Env_ s8Env_ s9Env_)
    (hs0 : S0PSeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv)
    (hs1 : S1TightSeamPinnedFreePlaced prog entry C A lim ctl uuidTryParse S tdEnv s1OkEnv)
    (hs2 : S2SeamPlaced prog entry A lim ctl)
    (hs3 : S3TightSeamPinnedPlaced prog entry C A lim ctl uuidTryParse S s3Env)
    (hs4 : S4SeamPlaced prog entry C A lim ctl uuidTryParse S s4Env)
    (hs5 : S5WTSeamPlaced prog entry tokenInitPlacedAt C A lim ctl uuidTryParse S s5Env)
    (hs6 : S6SeamPlaced prog entry C A lim ctl s6Env)
    (hs7 : S7SeamPlaced prog entry C A lim ctl uuidTryParse S s7Env_)
    (hs8 : S8SeamPlaced prog entry C A lim ctl uuidTryParse S s8Env_)
    (hs9 : S9SeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv s9Env_)
    (herr : ErrTailTightSeamPlaced prog entry C A lim ctl uuidTryParse S tdEnv) :
    subroutine_ok prog entry
      (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre hsp
  apply reaches_outcome_withLsCodeRoLoaded
  rcases tdp_pre_iff_placed hpre with ⟨hQ, hpreP⟩
  have hpre_raw : s0.mem ⊨
      (tryDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗
        (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ (tokenInitPlacedAt ∗ R)) := by
    dsimp only [cliTryDecryptSpecPPlaced, withLsCodeRoLoaded] at hpreP
    rwa [sepConj_assoc] at hpreP
  have hfits0 : FitsEnv M lim st_init (tdEnv (tryDecryptEnvArgs x)) :=
    fitsEnv_of_pre_P_placed hpre_raw
  obtain ⟨hseeds, hchains, hstk⟩ := seedsLen32_of_pre_P_placed hpre_raw
  have hrest : x.rest.length < 2 ^ 63 := restLen_of_pre_P_placed hpre_raw
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  rcases hs0 x st_init (tokenInitPlacedAt ∗ R) s0 hpc hrun hsp hpreP hL with
    ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hfalse⟩⟩
  swap; · exact hfalse.elim
  refine Arm64.reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 x st_init st_init (tokenInitPlacedAt ∗ R) s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error _ =>
      have hnotOk : (Mut.exec TripleRatchet.fromSessionState x.st).1.isOk = false := by
        rw [htr]; rfl
      have hb_err : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st_init FreeOnlyEvs :=
        (SeamBudget.init hfits0).weaken (hs1Err_td x · hnotOk)
      exact reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed
        (reaches_outcome_of_withLsCodeRoLoaded (hs1_step hb_err))
    | ok tr0 =>
      have hb0 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st_init
          (SeqEnv (s1OkEnv x)
            (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
              s3Env s4Env s5Env s6Env s7Env_ s8Env_ s9Env_
              x (s1InitTrGhost x.G) tr0 st1)) :=
        (SeamBudget.init hfits0).weaken (hs1Ok_td x tr0 st1 · htr)
      have hne2 : ∃ evs_rem,
          FromS2GenEnv C uuidTryParse S (stdAesOpt C)
            s3Env s4Env s5Env s6Env s7Env_ s8Env_ s9Env_
            x (s1InitTrGhost x.G) tr0 st1 evs_rem :=
        fromS2GenEnv_ne (C := C) (parse := uuidTryParse) (S := S) (aesOpt := stdAesOpt C)
          hne x (s1InitTrGhost x.G) tr0 st1
      have hfits1 : FitsEnv M lim st_init (s1OkEnv x) :=
        hb0.fitsSeg (fun _ _ => seqEnv_append) hne2
      rcases hs1_step hfits1 with ⟨s2, hsteps2, evs1, trG2, hevs1, hcaps2, hs2_state⟩
      refine Arm64.reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      set st2 := M.stepEvents evs1 st_init
      have hcaps2' : trGhostCaps trG2 = trGhostCaps (s1InitTrGhost x.G) :=
        hcaps2.trans (caps_trGhostOfCaps _).symm
      have hb2 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st2
          (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
            s3Env s4Env s5Env s6Env s7Env_ s8Env_ s9Env_
            x trG2 tr0 st1) :=
        (hb0.step (fun _ _ => seqEnv_append) hevs1).weaken
          (fun _ he => fromS2GenEnv_caps hne hcaps2' he)
      have hs2_step := hs2 x st2 trG2 tr0 st1 (tokenInitPlacedAt ∗ R) s0 s2 hs2_state hL2
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
          subst he; decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        exact Arm64.reaches_outcome_steps hsteps2'
          (reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed
            (reaches_outcome_of_withLsCodeRoLoaded
              (herr x st_init st2 trG2 tr0 st1 e (tokenInitPlacedAt ∗ R) s0 s2'
                hne_e hm1 hm2 hb2 herr_st)))
      | ok optCk =>
        cases optCk with
        | some ck =>
          unfold FromS2GenEnv at hb2
          rw [hf] at hs2_step hb2
          rcases hs2_step hL2 with ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Arm64.reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (decryptDraws_of_find_some x.rest htr hf).symm
          have htr0_eta :
              ({ tr0 with ratchet := tr0.ratchet } : TripleRatchet (List (BitVec 8))) = tr0 := by
            cases tr0; rfl
          have hs4_state' : ConsumeMsgKeyStatePlaced entry A lim st2 ctl x trG2
              { tr0 with ratchet := tr0.ratchet } st1 ck 0 (tokenInitPlacedAt ∗ R) s0 s4 := by
            rw [htr0_eta]; exact hs4_state
          have hb4 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st2
              (FromS4GenEnv C uuidTryParse S (stdAesOpt C)
                s4Env s5Env s6Env s7Env_ s8Env_ s9Env_
                x trG2 { tr0 with ratchet := tr0.ratchet } st1 ck) := by
            rw [htr0_eta]; exact hb2
          exact tdp_reaches_outcome_of_s4_placed hne.toFromS4EnvsInhabited
            herr hs4 hs5 hs6 hs7 hs8 hs9 hseeds hQ hstk htr herc hdraws hb4 hs4_state' hL4
        | none =>
          unfold FromS2GenEnv at hb2
          rw [hf] at hs2_step hb2
          rcases hs2_step hL2 with ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Arm64.reaches_outcome_steps hsteps3 ?_
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
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne_e : e ≠ .panic := dhRatchetStep_error_ne_panic hdh
              rcases hs3 x st2 trG2 tr0 st1 (tokenInitPlacedAt ∗ R) s0 s3
                  htr hf htr_chains hstk hrest hfits3 hs3_state hL3 with
                ⟨s3', hsteps3', hdh_out | ⟨hpan, hq⟩⟩
              · rw [hdh] at hdh_out
                rcases hdh_out with ⟨evs3, trG3, r1', hevs3, herr_st⟩
                have hberr := hb2.step (fun _ _ => seqEnv_append) hevs3
                exact Arm64.reaches_outcome_steps hsteps3'
                  (reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed
                    (reaches_outcome_of_withLsCodeRoLoaded
                      (herr x st_init (M.stepEvents evs3 st2) trG3 { tr0 with ratchet := r1' }
                        st1 e (tokenInitPlacedAt ∗ R) s0 s3' hne_e hm1 hm2 hberr herr_st)))
              · exact reaches_outcome_of_panicQF_PTight_placed hsteps3' hpan
                  (onPanicTight_drop_frame hq)
            | ok ck =>
              have hne4 : ∃ evs_rem,
                  FromS4GenEnv C uuidTryParse S (stdAesOpt C)
                    s4Env s5Env s6Env s7Env_ s8Env_ s9Env_
                    x (s3AfterTrGhost trG2 tr0.ratchet.receiverChains.length)
                    { tr0 with ratchet := r1 } st1 ck evs_rem :=
                fromS4GenEnv_ne (C := C) (parse := uuidTryParse) (S := S) (aesOpt := stdAesOpt C)
                  hne.toFromS4EnvsInhabited
                  x (s3AfterTrGhost trG2 tr0.ratchet.receiverChains.length)
                  { tr0 with ratchet := r1 } st1 ck
              have hfits3 : FitsEnv M lim st2 (s3Env x trG2 tr0) :=
                hb2.fitsSeg (fun _ _ => seqEnv_append) hne4
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3 x st2 trG2 tr0 st1 (tokenInitPlacedAt ∗ R) s0 s3
                  htr hf htr_chains hstk hrest hfits3 hs3_state hL3 with
                ⟨s4, hsteps4, hdh_out | ⟨hpan, hq⟩⟩
              · rw [hdh] at hdh_out
                rcases hdh_out with ⟨evs3, trG4, hevs3, hcaps4, hs4_state⟩
                refine Arm64.reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                have hcaps4' :
                    trGhostCaps trG4 =
                      trGhostCaps (s3AfterTrGhost trG2 tr0.ratchet.receiverChains.length) :=
                  hcaps4.trans (caps_trGhostOfCaps _).symm
                have hb4 : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init
                    (M.stepEvents evs3 st2)
                    (FromS4GenEnv C uuidTryParse S (stdAesOpt C)
                      s4Env s5Env s6Env s7Env_ s8Env_ s9Env_
                      x trG4 { tr0 with ratchet := r1 } st1 ck) :=
                  (hb2.step (fun _ _ => seqEnv_append) hevs3).weaken
                    (fun _ he => fromS4GenEnv_caps hne.toFromS4EnvsInhabited hcaps4' he)
                exact tdp_reaches_outcome_of_s4_placed hne.toFromS4EnvsInhabited
                  herr hs4 hs5 hs6 hs7 hs8 hs9 hseeds hQ hstk htr herc rfl hb4 hs4_state hL4
              · exact reaches_outcome_of_panicQF_PTight_placed hsteps4 hpan
                  (onPanicTight_drop_frame hq)

private theorem cliSeamEnvs_inhabited (C : Crypto) (S : SpqrModel)
    {fmtWriteEnv : List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs) :
    SeamEnvsInhabited
      (s3DefaultEnv C)
      (CmkSeg4Env fmtWriteEnv)
      (PqRecvEnv S RecvBytesEnv fmtEnv)
      s6FreeOnlyEnv
      (s7Env C.F uuidTryParse)
      s8Env
      s9Env where
  s4 x trG tr ck := by
    refine seqEnv_ne hFmtWrite_ne (seqEnv_ne ?_ ⟨[], freeOnlyEvs_nil⟩)
    unfold CmkStepEnv
    by_cases h1 : x.msg.counter < ck.index
    · simp only [h1, ↓reduceIte]; exact ⟨[], freeOnlyEvs_nil⟩
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (x.msg.counter - ck.index).toNat ≤ tr.ratchet.maxForwardJumps
      · simp only [h2, ↓reduceIte]
        cases tr.ratchet.findReceiverChainIndex x.msg.senderRatchetKey with
        | none =>
          by_cases h3 : ck.index < x.msg.counter
          · simp only [h3, ↓reduceIte]; exact ⟨[], Or.inl rfl⟩
          · simp only [h3, ↓reduceIte]; exact ⟨[], rfl⟩
        | some _ =>
          exact cmkLoopAdvanceEvs_nonempty _ _ _ _
      · simp only [h2, ↓reduceIte]; exact ⟨rustAllocEvents 36 1, rfl⟩
  s5 x tr := by
    unfold PqRecvEnv
    cases S.recv tr.pqrState x.msg.pqRatchet with
    | ok _ => exact hRecv_ne _ _
    | error _ => exact seqEnv_ne (seqEnv_ne (hRecv_ne _ _) hFmtInner_ne) ⟨[], freeOnlyEvs_nil⟩
  s6 _ := ⟨[], freeOnlyEvs_nil⟩
  s7 x tr mks _ :=
    ⟨vmacEvents C.F uuidTryParse x tr mks ++ rustAllocEvents 23 1,
      Or.inl (seqEnv_append rfl rfl)⟩
  s8 x _ _ := by
    unfold s8Env
    refine seqEnv_ne ?_ ⟨[], freeOnlyEvs_nil⟩
    unfold AesDecCtEnv
    by_cases h : x.msg.ciphertext.length = 0 ∨ x.msg.ciphertext.length % 16 ≠ 0
    · simp only [h, ↓reduceIte]; exact ⟨[], rfl⟩
    · simp only [h, ↓reduceIte]; exact ⟨_, Or.inl rfl⟩
  s9 _ _ _ _ _ :=
    let e_tr := rustAllocEvents 32 1 ++ (rustAllocEvents 33 1 ++
      (rustAllocEvents 33 1 ++ (rustAllocEvents 32 1 ++
        (rustAllocEvents 32 1 ++ rustAllocEvents 32 1))))
    ⟨e_tr, Or.inr ⟨[], e_tr, rfl, freeOnlyEvs_nil,
      Or.inr ⟨e_tr, [], (List.append_nil e_tr).symm, trApplyEnv_senderSome_mem, freeOnlyEvs_nil⟩⟩⟩
  s4_caps x trG₁ trG₂ tr ck evs hcaps h := by
    have hmk : List.map ChainGhost.mkCap trG₁.ratchet.chains =
        List.map ChainGhost.mkCap trG₂.ratchet.chains :=
      congrArg TrGhostCaps.mkCaps hcaps
    have hci : ∀ ci,
        trG₁.ratchet.chains[ci]?.map ChainGhost.mkCap =
          trG₂.ratchet.chains[ci]?.map ChainGhost.mkCap := fun ci => by
      rw [← List.getElem?_map, ← List.getElem?_map, hmk]
    have hstep : CmkStepEnv x.msg.counter x.msg.senderRatchetKey trG₁ tr.ratchet ck =
        CmkStepEnv x.msg.counter x.msg.senderRatchetKey trG₂ tr.ratchet ck := by
      funext e
      unfold CmkStepEnv
      cases tr.ratchet.findReceiverChainIndex x.msg.senderRatchetKey with
      | none => rfl
      | some ci => simp only [hci ci]
    unfold CmkSeg4Env at h ⊢
    rwa [← hstep]
  s9_trG _ _ _ _ _ _ _ h := h
  s3 x trG tr := by
    unfold s3DefaultEnv s3EnvOf
    cases tr.ratchet.senderChain with
    | none => exact ⟨[], rfl⟩
    | some sc =>
      dsimp only
      cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
      | error _ => exact ⟨_, rfl⟩
      | ok p1 =>
        rcases p1 with ⟨rk1, _⟩
        dsimp only
        cases rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error _ => exact seqEnv_ne ⟨_, rfl⟩ ⟨_, rfl⟩
        | ok _ =>
          exact seqEnv_ne ⟨_, rfl⟩ (seqEnv_ne ⟨_, rfl⟩ ⟨_, Or.inl rfl⟩)
  s3_caps x trG₁ trG₂ tr evs hcaps h := by
    have hcc : trG₁.ratchet.chainsCap = trG₂.ratchet.chainsCap :=
      congrArg TrGhostCaps.chainsCap hcaps
    have hs3_eq : s3DefaultEnv C x trG₁ tr = s3DefaultEnv C x trG₂ tr := by
      funext e
      unfold s3DefaultEnv s3EnvOf s3CommitDefaultEnv
      simp only [hcc]
    exact hs3_eq ▸ h

private theorem fromS2_envArgsToGhost_eq (C : Crypto) (S : SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost)
    (tr0 : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8))) :
    FromS2GenEnv C uuidTryParse S (stdAesOpt C)
      (s3DefaultEnv C) (CmkSeg4Env fmtWriteEnv) (PqRecvEnv S RecvBytesEnv fmtEnv)
      s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
      (envArgsToGhost (tryDecryptEnvArgs x))
      (s1InitTrGhost (tryDecryptEnvArgs x).G) tr0 st1 =
    FromS2GenEnv C uuidTryParse S (stdAesOpt C)
      (s3DefaultEnv C) (CmkSeg4Env fmtWriteEnv) (PqRecvEnv S RecvBytesEnv fmtEnv)
      s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
      x (s1InitTrGhost x.G) tr0 st1 := rfl

/-- Envelope-monotonic CLI Block-`433` `tryDecryptSpecTPTightAt` for any `tdEnv` containing
    `TryDecryptCliEnvOf`. -/
theorem tryDecryptV1_placed_ok_PTight_cli_of_tdEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv a evs →
      tdEnv a evs) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 434)
      (tryDecryptSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv) := by
  refine tryDecrypt_placed_ok_of_seams
    (s1OkEnv := fun _ => FreeOnlyEvs)
    (fun x evs herr hfree => htd (tryDecryptEnvArgs x) evs (by
      unfold TryDecryptCliEnvOf
      change (match Mut.exec TripleRatchet.fromSessionState x.st with
        | (.error _, _) => FreeOnlyEvs
        | (.ok tr0, st1) => _) evs
      rcases h : Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | _, _⟩
      · exact hfree
      · rw [h] at herr; cases herr))
    (fun x tr0 st1 evs htr hseq => htd (tryDecryptEnvArgs x) evs (by
      unfold TryDecryptCliEnvOf
      change (match Mut.exec TripleRatchet.fromSessionState x.st with
        | (.error _, _) => FreeOnlyEvs
        | (.ok tr0, st1) => _) evs
      rw [htr]
      dsimp only
      rw [fromS2_envArgsToGhost_eq]
      exact hseq))
    (cliSeamEnvs_inhabited W.C (spqrV1 W.C.F W.Q.K) hRecv_ne hFmtWrite_ne hFmtInner_ne)
    (s0_433_cli mmpl g W ctl (spqrV1 W.C.F W.Q.K) tdEnv)
    (s1_pinned_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) tdEnv)
    (s2_433_cli mmpl g W ctl)
    (dhStep_pinned_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (s4_433_cli_ofEnv mmpl g W hG hFmtWrite ctl (spqrV1 W.C.F W.Q.K))
    (pqRecv_433_cli_ofEnv mmpl g W hG hSpqr hFmtInner ctl)
    (s6_433_cli mmpl g W hG ctl)
    (s7_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (aesDecrypt_433_cli mmpl g W hG hAesDec ctl (spqrV1 W.C.F W.Q.K))
    (s9_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) tdEnv)
    (errTail_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) tdEnv)

/-- Envelope-parametric CLI Block-`433` `tryDecryptSpecTPTightAt` at `TryDecryptCliEnvOf`. -/
theorem tryDecryptV1_placed_ok_PTight_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 434)
      (tryDecryptSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
        (TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv)) :=
  tryDecryptV1_placed_ok_PTight_cli_of_tdEnv mmpl g W ctl hG hAesDec hSpqr hFmtWrite hFmtInner
    hRecv_ne hFmtWrite_ne hFmtInner_ne (fun _ _ h => h)

/-- Concrete placed CLI `subroutine_ok` for `tryDecryptSpecTPTightAt` on Block `433` at
    `S := spqrV1 W.C.F W.Q.K` and `tdEnv := TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)`. -/
theorem tryDecryptV1_placed_ok_PTight_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 434)
      (tryDecryptSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
        (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))) :=
  tryDecrypt_placed_ok_of_seams
    (s1OkEnv := fun _ => FreeOnlyEvs)
    (fun x evs herr hfree => by
      unfold TryDecryptCliEnv TryDecryptCliEnvOf
      change (match Mut.exec TripleRatchet.fromSessionState x.st with
        | (.error _, _) => FreeOnlyEvs
        | (.ok tr0, st1) => _) evs
      rcases h : Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | _, _⟩
      · exact hfree
      · rw [h] at herr; cases herr)
    (fun x tr0 st1 evs htr hseq => by
      unfold TryDecryptCliEnv TryDecryptCliEnvOf
      change (match Mut.exec TripleRatchet.fromSessionState x.st with
        | (.error _, _) => FreeOnlyEvs
        | (.ok tr0, st1) => _) evs
      rw [htr]
      dsimp only
      rw [fromS2_envArgsToGhost_eq]
      exact hseq)
    (cliSeamEnvs_inhabited (fmtWriteEnv := FmtWriteEnv) (fmtEnv := FormatInnerEnv)
      W.C (spqrV1 W.C.F W.Q.K)
      spqrRecvBytesEnv_nonempty ⟨[], rfl⟩ ⟨[], rfl⟩)
    (s0_433_cli mmpl g W ctl (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))
    (s1_pinned_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K)
      (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))
    (s2_433_cli mmpl g W ctl)
    (dhStep_pinned_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (s4_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (pqRecv_433_cli mmpl g W hG hSpqr ctl)
    (s6_433_cli mmpl g W hG ctl)
    (s7_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (aesDecrypt_433_cli mmpl g W hG hAesDec ctl (spqrV1 W.C.F W.Q.K))
    (s9_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))
    (errTail_433_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget
