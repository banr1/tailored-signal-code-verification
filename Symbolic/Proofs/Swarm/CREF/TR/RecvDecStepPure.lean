/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Branch Dispatcher for Whisper Receive Decrypt Step

Case-splits a successful `pureEvalRecvWireWithCoinsW` whisper receive call into the cached
skipped-key, existing-chain, and DH-ratchet branches over the composed model.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (messageVersion)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E
open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin (Role evalOpen inMemAnswers)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (AesW messageDecryptSignalW)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open Symbolic.Swarm.TRREF.GrowthRecordPure (pureSpqr)
open Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval (pureDrawsCoins pureDrawsCoins_false_of_found pureDrawsCoins_true_of_ratchet pureSerializeRole pureEvalRecvWireWithCoinsW)

private theorem tryFrom_preKyber_le_pure {b : List (BitVec 8)} {m : CryptoGames.LibsignalSession.SignalMessage}
    (h : CryptoGames.LibsignalSession.SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec b = .ok m) :
    CryptoGames.LibsignalSession.preKyberVersion ≤ m.messageVersion := by
  unfold CryptoGames.LibsignalSession.SignalMessage.tryFrom at h
  dsimp only at h
  generalize hv : b.headD 0 >>> 4 = ver at h
  generalize hd : CryptoVerification.LibsignalProtoCodec.protoSignalCodec.decode ((b.take (b.length - CryptoGames.LibsignalSession.macLength)).drop 1) = od at h
  by_cases h1 : b.length < CryptoGames.LibsignalSession.macLength + 1
  · simp only [h1, ↓reduceIte] at h; cases h
  by_cases h2 : ver < CryptoGames.LibsignalSession.preKyberVersion
  · simp only [h1, h2, ↓reduceIte] at h; cases h
  by_cases h3 : CryptoGames.LibsignalSession.currentVersion < ver
  · simp only [h1, h2, h3, ↓reduceIte] at h; cases h
  simp only [h1, h2, h3, ↓reduceIte] at h
  cases od with
  | none => simp at h
  | some p =>
    cases hrk : p.ratchetKey with
    | none => simp [hrk] at h
    | some rk =>
      cases hk : CryptoGames.LibsignalSession.PublicKey.deserialize rk with
      | error e => simp [hrk, hk, bind, Except.bind] at h
      | ok k =>
        cases hc : p.counter with
        | none => simp [hrk, hk, hc, bind, Except.bind] at h
        | some c =>
          cases hct : p.ciphertext with
          | none => simp [hrk, hk, hc, hct, bind, Except.bind] at h
          | some ct =>
            simp [hrk, hk, hc, hct] at h
            subst h
            exact BitVec.not_lt.mp h2

private theorem msgVersion_sessionVersion_of_version_pure {b : List (BitVec 8)} {m : CryptoGames.LibsignalSession.SignalMessage}
    {st : CryptoGames.LibsignalSession.SessionState (List (BitVec 8))}
    (hparse : CryptoGames.LibsignalSession.SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec b = .ok m)
    (hv : m.messageVersion.toNat = st.version.toNat) :
    m.messageVersion.toNat = st.sessionVersion.toNat := by
  have hge := BitVec.le_def.mp (tryFrom_preKyber_le_pure hparse)
  have h3 : (CryptoGames.LibsignalSession.preKyberVersion).toNat = 3 := rfl
  unfold CryptoGames.LibsignalSession.SessionState.version at hv
  split at hv
  · exfalso
    have h2 : (2 : BitVec 32).toNat = 2 := rfl
    rw [h2] at hv
    omega
  · exact hv

abbrev recvWireMissFact (C : Crypto) (W : AesW) (S : SpqrModel) (g : RecvWireGhost) : Prop :=
  ∀ r, pureEvalRecvWireWithCoinsW C W S g 0#256 = some r →
    ∀ body msg, g.wireBytes = 2#8 :: body →
      SignalMessage.tryFrom protoSignalCodec body = .ok msg →
      msg.messageVersion.toNat = g.sess.state.sessionVersion.toNat →
      pureDrawsCoins C g.sess.state msg.senderRatchetKey = false

/-- Splits a successful whisper evaluation `pureEvalRecvWireWithCoinsW` into its three mutually
exclusive branches (`Skipped`, `NoRatchet`, and `RatchetDH`), pairing the randomness draw
witness with the `RatchetDH` case. -/
theorem evalRecvWireWithCoinsW_branch_cases_of_draw
    (interpretation : ExternInterpretation)
    (body : HwBytes) (mid : List MachineEvent)
    (r : StateAndMessage) (g_rw : RecvWireGhost) (coins : BitVec 256)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hmid_cases :
      (coins = 0#256 ∧ mid = [] ∧
          recvWireMissFact (cryptoOf' interpretation)
            (Proofs.libsignal.SR.interpW interpretation)
            (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw) ∨
        (∃ rngBytes : HwBytes,
          mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧ coins = Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes) ∧
          (∀ msg, SignalMessage.tryFrom protoSignalCodec body = .ok msg →
            pureDrawsCoins (cryptoOf' interpretation) g_rw.sess.state msg.senderRatchetKey = true)))
    (heval :
      pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw coins =
        some (r.state, r.message)) :
    ∃ (m : SignalMessage) (newPqrState : HwBytes) (pqrKey : HKDF.Salt),
      SignalMessage.tryFrom protoSignalCodec body = .ok m ∧
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey) ∧
      ((∃ (ci : Nat) (rc : ReceiverChain) (ck : ChainKey),
          mid = [] ∧ coins = 0#256 ∧
          g_rw.sess.state.receiverChains[ci]? = some rc ∧
          rc.senderRatchetKey = m.senderRatchetKey ∧
          rc.chainKey = some ck ∧
          m.counter < ck.index) ∨
       (∃ (ci : Nat) (rc : ReceiverChain) (ck : ChainKey),
          mid = [] ∧ coins = 0#256 ∧
          g_rw.sess.state.receiverChains[ci]? = some rc ∧
          rc.senderRatchetKey = m.senderRatchetKey ∧
          rc.chainKey = some ck ∧
          ck.index ≤ m.counter) ∨
       (∃ rngBytes : HwBytes,
          mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧ coins = Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes) ∧
          ∀ rc ∈ g_rw.sess.state.receiverChains,
            rc.senderRatchetKey ≠ m.senderRatchetKey)) := by
  have heval0 := heval
  unfold pureEvalRecvWireWithCoinsW at heval
  rw [hwire] at heval
  simp only [wireWhisperTag] at heval
  rcases htry : SignalMessage.tryFrom protoSignalCodec body with e | m
  · simp [htry] at heval
  rw [htry] at heval
  dsimp only at heval
  rcases hrole : Role.ofWho g_rw.who with _ | role
  · simp [evalOpen, hrole] at heval
  have hopen : evalOpen g_rw.who g_rw.sess = some (role, g_rw.sess) := by
    simp [evalOpen, hrole]
  rw [hopen] at heval
  dsimp only at heval
  rcases hres : (messageDecryptSignalW (cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role coins) with ⟨res, calls⟩
  rw [hres] at heval
  dsimp only at heval
  rcases res with e | ptB
  · simp at heval
  simp only [Option.some.injEq, Prod.mk.injEq] at heval
  obtain ⟨_hst, hpt⟩ := heval
  subst hpt
  have h1 : (messageDecryptSignalW (cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role coins).1 = .ok r.message := by
    rw [hres]
  obtain ⟨st', hdec, _hrid, _hstore⟩ :=
    PureRecvEval.storedSession_of_decryptOk (cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) pureSerializeRole m
      role.peer role coins g_rw.sess r.message h1
  obtain ⟨remIk, r2, mkGen, newPqrState, pqrKey, hVer, hRem, hSpqr, _hDec, _hSt', hBr⟩ :=
    Proofs.libsignal.RngG.R3.decryptW_ok_branch hdec
  refine ⟨m, newPqrState, pqrKey, rfl, hSpqr, ?_⟩
  cases hBr with
  | skipped ck hFind hLt _hTake _hMac =>
    have hno : pureDrawsCoins (cryptoOf' interpretation) g_rw.sess.state m.senderRatchetKey = false :=
      pureDrawsCoins_false_of_found hFind
    rcases hmid_cases with ⟨hcoins0, hmid0, _⟩ | ⟨_rngBytes, _, _, _, hdraw⟩
    · obtain ⟨ci, rc, _hci, hrc, hsrk, hck⟩ :=
        Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
      exact Or.inl ⟨ci, rc, ck, hmid0, hcoins0, hrc, hsrk, hck, hLt⟩
    · have hyes := hdraw m htry
      rw [hno] at hyes
      exact Bool.noConfusion hyes
  | existing ck _ck_adv _ck_next _r_adv hFind hNotLt _hJump _hAdv _hNext _hSet _hMkGen _hMac =>
    have hno : pureDrawsCoins (cryptoOf' interpretation) g_rw.sess.state m.senderRatchetKey = false :=
      pureDrawsCoins_false_of_found hFind
    rcases hmid_cases with ⟨hcoins0, hmid0, _⟩ | ⟨_rngBytes, _, _, _, hdraw⟩
    · obtain ⟨ci, rc, _hci, hrc, hsrk, hck⟩ :=
        Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
      exact Or.inr (Or.inl ⟨ci, rc, ck, hmid0, hcoins0, hrc, hsrk, hck, BitVec.not_lt.mp hNotLt⟩)
    · have hyes := hdraw m htry
      rw [hno] at hyes
      exact Bool.noConfusion hyes
  | ratchet ck _ck_adv _ck_next r1 _r_adv hFind hDh _hNotLt _hJump _hAdv _hNext _hSet _hMkGen _hMac =>
    obtain ⟨sc, _newRootKey, _, _, hsc, hrc1, _, _⟩ :=
      Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
    have hyes : pureDrawsCoins (cryptoOf' interpretation) g_rw.sess.state m.senderRatchetKey = true :=
      pureDrawsCoins_true_of_ratchet hRem hFind hsc hrc1
    rcases hmid_cases with ⟨hcoins0, _hmid0, hmiss⟩ | ⟨rngBytes, hmid_rng, hrng_len, hcoins_rng, _⟩
    · have hver_eq : m.messageVersion.toNat = g_rw.sess.state.sessionVersion.toNat :=
        msgVersion_sessionVersion_of_version_pure htry hVer.symm
      have heval_zero : pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
          (Proofs.libsignal.SR.interpW interpretation)
          (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw 0#256 =
          some (r.state, r.message) := hcoins0 ▸ heval0
      have hno := hmiss (r.state, r.message) heval_zero body m hwire htry hver_eq
      rw [hyes] at hno
      exact Bool.noConfusion hno
    · have hci : (Proofs.libsignal.RngG.R3.ratchetStateOf g_rw.sess.state).findReceiverChainIndex
          m.senderRatchetKey = none :=
        Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_none _ _ hFind
      have hNone : ∀ rc ∈ g_rw.sess.state.receiverChains,
          rc.senderRatchetKey ≠ m.senderRatchetKey := by
        intro rc hMem hEq
        unfold RatchetState.findReceiverChainIndex at hci
        rw [List.findIdx?_eq_none_iff] at hci
        have hFalse := hci rc hMem
        simp [hEq] at hFalse
      exact Or.inr (Or.inr ⟨rngBytes, hmid_rng, hrng_len, hcoins_rng, hNone⟩)

theorem evalRecvWireWithCoinsW_branch_cases
    (interpretation : ExternInterpretation)
    (body : HwBytes) (mid : List MachineEvent)
    (r : StateAndMessage) (g_rw : RecvWireGhost) (coins : BitVec 256)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hmid_cases :
      (coins = 0#256 ∧ mid = [] ∧
          recvWireMissFact (cryptoOf' interpretation)
            (Proofs.libsignal.SR.interpW interpretation)
            (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw) ∨
        (∃ rngBytes : HwBytes,
          mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧ coins = Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes) ∧
          (∀ msg, SignalMessage.tryFrom protoSignalCodec body = .ok msg →
            pureDrawsCoins (cryptoOf' interpretation) g_rw.sess.state msg.senderRatchetKey = true)))
    (heval :
      pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw coins =
        some (r.state, r.message)) :
    ∃ (m : SignalMessage) (newPqrState : HwBytes) (pqrKey : HKDF.Salt),
      SignalMessage.tryFrom protoSignalCodec body = .ok m ∧
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey) ∧
      ((∃ (ci : Nat) (rc : ReceiverChain) (ck : ChainKey),
          mid = [] ∧ coins = 0#256 ∧
          g_rw.sess.state.receiverChains[ci]? = some rc ∧
          rc.senderRatchetKey = m.senderRatchetKey ∧
          rc.chainKey = some ck ∧
          m.counter < ck.index) ∨
       (∃ (ci : Nat) (rc : ReceiverChain) (ck : ChainKey),
          mid = [] ∧ coins = 0#256 ∧
          g_rw.sess.state.receiverChains[ci]? = some rc ∧
          rc.senderRatchetKey = m.senderRatchetKey ∧
          rc.chainKey = some ck ∧
          ck.index ≤ m.counter) ∨
       (∃ rngBytes : HwBytes,
          mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧ coins = Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes) ∧
          ∀ rc ∈ g_rw.sess.state.receiverChains,
            rc.senderRatchetKey ≠ m.senderRatchetKey)) :=
  evalRecvWireWithCoinsW_branch_cases_of_draw interpretation body mid r g_rw coins
    hwire hmid_cases heval

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
