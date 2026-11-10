/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CHistStepPure
public import Symbolic.Proofs.Swarm.CREF.TR.PureRecvEval
import Symbolic.Proofs.RngG.R3Canon
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecRecvRkOkRatchetDHPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.HistHwPureA
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj

/-!
# Record-Level Receiver-Chain Inclusion and `RecRecvRkOk`

Proves record-level receiver-chain inclusion across `pureEvalRecvWireWithCoinsW`, preserves
`RecRecvRkOk` on the output record, and extracts entry `RecRecvRkOk` from `CHist` and
`PureCRecRel`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

section RatchetAndEval

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E
open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.SR
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec receiverChainToChainRec)
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.TRREF.GrowthRecordPure (pureSpqr)
open Symbolic.Swarm.CREF.TR (normPending)
open Symbolic.Swarm.CREF.CliPure.TR.CHistStep (RecRecvRkOk)
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep (sessionToRecordRecPending)

theorem storedSession_decryptW_receiverChains_cases {Addr : Type} (C : Crypto) (W : AesW)
    (S : SpqrModel) (ser : Addr → Addr → Option (List (BitVec 8)))
    (msg : SignalMessage) (rem loc : Addr) (coins : BitVec 256)
    (sess : Session (List (BitVec 8))) :
    let sess' := storedSession sess
      (messageDecryptSignalW C W (pureSpqr S) ser (inMemAnswers sess) msg rem loc coins).2
    (∀ rc' ∈ sess'.state.receiverChains,
      ∃ rc₀ ∈ sess.state.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey) ∨
    (∃ (ck : ChainKey) (r1 : RatchetState),
      Mut.exec (RatchetState.dhRatchetStep C msg.senderRatchetKey coins)
        (ratchetStateOf sess.state) = (.ok ck, r1) ∧
      ∀ rc' ∈ sess'.state.receiverChains,
        (∃ rc₀ ∈ sess.state.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey) ∨
          rc'.senderRatchetKey = msg.senderRatchetKey) := by
  dsimp only
  rcases storedSession_decryptW_cases_hw C W (pureSpqr S) ser
      msg rem loc coins sess with h | ⟨pt, st', htr, h⟩
  · left
    rw [h]
    exact fun rc' hrc' => ⟨rc', hrc', rfl⟩
  · rw [h]
    exact tryDecryptFromRecordW_receiverChains_cases htr

theorem flatten_map_lenField_length_ge_hw {α : Type} (tag : Nat) (f : α → List (BitVec 8))
    (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤
      ((l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten).length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

theorem encReceiverChain_length_le_encSession_hw (s : Session (List (BitVec 8)))
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := flatten_map_lenField_length_ge_hw 7 CryptoVerification.E2E.Record.encReceiverChain
    s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega

theorem encSession_length_le_encodeRecord_hw (s : Session (List (BitVec 8))) :
    (CryptoVerification.E2E.Record.encSession s).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField
  dsimp only [Option.map_some]
  simp only [List.length_append]
  omega

theorem storedSession_decryptW_post_hw {Addr : Type} (C : Crypto) (W : AesW) (S : SpqrModel)
    (ser : Addr → Addr → Option (List (BitVec 8)))
    (msg : SignalMessage) (rem loc : Addr) (coins : BitVec 256)
    (sess : Session (List (BitVec 8))) :
    storedSession sess (Proofs.libsignal.SR.messageDecryptSignalW C W (pureSpqr S) ser
        (inMemAnswers sess) msg rem loc coins).2 = sess ∨
      ∃ (st' : SessionState (List (BitVec 8))) (salt : CryptoGames.HKDF.Salt),
        storedSession sess (Proofs.libsignal.SR.messageDecryptSignalW C W (pureSpqr S) ser
            (inMemAnswers sess) msg rem loc coins).2 =
          { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none } ∧
        S.recv sess.state.pqRatchetState msg.pqRatchet = .ok (st'.pqRatchetState, salt) ∧
        (SeedsLen32 sess.state → SeedsLen32 st') ∧
        (sess.state.receiverChains.length ≤ maxReceiverChains →
          st'.receiverChains.length ≤ maxReceiverChains) := by
  rcases storedSession_decryptW_cases_hw C W (pureSpqr S) ser
      msg rem loc coins sess with h | ⟨pt, st', htr, h⟩
  · exact Or.inl h
  · right
    obtain ⟨_, _, _, newPq, salt, -, -, hspqr, -, hst', -⟩ :=
      Proofs.libsignal.RngG.R3.decryptW_ok_branch htr
    obtain ⟨-, -, -, hSeeds, -, hLe, -, -⟩ :=
      Proofs.libsignal.RngG.R3.tryDecryptFromRecordW_ok_state_props htr
    refine ⟨st', salt, h, ?_, hSeeds, hLe⟩
    rw [hst']
    exact hspqr

/-- If `sess` satisfies `slots_RecordCanonical_Q` and the encoded stored session after
`messageDecryptSignalW` satisfies `WireRecCanon`, then `recordBytes (sessionToRecordRecPending sess')`
equals `outState`. -/
theorem recordBytes_storedSession_decryptW_eq_encodeRecord
    {Addr : Type} {Q : List (BitVec 8) → Prop} {C : Crypto} {W : AesW} {S : SpqrModel}
    {ser : Addr → Addr → Option (List (BitVec 8))}
    {recBytes outState : HwBytes} {sess : Session (List (BitVec 8))}
    {msg : SignalMessage} {rem loc : Addr} {coins : BitVec 256}
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q Q recBytes sess)
    (hwc : TR.Pure.WireRecCanon outState)
    (henc : outState = CryptoVerification.E2E.Record.encodeRecord ⟨some (storedSession sess
      (messageDecryptSignalW C W (pureSpqr S) ser (inMemAnswers sess) msg rem loc coins).2)⟩) :
    recordBytes (sessionToRecordRecPending (storedSession sess
      (messageDecryptSignalW C W (pureSpqr S) ser (inMemAnswers sess) msg rem loc coins).2)) =
      outState := by
  set sess' := storedSession sess
    (messageDecryptSignalW C W (pureSpqr S) ser (inMemAnswers sess) msg rem loc coins).2
  obtain ⟨_, _, ⟨_, _, hchains_sc, halice_lt, _, _, _⟩⟩ := hcanon_q
  have hSeeds0 : SeedsLen32 sess.state := fun rc hrc mk hmk => (hchains_sc rc hrc).2 mk hmk
  have halice_and_seeds : sess'.aliceBaseKey = sess.aliceBaseKey ∧ SeedsLen32 sess'.state := by
    dsimp only [sess']
    rcases storedSession_decryptW_post_hw C W S ser msg rem loc coins sess with
      heq | ⟨st', _salt, heq, _, hSeeds, _⟩
    · rw [heq]; exact ⟨rfl, hSeeds0⟩
    · rw [heq]; exact ⟨rfl, hSeeds hSeeds0⟩
  obtain ⟨sess₁, hrc₁, -, -, -, h62, -⟩ := hwc
  have hpq_eq : sess₁.state.pqRatchetState = sess'.state.pqRatchetState :=
    EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₁.1 henc h62
  obtain ⟨_, _, ⟨_, _, _, _, _, hpq₁_lt, _⟩⟩ := hrc₁
  have hpq_lt : sess'.state.pqRatchetState.length < 2 ^ 63 := by
    rw [← hpq_eq]; omega
  have halice_lt' : sess'.aliceBaseKey.length < 2 ^ 63 := by
    rw [halice_and_seeds.1]; omega
  have hseeds' : ∀ rc ∈ sess'.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
    intro rc hrc mk hmk
    have h32 := halice_and_seeds.2 rc hrc mk hmk
    omega
  have hsess_len : (CryptoVerification.E2E.Record.encSession sess').length < 2 ^ 64 := by
    have hle := encSession_length_le_encodeRecord_hw sess'
    rw [← henc] at hle
    omega
  rw [henc]
  refine TR.RecvDecStep.recordBytes_sessionToRecordRecPending_eq_encodeRecord sess'
    halice_lt' hpq_lt hseeds' (fun rc hrc => ?_) hsess_len
  exact Nat.lt_of_le_of_lt (encReceiverChain_length_le_encSession_hw sess' rc hrc) hsess_len

/-- Record-level receiver-chain inclusion across `pureEvalRecvWireWithCoinsW`. -/
theorem evalRecvWireWithCoinsW_receiverChains_cases
    {C : Crypto} {W : AesW} {S : SpqrModel}
    {recBytes : HwBytes} {g : RecvWireGhost} {coins : BitVec 256}
    {out : HwBytes × HwBytes} {rec rec' : RecordRec}
    (hrec : recBytes = recordBytes rec)
    (hrec' : out.1 = recordBytes rec')
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g.sess)
    (hwc : TR.Pure.WireRecCanon out.1)
    (hev : TR.PureRecvEval.pureEvalRecvWireWithCoinsW C W S g coins = some out) :
    (∀ k ∈ rec'.current.receiverChains.map ChainRec.senderRatchetKey,
      k ∈ rec.current.receiverChains.map ChainRec.senderRatchetKey) ∨
    (∃ (msg : SignalMessage) (ck : ChainKey) (r1 : RatchetState),
      Mut.exec (RatchetState.dhRatchetStep C msg.senderRatchetKey coins)
        (ratchetStateOf g.sess.state) = (.ok ck, r1) ∧
      ∀ k ∈ rec'.current.receiverChains.map ChainRec.senderRatchetKey,
        k ∈ rec.current.receiverChains.map ChainRec.senderRatchetKey ∨
          k = msg.senderRatchetKey.serialize) := by
  obtain ⟨_body, msg, role, _hw, _hm, _hopen, henc⟩ :=
    TR.PureRecvEval.pureEvalRecvWireWithCoinsW_some_inv hev
  set sess' := storedSession g.sess
    (messageDecryptSignalW C W (pureSpqr S) TR.PureRecvEval.pureSerializeRole (inMemAnswers g.sess)
      msg role.peer role coins).2
  have hnorm_in : normPending rec = normPending (sessionToRecordRecPending g.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrec hcanon_q
  have hrc_in : rec.current.receiverChains = (sessionToRecordRec g.sess).current.receiverChains := by
    change (normPending rec).current.receiverChains =
      (normPending (sessionToRecordRecPending g.sess)).current.receiverChains
    exact congrArg (fun r : RecordRec => r.current.receiverChains) hnorm_in
  have hbytes_out : recordBytes (sessionToRecordRecPending sess') = out.1 :=
    recordBytes_storedSession_decryptW_eq_encodeRecord hcanon_q hwc henc
  have hnorm_out : normPending rec' = normPending (sessionToRecordRecPending sess') := by
    apply TR.recordBytes_injective
    rw [← hrec', hbytes_out]
  have hrc_out : rec'.current.receiverChains = (sessionToRecordRec sess').current.receiverChains := by
    change (normPending rec').current.receiverChains =
      (normPending (sessionToRecordRecPending sess')).current.receiverChains
    exact congrArg (fun r : RecordRec => r.current.receiverChains) hnorm_out
  rw [hrc_in, hrc_out]
  rcases storedSession_decryptW_receiverChains_cases C W S TR.PureRecvEval.pureSerializeRole
      msg role.peer role coins g.sess with hsub | ⟨ck, r1, hDh, hchains⟩
  · left
    intro k hk
    simp only [sessionToRecordRec, sessionToSessionRec, List.map_map, List.mem_map] at hk ⊢
    obtain ⟨rc', hrc', rfl⟩ := hk
    obtain ⟨rc₀, hrc₀, heq⟩ := hsub rc' hrc'
    refine ⟨rc₀, hrc₀, ?_⟩
    simp [receiverChainToChainRec, heq]
  · right
    refine ⟨msg, ck, r1, hDh, fun k hk => ?_⟩
    simp only [sessionToRecordRec, sessionToSessionRec, List.map_map, List.mem_map] at hk ⊢
    obtain ⟨rc', hrc', rfl⟩ := hk
    rcases hchains rc' hrc' with ⟨rc₀, hrc₀, heq⟩ | hnew
    · left
      refine ⟨rc₀, hrc₀, ?_⟩
      simp [receiverChainToChainRec, heq]
    · right
      simp [receiverChainToChainRec, hnew]

/-- Preserves `RecRecvRkOk` across `pureEvalRecvWireWithCoinsW`. -/
theorem recRecvRkOk_of_evalRecvWireWithCoinsW
    (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    (W : AesW) (S : SpqrModel)
    {recBytes : HwBytes} {g : RecvWireGhost} {coins : BitVec 256}
    {out : HwBytes × HwBytes} {rec : RecordRec}
    (hrec : recBytes = recordBytes rec)
    (hok : RecRecvRkOk rec)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g.sess)
    (hwc : TR.Pure.WireRecCanon out.1)
    (hev : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation E D) W S g coins = some out) :
    ∀ rec' : RecordRec, out.1 = recordBytes rec' → RecRecvRkOk rec' := by
  intro rec' hrec'
  rcases evalRecvWireWithCoinsW_receiverChains_cases hrec hrec' hcanon_q hwc hev with
    hsub | ⟨msg, ck, r1, hDh, hsub⟩
  · intro rc hrc
    have hmem : rc.senderRatchetKey ∈ rec.current.receiverChains.map ChainRec.senderRatchetKey :=
      hsub rc.senderRatchetKey (List.mem_map_of_mem hrc)
    obtain ⟨rc₀, hrc₀, hk⟩ := List.mem_map.mp hmem
    rw [← hk]
    exact hok rc₀ hrc₀
  · exact TR.CHistStep.recRecvRkOk_of_subset_or_dhRatchetStep interpretation hEq E D hok hDh hsub

/-- On either branch of `PureCRecRel`, `CHist` implies that `rec` decodes to a version-4
`RecordRec` satisfying `RecRecvRkOk`. -/
theorem rcv_recRecvRkOk_entry_of_cRecRel
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {p : Participant} {rec : HwBytes}
    (hch : CHist interpretation r S g ms)
    (hcr : PureCRecRel interpretation r S g ms p rec) :
    ∃ rr : RecordRec, rec = recordBytes rr ∧ rr.current.sessionVersion = 4#32 ∧ RecRecvRkOk rr := by
  rcases hcr with htr | ⟨rfl, hp⟩
  · obtain ⟨_, rr, st, stateIdx, hb, hget, _, hst_rel, _, _, _, _⟩ := htr p rec (by simp)
    have hst : st ∈ DY.Libsignal.Composed.Refinement.availableStates r (runTraceMoves r ms) :=
      TR.mem_availableStates_of_trStateStoredAt r ms
        (TR.FreshSigma.at?_eq_some_of_getLocalState_some hget)
    exact ⟨rr, hb, congrArg SessionRec.sessionVersion hst_rel.2,
      TR.CHistStep.recRecvRkOk_of_cHist_frame hch hst hst_rel (fun _ hk => hk)⟩
  · obtain ⟨_sess, _sc, _remote, _items, _kpk, st, stateIdx, _ekIdx, _ctIdx, _ek, _ct,
      _hcanon, _hscope, _hscopeP, hget, _h5, _h6, _h7, _h8, _h9, _h10, _h11, _h12, _h13, _hrem,
      _h15, _h16, _h17, _h18, _h19, _h20, _h21, _h22, _h23, _h24, _h25, rr, hb, hst_rel, _⟩ := hp
    have hst : st ∈ DY.Libsignal.Composed.Refinement.availableStates r (runTraceMoves r ms) :=
      TR.mem_availableStates_of_trStateStoredAt r ms
        (TR.FreshSigma.at?_eq_some_of_getLocalState_some hget)
    exact ⟨rr, hb, congrArg SessionRec.sessionVersion hst_rel.2,
      TR.CHistStep.recRecvRkOk_of_cHist_frame hch hst hst_rel (fun _ hk => hk)⟩

end RatchetAndEval

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
