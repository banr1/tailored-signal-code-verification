/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieACorePure
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Block-Level Existing-Chain Whisper Decrypt Tie

Lifts `a2b_tieA_core` to an accepting `XplBlock` decomposed as `pre ++ Move.decrypt ... :: post`
with `InvisibleNoEffect` surrounding moves.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2 Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR

/-- Preserves `PureTRRecordStateInv` and `TRNsBound` across a no-ratchet `Move.decrypt` in an
accepting block when `pureEvalRecvWireWithCoinsW` takes the existing-chain branch. -/
theorem a2b_tieA_of_block
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc blk : List MachineEvent) (sent : List HwBytes)
    (p : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (rec body : HwBytes)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hno_rng : ∀ e ∈ blk, eventKind e ≠ .rng) (hacc : ∃ e ∈ blk, eventKind e = .accept)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body
      (.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped))
    (hrr : PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g (ms₀ ++ pre)
      (fun q => if q = p then some rec else none))
    (hns : TRNsBound r₀ (ms₀ ++ pre) sent)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r₀ S g (ms₀ ++ pre))
    (r : StateAndMessage) (g_rw : RecvWireGhost)
    (m : SignalMessage) (ci : Nat) (rc : ReceiverChain) (ck : ChainKey)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hstate_lt : r.state.length < 2 ^ 64)
    (hcanon' : r.state.length < 2 ^ 32 - 2 ^ 20 → (pureTrSlots r₀).canon p r.state)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc)
    (hrc_key : rc.senderRatchetKey = m.senderRatchetKey) (hck : rc.chainKey = some ck)
    (hstep_idx : ck.index ≤ m.counter)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins none) =
        some (r.state, r.message)) :
    PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = p then some r.state else none) ∧
      TRNsBound r₀ (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) sent := by
  have hmatch := a2b_block_vis hB hpre hpost
  obtain ⟨st, t, msg, c, c', seed, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver, _hrcf,
      hfind, _hidx, hcons, hspqr, hpqSalt, hmac_eq, hdec, _hpt⟩ :=
    noRatchet_of_matched hmatch hno_rng hacc
  have hreach : (runTraceMoves r₀ (ms₀ ++ pre)).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 (ms₀ ++ pre).length
    rwa [← List.append_assoc, List.take_left] at h
  have hrun : ModelRun r₀ (ms₀ ++ pre) := by
    have h := hB.run
    rw [← List.append_assoc] at h
    exact modelRun_prefix_of_reachable h hreach
  have hrep : t ∈ recvRepresentations interpretation r₀ S g (ms₀ ++ pre) body := hcurR.2 t hmsg
  exact a2b_tieA_core interpretation hceh r₀ hwf S hS g (ms₀ ++ pre)
    (fun q => if q = p then some rec else none) sent hB.pre.1 hrun hrr hns hrole hat
    p stateIdx msgIdx pqIdx spqrMsgIdx wrapped st t msg c c' seed spqr' key pqSalt ptTerm
    hst hcurR.1 hmsg hparse hver hfind hcons hspqr hpqSalt hmac_eq hdec
    rec body r g_rw m ci rc ck newPqrState pqrKey (by simp) hrep hstate_lt hcanon' hwire hcanon_q
    htry hrc hrc_key hck hstep_idx hrecv_spqr heval

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
