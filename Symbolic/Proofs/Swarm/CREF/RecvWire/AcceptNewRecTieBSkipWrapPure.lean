/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.SR.SendSpecWPure
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.TR.PureRecvEval
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieBSkipPure
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.SkippedHit
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Whisper Decrypt Cached Skipped-Key Block Tie

Lifts `a2b_tieB_skip_core` to an accepting `XplBlock` containing a `decryptSkipped` move
framed by `InvisibleNoEffect` prefixes and suffixes.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
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
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2 Proofs.libsignal.RngG.CliPure.R3
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR

/-- Preserves `PureTRRecordStateInv` and `TRNsBound` across a `decryptSkipped` move in an
accepting block on the cached skipped-key branch. -/
theorem a2b_tieB_skip_of_block
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc blk : List MachineEvent) (sent : List HwBytes)
    (p : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (rec body : HwBytes)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hacc : ∃ e ∈ blk, eventKind e = .accept)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body
      (.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped))
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
    (hskip_idx : m.counter < ck.index)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw 0#256 =
        some (r.state, r.message)) :
    PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms₀ ++ pre ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = p then some r.state else none) ∧
      TRNsBound r₀ (ms₀ ++ pre ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])
        sent := by
  have hmatch := a2b_block_vis hB hpre hpost
  have hacc_vis : ∃ v ∈ (Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).vis
      (runTraceMoves r₀ (ms₀ ++ pre)), v.kind = .accept := by
    obtain ⟨e, he, hk⟩ := hacc
    obtain ⟨v, hv, hev⟩ := Symbolic.Swarm.CREF.xpl_forall₂_mem_left hmatch e he
    exact ⟨v, hv, hev.1.symm.trans hk⟩
  obtain ⟨st, t, msg, seed, rIdx, srcIdx, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver,
      hsk, hunused, hspqr, hpqSalt, hmac_eq, hdec, _hpt, hfind⟩ :=
    skippedHit_of_decryptSkipped hacc_vis
  have hrep : t ∈ recvRepresentations interpretation r₀ S g (ms₀ ++ pre) body := hcurR.2 t hmsg
  exact a2b_tieB_skip_core interpretation hceh r₀ S hS g (ms₀ ++ pre)
    (fun q => if q = p then some rec else none) sent hrr hns hrole hat
    p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped st t msg seed rIdx srcIdx spqr' key pqSalt
    ptTerm hst hcurR.1 hmsg hparse hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind
    rec body r g_rw m ci rc ck newPqrState pqrKey (by simp) hrep hstate_lt hcanon' hwire hcanon_q
    htry hrc hrc_key hck hskip_idx hrecv_spqr heval

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
