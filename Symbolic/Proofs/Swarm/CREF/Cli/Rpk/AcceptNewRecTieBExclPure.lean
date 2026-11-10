/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Batteries.Data.UInt
public import Symbolic.Proofs.Refinement.RecordBytesBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure
public import Symbolic.Proofs.Swarm.TRREF.B3DefsPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet
import Symbolic.Proofs.Swarm.CREF.Xpl.SkippedHit
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Receive-Branch Mismatch Exclusions

Aligns concrete receiver chains with `st.recv` under `StateRel` (`a2b_modelChain_of_binChain`),
and rules out two branch mismatches between the binary and the model explanation:
a cached skipped-key binary branch (`m.counter < ck.index`) paired with an RNG-free model `decrypt`
(`a2b_not_decrypt_of_binSkip`), and a DH-ratchet binary branch emitting `.rng` paired with a model
`decryptSkipped` (`a2b_not_decryptSkipped_of_rng`).
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2 Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.Pure

/-- Under `StateRel`, a concrete receiver chain at index `ci` with chain key `ck` corresponds to a
model `RecvChain` at `st.recv[ci]?` with matching index and concretized ratchet key. -/
theorem a2b_modelChain_of_binChain {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {s : Session (List (BitVec 8))} {ci : Nat} {rc : ReceiverChain} {ck : ChainKey}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hrc : s.state.receiverChains[ci]? = some rc) (hck : rc.chainKey = some ck) :
    ∃ c₀ : RecvChain, st.recv[ci]? = some c₀ ∧ c₀.index.toBitVec = ck.index ∧
      gamma interpretation S g c₀.ratchetKey = rc.senderRatchetKey.bytes.toList := by
  have h := congrArg (fun l => l[ci]?) (receiverChains_of_stateRel_tr hrel)
  simp only [List.getElem?_map, hrc, Option.map_some, sessionOf] at h
  cases hc : st.recv[ci]? with
  | none => rw [hc] at h; simp at h
  | some c₀ =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨c₀, rfl, ?_, ?_⟩
    · have hk := congrArg ChainRec.chainKey h
      simp only [recChainOfErased, eraseRecvChain, hck, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hk
      exact hk.1.symm
    · have hk := congrArg ChainRec.senderRatchetKey h
      simp only [recChainOfErased, eraseRecvChain, PublicKey.serialize,
        Symbolic.Swarm.CREF.TR.serializedKey, ecKey, djbType] at hk
      injection hk with _ hbytes
      exact hbytes.symm

/-- Rules out an RNG-free accepting model `decrypt` when the binary takes the cached skipped-key
branch (`m.counter < ck.index`). -/
theorem a2b_not_decrypt_of_binSkip
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc blk : List MachineEvent)
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
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (g_rw : RecvWireGhost) (m : SignalMessage) (ci : Nat) (rc : ReceiverChain) (ck : ChainKey)
    (hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc)
    (hrc_key : rc.senderRatchetKey = m.senderRatchetKey) (hck : rc.chainKey = some ck)
    (hskip_idx : m.counter < ck.index) : False := by
  have hmatch := a2b_block_vis hB hpre hpost
  obtain ⟨st, t, msg, c, c', seed, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver, _hrcf,
      hfind, hidx, _hcons, _hspqr, _hpqSalt, _hmac_eq, _hdec, _hpt⟩ :=
    noRatchet_of_matched hmatch hno_rng hacc
  have hrep : t ∈ recvRepresentations interpretation r₀ S g (ms₀ ++ pre) body := hcurR.2 t hmsg
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, _hks₀,
      hnd₀⟩ := hrr p rec (by simp)
  have hidx₀ : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx₀
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hnorm_eq : normPending rec₀ = normPending (sessionToRecordRecPending g_rw.sess) :=
    rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff, ← hnorm_eq,
      stateRel_normPending_iff]; exact hrel₀
  have hnd1 : ((sessionToRecordRec g_rw.sess).current.receiverChains.map
      ChainRec.senderRatchetKey).Nodup := hrc_rec₀ ▸ hnd₀.1
  obtain ⟨c₀, hc₀, hidx_eq, hrk₀⟩ := a2b_modelChain_of_binChain hrel_sess hrc hck
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld m htry
  have hfind' := hfind
  unfold findRecvChain at hfind'
  have hc_mem : c ∈ st.recv := List.mem_of_find?_eq_some hfind'
  have hc_rk : c.ratchetKey = msg.ratchetKey := by simpa using List.find?_some hfind'
  have hc₀_mem : c₀ ∈ st.recv := List.mem_of_getElem? hc₀
  have hcc : c₀ = c :=
    a2b_recvChain_eq_of_gamma hrel_sess hnd1 hc₀_mem hc_mem
      (by rw [hrk₀, hrc_key, hc_rk, hrk_m])
  have hctr_eq : UInt32.ofBitVec m.counter = msg.counter := UInt32.ext hctr_m.symm
  have hlt : msg.counter < c.index := by
    rw [← hctr_eq, ← hcc]; show m.counter < c₀.index.toBitVec; rw [hidx_eq]; exact hskip_idx
  exact UInt32.not_lt.mpr hidx hlt

/-- Rules out an accepting model `decryptSkipped` when the visible block contains an `.rng` event. -/
theorem a2b_not_decryptSkipped_of_rng
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc blk : List MachineEvent)
    (p : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hacc : ∃ e ∈ blk, eventKind e = .accept) (hrng : ∃ e ∈ blk, eventKind e = .rng) : False := by
  have hmatch := a2b_block_vis hB hpre hpost
  have hacc_vis : ∃ v ∈ (Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).vis
      (runTraceMoves r₀ (ms₀ ++ pre)), v.kind = .accept := by
    obtain ⟨e, he, hk⟩ := hacc
    obtain ⟨v, hv, hev⟩ := Symbolic.Swarm.CREF.xpl_forall₂_mem_left hmatch e he
    exact ⟨v, hv, hev.1.symm.trans hk⟩
  obtain ⟨st, t, msg, seed, rIdx, srcIdx, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver,
      hsk, hunused, hspqr, hpqSalt, hmac_eq, hdec, _hpt, hfind⟩ :=
    skippedHit_of_decryptSkipped hacc_vis
  have hnext := Symbolic.Swarm.CREF.TR.RecvDec.decryptSkipped_next_eq (wrapped := wrapped)
    hst hmsg hparse hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind
  have hnr := Symbolic.Swarm.CREF.TR.RecvDec.newRandoms_decSkippedTr (runTraceMoves r₀ (ms₀ ++ pre)) p
    stateIdx skIdx rIdx srcIdx st msg.ratchetKey seed key pqSalt ptTerm spqr' msg.counter
  rw [← hnext] at hnr
  obtain ⟨e, he, hk⟩ := hrng
  obtain ⟨v, hv, hev⟩ := Symbolic.Swarm.CREF.xpl_forall₂_mem_left hmatch e he
  have hvk : v.kind = .rng := hev.1.symm.trans hk
  rw [vis_decryptSkipped rfl, List.mem_append] at hv
  rcases hv with hv | hv
  · exact (newRandoms_eq_nil_iff_no_rng_decVis _ _ stateIdx msgIdx wrapped).mpr hnr v hv hvk
  · rw [exposures_kind_eq_leak hv] at hvk; cases hvk

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
