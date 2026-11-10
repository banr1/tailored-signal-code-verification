/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieNormPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CHistStepPure
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SkippedKeyRunInvPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecRelInvPure
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Chain-History Invariant Step Across Bob's Pre-Key Start

Proves that `TR.CHistStep.CHist` and `SkippedInstallByteFresh` step across `Move.bobStart` when
Bob accepts a pre-key message into a fresh session.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (TREvent)
open DY.Libsignal.TripleRatchet (SessionInfo findRecvChain setRecvChain recvChainFor)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.CliPure.RpkCli.Skr (skippedKeySrcLt_runTrace)
open Symbolic.Swarm.CREF.CliPure.TR.CHistStep (RecRecvRkOk cHist_step)
open Symbolic.Swarm.CREF.TR.RecvDec
  (at?_eq_none_of_le at?_append_non_entry logSkippedKeysTr logSkippedKeysTr_length
   at?_trEntry_logSkippedKeysTr_lt at?_trEntry_logSkippedKeysTr_add at?_stEntry_logSkippedKeysTr)

private abbrev TREntryBH := DY.ProtocolEvent.ExecEntryT TREvent

private theorem rpkBH_length_preSkip (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) :
    tr.length ≤ (bobStartPreSkipTr tr b a o msg key).length := by
  unfold bobStartPreSkipTr
  dsimp only
  cases o.opk with
  | none =>
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    omega
  | some opkPk =>
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    omega

theorem rpkBH_eventLoggedAt_skippedKeyStored_preSkip (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) (s : SessionInfo) (pk : DY.Bytes) (n : UInt32) (seed : DY.Bytes)
    (rIdx src i : Nat) :
    (bobStartPreSkipTr tr b a o msg key).EventLoggedAt
      (TREvent.SkippedKeyStored s pk n seed rIdx src) i →
    tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i := by
  intro hlog
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog ⊢
  unfold bobStartPreSkipTr at hlog
  dsimp only at hlog
  rw [at?_append_non_entry _ _ rfl] at hlog
  have h1 : ∀ (t : ExecTrace) (ev₀ : TREvent),
      (∀ s' pk' n' seed' rIdx' src', ev₀ ≠ TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') →
      ((t.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE ev₀)).at? i : Option TREntryBH) =
        some ⟨TREvent.SkippedKeyStored s pk n seed rIdx src⟩ →
      (t.at? i : Option TREntryBH) = some ⟨TREvent.SkippedKeyStored s pk n seed rIdx src⟩ := by
    intro t ev₀ hne h
    by_cases hlt : i < t.length
    · rwa [at?_append_of_lt t _ hlt] at h
    · by_cases heq : i = t.length
      · subst heq
        rw [DY.Trace.at?_append] at h
        injection h with h'; injection h' with h'
        exact absurd h' (hne s pk n seed rIdx src)
      · rw [at?_eq_none_of_le _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at h
        cases h
  have hlog2 := h1 _ _ (fun _ _ _ _ _ _ h => by cases h) hlog
  have hlog3 := h1 _ _ (fun _ _ _ _ _ _ h => by cases h) hlog2
  rw [at?_append_non_entry _ _ rfl] at hlog3
  rcases hopk : o.opk with _ | opkPk
  · rw [hopk, at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl] at hlog3
    exact hlog3
  · rw [hopk, at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl] at hlog3
    exact hlog3

theorem rpkBH_availableStates_bobStart {r : ProtocolSetup} {ms : List Move} {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles}
    {pqIdx : Nat} {spqrMsgIdx : UInt32} (shown : Nat)
    (w : BobStartOk (runTraceMoves r ms) b a kh regA mh pqIdx spqrMsgIdx) :
    ∀ st ∈ availableStates r (runTraceMoves r (ms ++ [.bobStart b a kh regA mh pqIdx spqrMsgIdx shown])),
      st ∈ availableStates r (runTraceMoves r ms) ∨ st = rpkR_finalSt w := by
  intro st hst
  unfold availableStates at hst
  obtain ⟨⟨p, _⟩, hls, rfl⟩ := List.mem_map.mp hst
  unfold storedStates DY.ExecTrace.getLocalStateAt at hls
  obtain ⟨i, _, hi_map⟩ := List.mem_filterMap.mp hls
  rw [Option.map_eq_some_iff] at hi_map
  obtain ⟨⟨⟨p', st'⟩⟩, hat, heq⟩ := hi_map
  injection heq with hp hst_eq; subst hp hst_eq
  rw [TR.runTrace_snoc, w.next_eq] at hat
  rcases rpkBH_trStateStoredAt_bobStartTr w hat with ⟨_, hat_tr⟩ | ⟨_, _, rfl⟩
  · exact Or.inl (mem_availableStates_of_trStateStoredAt r ms hat_tr)
  · exact Or.inr rfl

theorem rpkBH_skippedInstallByteFresh_bobStart {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles}
    {pqIdx : Nat} {spqrMsgIdx : UInt32} (shown : Nat)
    (w : BobStartOk (runTraceMoves r ms) b a kh regA mh pqIdx spqrMsgIdx)
    (hbf : SkippedInstallByteFresh interpretation S g r ms) :
    SkippedInstallByteFresh interpretation S g r
      (ms ++ [.bobStart b a kh regA mh pqIdx spqrMsgIdx shown]) := by
  intro s' pk' n' seed' rIdx' src' i' p₀ st₀ c₀ hlog hst₀ hrc c_m hc_m
  let tr := runTraceMoves r ms
  let c := bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk
  let st_r := bobRatchetedSt a w.out.ikB w.out.ikA w.out.keys w.out.spkSk w.msg.ratchetKey
    (randTerm tr.length 32)
  let tr_hs := bobStartPreSkipTr tr b a w.out w.msg w.key
  let skipped := w.msg.counter.toNat - c.index.toNat
  let childIdx := tr_hs.length + skipped + 2
  let tr1 := logSkippedKeysTr (st_r.sessionInfo b) w.msg.ratchetKey c.rIdx childIdx c.chainKey c.index
    skipped tr_hs
  rw [TR.runTrace_snoc, w.next_eq] at hlog hst₀
  have hlog_tr1 : tr1.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    have hlog' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog
    unfold bobStartTr at hlog'
    dsimp only at hlog'
    rw [(TR.RecvDec.logSkippedKeys_run _ _ _ _ _ _ _ _).2] at hlog'
    rw [at?_append_non_entry _ _ rfl] at hlog'
    rcases Nat.lt_or_ge i' (tr1.length + 1) with hlt1 | hge1
    · rw [at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hlog'
      rcases Nat.lt_or_ge i' tr1.length with hlt0 | hge0
      · rw [at?_append_of_lt _ _ hlt0] at hlog'
        exact hlog'
      · have heq0 : i' = tr1.length := by omega
        subst heq0
        rw [DY.Trace.at?_append] at hlog'
        nomatch hlog'
    · rcases Nat.eq_or_lt_of_le hge1 with heq1 | hgt1
      · have hlen_rcv : tr1.length + 1 =
            (tr1.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
              (.Received b st_r.peer w.msg.ratchetKey w.msg.counter w.m))).length := by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        rw [← heq1, hlen_rcv, DY.Trace.at?_append] at hlog'
        nomatch hlog'
      · rw [at?_eq_none_of_le _ (by
          dsimp only [tr1, childIdx, skipped, tr_hs, st_r, c, tr] at hgt1
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
          omega)] at hlog'
        nomatch hlog'
  rcases Nat.lt_or_ge i' tr_hs.length with hi_lt | hi_ge
  · have hlog_hs : tr_hs.EventLoggedAt
        (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' := by
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      have hlog_tr1' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog_tr1
      rwa [at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ hi_lt] at hlog_tr1'
    have hlog0 := rpkBH_eventLoggedAt_skippedKeyStored_preSkip tr b a w.out w.msg w.key
      s' pk' n' seed' rIdx' src' i' hlog_hs
    have hsrc_lt : src' < tr.length :=
      skippedKeySrcLt_runTrace r ms s' pk' n' seed' rIdx' src' i' hlog0
    rcases rpkBH_trStateStoredAt_bobStartTr w hst₀ with ⟨_, hst_tr⟩ | ⟨hsrc_eq, _, _⟩
    · exact hbf s' pk' n' seed' rIdx' src' i' p₀ st₀ c₀ hlog0 hst_tr hrc c_m hc_m
    · have hle_hs := rpkBH_length_preSkip (runTraceMoves r ms) b a w.out w.msg w.key
      dsimp only [tr] at hsrc_lt
      omega
  · have hlog_tr1' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog_tr1
    have hi_lt1 : i' < tr1.length := by
      have hlen := DY.Trace.at?_eq_some_implies_length_le (EntryT := TREntryBH) tr1 i'
      rwa [hlog_tr1'] at hlen
    have htr1_len : tr1.length = tr_hs.length + skipped :=
      logSkippedKeysTr_length _ _ _ _ _ _ _ _
    have hj_lt : i' - tr_hs.length < skipped := by omega
    have hi_eq : i' = tr_hs.length + (i' - tr_hs.length) := by omega
    have hat_add := at?_trEntry_logSkippedKeysTr_add
      (st_r.sessionInfo b) w.msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped tr_hs hj_lt
    rw [hi_eq, hat_add] at hlog_tr1'
    injection hlog_tr1' with hE
    injection hE with hE'
    injection hE' with _ hpk_eq _ _ _ hsrc_eq
    subst hpk_eq hsrc_eq
    rcases rpkBH_trStateStoredAt_bobStartTr w hst₀ with ⟨hsrc_lt, _⟩ | ⟨_, _, rfl⟩
    · have hle_hs := rpkBH_length_preSkip (runTraceMoves r ms) b a w.out w.msg w.key
      dsimp only [childIdx, tr_hs, tr] at hsrc_lt
      omega
    · have hrk : w.c'.ratchetKey = w.msg.ratchetKey :=
        RecRecvRkOkStart.consumeMessageKey_ratchetKey c w.c' w.msg.counter w.seed w.hcons
      have hfind : findRecvChain (rpkR_finalSt w).recv w.msg.ratchetKey = some w.c' := by
        dsimp only [rpkR_finalSt, bobRatchetedSt, setRecvChain, findRecvChain, List.map,
          bobRatchetedChain]
        simp [hrk]
      have hrc_false : recvChainFor (rpkR_finalSt w).toDRState w.msg.ratchetKey =
          some (w.c', false) :=
        recvChainFor_eq_some_false_of_findRecvChain_some hfind
      rw [hrc_false] at hrc
      nomatch hrc

theorem rpkBH_cHist_bobStart_of_recRecvRkOk {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles}
    {pqIdx : Nat} {spqrMsgIdx : UInt32} (shown : Nat)
    (w : BobStartOk (runTraceMoves r ms) b a kh regA mh pqIdx spqrMsgIdx)
    {rec' : RecordRec}
    (hch : TR.CHistStep.CHist interpretation r S g ms)
    (hrel' : StateRel interpretation S g (rpkR_finalSt w) rec')
    (hnd' : (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup)
    (hok' : RecRecvRkOk rec') :
    TR.CHistStep.CHist interpretation r S g (ms ++ [.bobStart b a kh regA mh pqIdx spqrMsgIdx shown]) :=
  cHist_step hch (rpkBH_availableStates_bobStart shown w) hrel' hnd' hok'
    (rpkBH_skippedInstallByteFresh_bobStart shown w)

/-- Steps `TR.CHistStep.CHist` across `Move.bobStart` from `StateRel` and a non-low-order 32-byte
`gamma` image of `w.msg.ratchetKey`. -/
theorem rpkBH_cHist_bobStart {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles}
    {pqIdx : Nat} {spqrMsgIdx : UInt32} (shown : Nat)
    (w : BobStartOk (runTraceMoves r ms) b a kh regA mh pqIdx spqrMsgIdx)
    {rec' : RecordRec}
    (hch : TR.CHistStep.CHist interpretation r S g ms)
    (hrel' : StateRel interpretation S g (rpkR_finalSt w) rec')
    (hnd' : (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup)
    (hlen : (gamma interpretation S g w.msg.ratchetKey).length = 32)
    (hlow : DY.X25519.isLowOrderKey
      ((gamma interpretation S g w.msg.ratchetKey).map BitVec.toNat) = false) :
    TR.CHistStep.CHist interpretation r S g (ms ++ [.bobStart b a kh regA mh pqIdx spqrMsgIdx shown]) := by
  refine rpkBH_cHist_bobStart_of_recRecvRkOk shown w hch hrel' hnd' ?_
  exact RecRecvRkOkStart.recRecvRkOk_bobStart interpretation S g (rpkR_finalSt w) rec'
    (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk) w.c' w.msg.counter w.seed
    hrel' rfl w.hcons hlen hlow

/-- In an accepting `session_recv_prekey` call, `pf.inner.senderRatchetKey` has 32 bytes and is
not low-order. -/
theorem rpkBH_senderRatchetKey_len_notLow {interpretation : ExternInterpretation}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    {r : ProtocolSetup} {pf : PreKeyFields} {d pt : HwBytes}
    {sm : StateAndMessage}
    (hD : AcceptD.AcceptTieD interpretation r pf d pt sm) :
    pf.inner.senderRatchetKey.bytes.toList.length = 32 ∧
    DY.X25519.isLowOrderKey (pf.inner.senderRatchetKey.bytes.toList.map BitVec.toNat) = false := by
  obtain ⟨st0, _, _, _, ck, _, _, r1, _, _, _, _, _, _, -, -, _, _, hDh, -⟩ :=
    AcceptD.rpkI_acceptTieD_ratchet_inv hD
  obtain ⟨sc, newRk, _, _, _, hrc1, -, -⟩ :=
    Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
  exact RecRecvRkOkStart.notLowOrder_of_rootCreateChain_cryptoOf' interpretation hEq
    st0.rootKey pf.inner.senderRatchetKey sc.ratchetKey.privateKey (newRk, ck) hrc1

end Symbolic.Swarm.CREF.CliPure
