/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
import DY.Trace.Basic
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvFreshLinkPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvFreshLinkPureA
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# No-Ratchet Decrypt Step Lemmas at General Traces

Characterizes the post-move trace `decTailTr` for an existing-chain `decrypt` move at an
arbitrary `runTraceMoves r₀ ms`, and establishes `TRNsBound`, singleton `PureTRRecordStateInv`,
and skipped-key invariants across `decTailTr`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain setRecvChain consumeMessageKey chainKeyAt
  kdfCk computeMac messageVersion)
open DY.Libsignal.TripleRatchet
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec (decrypt_next_noRatchet_eq)

theorem a2b_runTrace_decrypt_noRatchet
    {r₀ : ProtocolSetup} {ms : List Move} {p : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {wrapped : Bool}
    {st : TRState} {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c c' : RecvChain}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm) :
    runTraceMoves r₀ (ms ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) =
      decTailTr ((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)) p stateIdx st c c'
        msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
  rw [runTrace_snoc, ← decTailTr_eq_recvDec]
  exact decrypt_next_noRatchet_eq hst hmsg hparse hver hfind hcons hspqr hpqSalt hmac_eq hdec

theorem a2b_trNsBound_decTail
    {r₀ : ProtocolSetup} {ms : List Move} {sent : List HwBytes} {m : Move}
    {p : Participant} {stateIdx : Nat} {st : TRState}
    {key seed pqSalt ptTerm spqr' pk : DY.Bytes} {c c' : RecvChain} {n : UInt32}
    (hns : TRNsBound r₀ ms sent)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      decTailTr ((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)) p stateIdx st c c'
        pk seed pqSalt ptTerm spqr' n) :
    TRNsBound r₀ (ms ++ [m]) sent := by
  intro q idx st_q hget
  rw [htr] at hget
  by_cases hlt : idx < ((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)).length +
      (n.toNat - c.index.toNat) + 2
  · rw [getLocalState_fst, at?_stEntry_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ hlt,
      at?_append_non_entry _ _ rfl, ← getLocalState_fst] at hget
    exact hns q idx st_q hget
  · by_cases heq : idx = ((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)).length +
        (n.toNat - c.index.toNat) + 2
    · subst heq; rw [getLocalState_fst, at?_stEntry_decTailTr_last] at hget
      by_cases hqp : p = q
      · subst hqp; simp only [↓reduceIte, Option.some.injEq] at hget; subst hget
        exact hns p stateIdx st hst
      · simp only [hqp, ↓reduceIte] at hget; cases hget
    · rw [getLocalState_fst, at?_eq_none_of_le _ (by rw [decTailTr_length]; omega)] at hget
      cases hget

theorem findRecvChain_setRecvChain_isSome (recv : List RecvChain) (c : RecvChain) (pk : DY.Bytes) :
    (findRecvChain (setRecvChain recv c) pk).isSome = (findRecvChain recv pk).isSome := by
  unfold findRecvChain setRecvChain
  induction recv with
  | nil => rfl
  | cons d tl ih =>
    rw [List.map_cons, List.find?_cons, List.find?_cons]
    have hrk : (if (d.ratchetKey == c.ratchetKey) = true then c else d).ratchetKey = d.ratchetKey := by
      cases h : d.ratchetKey == c.ratchetKey
      · rfl
      · exact (beq_iff_eq.mp h).symm
    rw [hrk]
    cases d.ratchetKey == pk
    · exact ih
    · rfl

/-- Establishes `PureTRRecordStateInv` for the singleton update assigning `newBytes` to `p`
after a `decTailTr` transition. -/
theorem a2b_trRecordStateInv_decTail_single
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : SpqrSem} {Z : PureTRSlots}
    {g : Ghost} {ms : List Move} {m : Move}
    {p : Participant} {stateIdx : Nat} {st : TRState} {rec' : RecordRec} {newBytes : HwBytes}
    {key seed pqSalt ptTerm spqr' pk : DY.Bytes} {c c' : RecvChain} {n : UInt32}
    (hp_mem : p = r₀.alice ∨ p = r₀.bob)
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      decTailTr ((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)) p stateIdx st c c'
        pk seed pqSalt ptTerm spqr' n)
    (hnew : newBytes = recordBytes rec')
    (hrel' : StateRel interpretation S g { st with recv := setRecvChain st.recv c', spqr := spqr' }
      rec')
    (hsk' : ∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys,
      ∃ pk_k rIdx srcIdx skIdx seed_k,
        (runTraceMoves r₀ (ms ++ [m])).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx srcIdx)
          skIdx ∧
        !skippedKeyUsedB (runTraceMoves r₀ (ms ++ [m])) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r₀ (ms ++ [m])) (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1)
          rIdx ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k) ∧
        (findRecvChain { st with recv := setRecvChain st.recv c', spqr := spqr' }.toDRState.recv pk_k).isSome = true)
    (hcanon' : newBytes.length < 2 ^ 32 - 2 ^ 20 → Z.canon p newBytes)
    (hks : TRKeyShape interpretation S g st)
    (hnd' : (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
      (∀ c_k ∈ rec'.current.receiverChains, (c_k.messageKeys.map Prod.fst).Nodup) ∧
      ∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys,
        ∃ ck, c_k.chainKey = some ck ∧ k.1 < ck.1) :
    PureTRRecordStateInv interpretation r₀ S Z g (ms ++ [m])
      (fun q => if q = p then some newBytes else none) := by
  intro q b hqb
  by_cases hqp : q = p
  · subst hqp; simp only [↓reduceIte, Option.some.injEq] at hqb; subst hqb
    refine ⟨hp_mem, rec', { st with recv := setRecvChain st.recv c', spqr := spqr' },
      ((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)).length +
        (n.toNat - c.index.toNat) + 2, hnew, ?_, ?_, hrel', hsk', hcanon',
      trKeyShape_setRecvChain_spqr hks c' spqr', hnd'⟩
    · rw [htr, getLocalState_decTailTr_last]
    · rw [htr, isCurrentSnapshot_decTailTr_last]
  · simp only [hqp, ↓reduceIte] at hqb; cases hqb

private theorem a2b_index_le_of_cons {c c' : RecvChain} {ctr : UInt32} {seed : DY.Bytes}
    (hcons : consumeMessageKey c ctr = some (seed, c')) : c.index ≤ ctr := by
  have hnotlt := ((consumeMessageKey_eq_some_iff_tr c ctr seed c').mp hcons).1
  rw [UInt32.lt_iff_toNat_lt] at hnotlt; rw [UInt32.le_iff_toNat_le]; omega

private theorem a2b_uint32_le_add {idx ctr : UInt32} {j : Nat}
    (hj : j < ctr.toNat - idx.toNat) : idx ≤ idx + UInt32.ofNat j := by
  rw [UInt32.le_iff_toNat_le]
  have hctr_lt : ctr.toBitVec.toNat < 2 ^ 32 := ctr.toBitVec.isLt
  have hctr_eq : ctr.toBitVec.toNat = ctr.toNat := rfl
  have hlt32 : idx.toNat + j < 2 ^ 32 := by omega
  change idx.toBitVec.toNat ≤ (idx.toBitVec + BitVec.ofNat 32 j).toNat
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hidx : idx.toBitVec.toNat = idx.toNat := rfl; omega

/-- Preserves and extends the skipped-key invariant across an existing-chain `decTailTr` step. -/
theorem a2b_skippedOk_existing_decTail
    {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {r₀ : ProtocolSetup} {ms : List Move} {m : Move} {p : Participant} {stateIdx : Nat}
    {st : TRState} {c c' : RecvChain} {key seed pqSalt ptTerm spqr' pkL : DY.Bytes} {ctr : UInt32}
    {rec rec' : RecordRec}
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hF : TRRecvCountersFresh (runTraceMoves r₀ ms) p st) (hc_mem : c ∈ st.recv)
    (hc_rk : c.ratchetKey = pkL)
    (hcons : consumeMessageKey c ctr = some (seed, c'))
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      decTailTr ((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)) p stateIdx st c c'
        pkL seed pqSalt ptTerm spqr' ctr)
    (hback : ∀ c_old ∈ rec.current.receiverChains, ∀ k ∈ c_old.messageKeys,
      ∃ (pk_k : DY.Bytes) (rIdx_k srcIdx_k skIdx_k : Nat) (seed_k : DY.Bytes),
        (runTraceMoves r₀ ms).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k)
          skIdx_k ∧
        !skippedKeyUsedB (runTraceMoves r₀ ms) skIdx_k ∧
        !receiverKeyUsedB (runTraceMoves r₀ ms) (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx_k ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_old.senderRatchetKey = serializedKey (gamma interpretation S g pk_k) ∧
        (findRecvChain st.toDRState.recv pk_k).isSome = true)
    (hSub : ∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys,
      (∃ c_old ∈ rec.current.receiverChains,
        c_old.senderRatchetKey = c_k.senderRatchetKey ∧ k ∈ c_old.messageKeys) ∨
      (c_k.senderRatchetKey = serializedKey (gamma interpretation S g pkL) ∧
        ∃ j < ctr.toNat - c.index.toNat,
          UInt32.ofBitVec k.1 = c.index + UInt32.ofNat j ∧
          UInt32.ofBitVec k.1 ≠ ctr ∧
          k.2 = gamma interpretation S g (kdfCk (chainKeyAt c.chainKey j)).2)) :
    ∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys,
      ∃ pk_k rIdx srcIdx skIdx seed_k,
        (runTraceMoves r₀ (ms ++ [m])).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx srcIdx)
          skIdx ∧
        !skippedKeyUsedB (runTraceMoves r₀ (ms ++ [m])) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r₀ (ms ++ [m])) (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1)
          rIdx ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k) ∧
        (findRecvChain { st with recv := setRecvChain st.recv c', spqr := spqr' }.toDRState.recv pk_k).isSome = true := by
  intro c_k hc_k k hk
  rw [htr]
  let tr := runTraceMoves r₀ ms
  let tr_pre := tr.append (⟨key⟩ : Network.ExecEntryT)
  have hIdxLe : c.index ≤ ctr := a2b_index_le_of_cons hcons
  rcases hSub c_k hc_k k hk with ⟨c_old, hc_old, hsrkEq, hk_old⟩ |
      ⟨hlinkNew, j, hjLt, hjU32, hjNe, hjSeed⟩
  · obtain ⟨pk_k, rIdx_k, srcIdx_k, skIdx_k, seed_k, hlog, hsu, hru, hgam, hlink, hfind_k⟩ :=
      hback c_old hc_old k hk_old
    have hlt_tr : skIdx_k < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := TREntry) tr skIdx_k
      have hlog' := hlog
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog'
      rw [hlog'] at this; exact this
    have hlt_pre : skIdx_k < tr_pre.length := by
      simp only [tr_pre, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega
    have hne_cnt : ¬ (seed = seed_k ∧ ctr = UInt32.ofBitVec k.1 ∧ c.rIdx = rIdx_k) :=
      not_consumed_of_skippedKeyStored_tr hF hc_mem hIdxLe hlog
    refine ⟨pk_k, rIdx_k, srcIdx_k, skIdx_k, seed_k, ?_, ?_, ?_, hgam, hsrkEq.symm.trans hlink, ?_⟩
    · rw [eventLoggedAt_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ hlt_pre,
        eventLoggedAt_append_non_tr_a2 _ _ rfl]
      exact hlog
    · rw [skippedKeyUsedB_decTailTr, skippedKeyUsedB_append_non_tr_a2 _ _ rfl]; exact hsu
    · rw [receiverKeyUsedB_decTailTr, receiverKeyUsedB_append_non_tr_a2 _ _ rfl]
      have hfalse : decide (st.sessionInfo p = st.sessionInfo p ∧ seed = seed_k ∧
          ctr = UInt32.ofBitVec k.1 ∧ c.rIdx = rIdx_k) = false := by
        simp [hne_cnt]
      rw [hfalse, Bool.or_false]; exact hru
    · dsimp only
      rw [findRecvChain_setRecvChain_isSome]
      exact hfind_k
  · refine ⟨pkL, c.rIdx, stateIdx, tr_pre.length + j, (kdfCk (chainKeyAt c.chainKey j)).2,
      ?_, ?_, ?_, hjSeed.symm, hlinkNew, ?_⟩
    · rw [hjU32]
      exact hsk'_decTailTr_of_new_exact_tr tr_pre p stateIdx st c c' pkL seed pqSalt ptTerm spqr'
        ctr hjLt
    · rw [skippedKeyUsedB_decTailTr, skippedKeyUsedB_append_non_tr_a2 _ _ rfl]
      have hge : tr.length ≤ tr_pre.length + j := by
        simp only [tr_pre, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega
      rw [skippedKeyUsedB_of_ge_length_tr hreach hge]; rfl
    · rw [receiverKeyUsedB_decTailTr]
      have hne_ctr : ¬ (ctr = UInt32.ofBitVec k.1) := fun h => hjNe h.symm
      simp only [hne_ctr, false_and, and_false, decide_false, Bool.or_false]
      rw [receiverKeyUsedB_append_non_tr_a2 _ _ rfl]
      have hge_idx : c.index ≤ UInt32.ofBitVec k.1 := by
        rw [hjU32]; exact a2b_uint32_le_add hjLt
      rw [receiverKeyUsedB_false_of_ge_tr hF hc_mem _ hge_idx]; rfl
    · dsimp only
      rw [findRecvChain_setRecvChain_isSome]
      exact List.find?_isSome.mpr ⟨c, hc_mem, beq_iff_eq.mpr hc_rk⟩

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
