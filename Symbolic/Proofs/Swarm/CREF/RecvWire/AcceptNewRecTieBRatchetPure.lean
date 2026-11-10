/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Batteries.Data.UInt
import DY.Actions.ProtocolEvent
import DY.Trace.Basic
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptSplitPure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHProvPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureA
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieBRatchetPureA
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.RatchetHit
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# Block-Level DH-Ratchet Whisper Decrypt Tie

Proves `PureTRRecordStateInv` and `TRNsBound` preservation across an accepting DH-ratchet
`Move.decrypt` block (`rcvAccBlk body [.rng rngBytes] r`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt gamma_concat gamma_dhPk getLocalState_fst leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd uOf_leBytes uOf_lt
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.DiffieHellman DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain setRecvChain chainKeyAt kdfCk maxForwardJumps)
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
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec
  receiverChainToChainRec)
open CryptoVerification.SessionModel.AdvanceAndFrame (mem_set_or)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState decRatchetPreTr)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (recordBytes_sessionToRecordRecPending_eq_encodeRecord_64)

open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep (receiverKeyUsedB_false_of_gt_rIdx_tr not_consumed_of_skippedKeyStored_gt_rIdx_tr)

private theorem a2b_findRecvChain_setRecvChain_isSome (recv : List RecvChain) (c : RecvChain) (pk : DY.Bytes) :
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

private theorem a2b_drop_append_of_le {α : Type} :
    ∀ (xs ys : List α) (d : Nat), d ≤ xs.length → (xs ++ ys).drop d = xs.drop d ++ ys
  | xs, ys, 0, _ => rfl
  | [], _, d + 1, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos d))
  | _ :: xs, ys, d + 1, h => a2b_drop_append_of_le xs ys d (Nat.le_of_succ_le_succ h)

private theorem a2b_map_drop_eq {α β : Type} (f : α → β) :
    ∀ (xs : List α) (d : Nat), (xs.drop d).map f = (xs.map f).drop d
  | xs, 0 => rfl
  | [], _ + 1 => rfl
  | _ :: xs, d + 1 => a2b_map_drop_eq f xs d

private theorem a2b_eq_of_mem_of_nodup_map {α β : Type} (f : α → β) :
    ∀ {xs : List α} {a b : α}, (xs.map f).Nodup → a ∈ xs → b ∈ xs → f a = f b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: xs, a, b, hnd, ha, hb, heq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (heq ▸ List.mem_map_of_mem hb') hnd.1
    · exact absurd (heq.symm ▸ List.mem_map_of_mem ha') hnd.1
    · exact a2b_eq_of_mem_of_nodup_map f hnd.2 ha' hb' heq

private theorem a2b_findRecvChain_trDhRatchetState_self_isSome
    (st : TRState) (pk : DY.Bytes) (ts : Nat) (c' : RecvChain) (spqr' : DY.Bytes) :
    (findRecvChain
      { (trDhRatchetState st pk ts).1 with
        recv := setRecvChain (trDhRatchetState st pk ts).1.recv c',
        spqr := spqr' }.toDRState.recv pk).isSome = true := by
  dsimp only
  rw [a2b_findRecvChain_setRecvChain_isSome]
  unfold trDhRatchetState
  dsimp only
  have hd : (st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains ≤ st.recv.length := by
    change (st.recv.length + 1) - 5 ≤ st.recv.length; omega
  rw [a2b_drop_append_of_le _ _ _ hd]
  exact List.find?_isSome.mpr
    ⟨_, List.mem_append_right _ (List.Mem.head []), beq_self_eq_true pk⟩

private theorem a2b_findRecvChain_trDhRatchetState_old_isSome
    {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    {rc' rc_new : ReceiverChain} {pk pk_k : DY.Bytes} {ts : Nat}
    {c' : RecvChain} {spqr' : DY.Bytes}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hnd : ((sessionToRecordRec s).current.receiverChains.map ChainRec.senderRatchetKey).Nodup)
    (hrc_drop : rc' ∈ RatchetState.evictReceiverChains (s.state.receiverChains ++ [rc_new]))
    (hne_new : rc' ≠ rc_new)
    (hlink : (receiverChainToChainRec rc').senderRatchetKey =
      serializedKey (gamma interpretation S g pk_k))
    (hfind_old : (findRecvChain st.toDRState.recv pk_k).isSome = true) :
    (findRecvChain
      { (trDhRatchetState st pk ts).1 with
        recv := setRecvChain (trDhRatchetState st pk ts).1.recv c',
        spqr := spqr' }.toDRState.recv pk_k).isSome = true := by
  dsimp only
  rw [a2b_findRecvChain_setRecvChain_isSome]
  have hrc_eq : (sessionToRecordRec s).current.receiverChains.map
        (fun c => { c with messageKeys := [] }) =
      (Symbolic.Swarm.CREF.TR.sessionOf interpretation (gamma interpretation S g) st).receiverChains := by
    simpa [Symbolic.Swarm.CREF.TR.eraseSkipped, Symbolic.Swarm.CREF.TR.eraseUnmodelled] using
      congrArg SessionRec.receiverChains hrel.2
  let f_bin : ReceiverChain → HwBytes := fun rc => rc.senderRatchetKey.serialize
  let f_mod : RecvChain → HwBytes := fun c => serializedKey (gamma interpretation S g c.ratchetKey)
  have hmap_rec : (sessionToRecordRec s).current.receiverChains.map ChainRec.senderRatchetKey =
      s.state.receiverChains.map f_bin := by
    dsimp only [sessionToRecordRec, sessionToSessionRec, receiverChainToChainRec, f_bin]
    rw [List.map_map]; rfl
  have hmap_eq : s.state.receiverChains.map f_bin = st.recv.map f_mod := by
    have h1 := congrArg (List.map ChainRec.senderRatchetKey) hrc_eq
    rw [List.map_map] at h1
    dsimp only [Symbolic.Swarm.CREF.TR.sessionOf] at h1
    rw [List.map_map] at h1
    exact hmap_rec.symm.trans h1
  have hlen_eq : s.state.receiverChains.length = st.recv.length := by
    have h := congrArg List.length hmap_eq
    simpa only [List.length_map] using h
  have hd_bin : (s.state.receiverChains.length + 1) -
      CryptoGames.LibsignalSession.maxReceiverChains ≤ s.state.receiverChains.length := by
    change (s.state.receiverChains.length + 1) - 5 ≤ s.state.receiverChains.length; omega
  have hrc_in_drop : rc' ∈ s.state.receiverChains.drop ((st.recv.length + 1) - 5) := by
    unfold RatchetState.evictReceiverChains at hrc_drop
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hrc_drop
    rw [a2b_drop_append_of_le _ _ _ hd_bin] at hrc_drop
    change rc' ∈ s.state.receiverChains.drop ((s.state.receiverChains.length + 1) - 5) ++ [rc_new] at hrc_drop
    rw [hlen_eq] at hrc_drop
    rcases List.mem_append.mp hrc_drop with h | h
    · exact h
    · cases h with
      | head => exact absurd rfl hne_new
      | tail _ h' => nomatch h'
  have hf_in_drop : f_bin rc' ∈ (st.recv.drop ((st.recv.length + 1) - 5)).map f_mod := by
    rw [a2b_map_drop_eq, ← hmap_eq, ← a2b_map_drop_eq]
    exact List.mem_map_of_mem hrc_in_drop
  obtain ⟨c₁, hc₁_drop, hc₁_f⟩ := List.mem_map.mp hf_in_drop
  obtain ⟨c₀, hc₀_mem, hc₀_beq⟩ := List.find?_isSome.mp hfind_old
  have hc₀_rk : c₀.ratchetKey = pk_k := beq_iff_eq.mp hc₀_beq
  have hnd_mod : (st.recv.map f_mod).Nodup := by
    rw [← hmap_eq, ← hmap_rec]; exact hnd
  have hf_eq : f_mod c₁ = f_mod c₀ := by
    rw [hc₁_f]
    dsimp only [f_bin, f_mod]
    rw [hc₀_rk]
    exact hlink
  have hc_eq : c₁ = c₀ :=
    a2b_eq_of_mem_of_nodup_map f_mod hnd_mod (List.mem_of_mem_drop hc₁_drop) hc₀_mem hf_eq
  subst hc_eq
  unfold trDhRatchetState
  dsimp only
  have hd_mod : (st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains ≤ st.recv.length := by
    change (st.recv.length + 1) - 5 ≤ st.recv.length; omega
  rw [a2b_drop_append_of_le _ _ _ hd_mod]
  exact List.find?_isSome.mpr ⟨c₁, List.mem_append_left _ hc₁_drop, hc₀_beq⟩

/-- Skipped-key preservation across a DH-ratchet `decrypt` move at a general trace `runTraceMoves r₀ ms`. -/
theorem a2b_skippedOk_ratchet_decTail
    {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {r₀ : ProtocolSetup} {ms : List Move} {m_move : Move} {p : Participant} {stateIdx : Nat}
    {st : TRState} {seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c' : RecvChain}
    {s s' : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    {their : PublicKey} {ck ck_next : ChainKey} {r1 r2 : RatchetState}
    {mks' : List MessageKeyGenerator}
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hF : TRRecvCountersFresh (runTraceMoves r₀ ms) p st)
    (htr : runTraceMoves r₀ (ms ++ [m_move]) =
      decTailTr
        (decRatchetPreTr (runTraceMoves r₀ ms) p
          (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1 msg.ratchetKey key)
        p stateIdx
        (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1
        (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2
        c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter)
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hnd : ((sessionToRecordRec s).current.receiverChains.map ChainRec.senderRatchetKey).Nodup)
    (hrsiSk : ∀ c_old ∈ (sessionToRecordRec s).current.receiverChains, ∀ k ∈ c_old.messageKeys,
      ∃ (pk_k : DY.Bytes) (rIdx_k srcIdx_k skIdx_k : Nat) (seed_k : DY.Bytes),
        (runTraceMoves r₀ ms).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k)
          skIdx_k ∧
        !skippedKeyUsedB (runTraceMoves r₀ ms) skIdx_k ∧
        !receiverKeyUsedB (runTraceMoves r₀ ms) (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx_k ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_old.senderRatchetKey = serializedKey (gamma interpretation S g pk_k) ∧
        (findRecvChain st.toDRState.recv pk_k).isSome = true)
    (htheir : their.bytes.toList = gamma interpretation S g msg.ratchetKey)
    (hR1Rc : r1.receiverChains =
      RatchetState.evictReceiverChains (s.state.receiverChains ++ [⟨their, some ck, []⟩]))
    (hR2Rc : r2.receiverChains =
      r1.receiverChains.set (r1.receiverChains.length - 1) ⟨their, some ck_next, mks'⟩)
    (hMks' : ∀ k ∈ mks',
      ∃ j < msg.counter.toNat,
        k.counter = BitVec.ofNat 32 j ∧ UInt32.ofBitVec k.counter = UInt32.ofNat j ∧
        UInt32.ofBitVec k.counter ≠ msg.counter ∧
        k.seed = gamma interpretation S g
          (kdfCk (chainKeyAt
            (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2.chainKey j)).2 ∧
        k.seed.length = 32)
    (hRcs' : s'.state.receiverChains = r2.receiverChains) :
    ∀ c_k ∈ (sessionToRecordRec s').current.receiverChains, ∀ k ∈ c_k.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed_k,
        (runTraceMoves r₀ (ms ++ [m_move])).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk (UInt32.ofBitVec k.1) seed_k rIdx srcIdx) skIdx ∧
        !skippedKeyUsedB (runTraceMoves r₀ (ms ++ [m_move])) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r₀ (ms ++ [m_move])) (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain
          { (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1 with
            recv := setRecvChain (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.recv c',
            spqr := spqr' }.toDRState.recv pk).isSome = true := by
  intro c_k hc_k k hk
  rw [htr]
  let tr := runTraceMoves r₀ ms
  let st1 := (trDhRatchetState st msg.ratchetKey tr.length).1
  let c := (trDhRatchetState st msg.ratchetKey tr.length).2
  let tr_pre := decRatchetPreTr tr p st1 msg.ratchetKey key
  have hsinfo : st1.sessionInfo p = st.sessionInfo p := rfl
  have hrIdx_c : c.rIdx = st.rIdx + 2 := rfl
  have hgt_rIdx : st.rIdx < c.rIdx := by omega
  simp only [sessionToRecordRec, sessionToSessionRec, hRcs', hR2Rc, List.mem_map] at hc_k
  rcases hc_k with ⟨rc', hrc', rfl⟩
  simp only [receiverChainToChainRec, List.mem_map] at hk
  rcases hk with ⟨mk, hmk, rfl⟩
  rcases mem_set_or r1.receiverChains (r1.receiverChains.length - 1) ⟨their, some ck_next, mks'⟩
      rc' hrc' with rfl | hrc_r1
  · obtain ⟨j, hjLt, _, hjU32, hjNe, hjSeed, _⟩ := hMks' mk hmk
    refine ⟨msg.ratchetKey, c.rIdx, stateIdx, tr_pre.length + j,
      (kdfCk (chainKeyAt c.chainKey j)).2, ?_, ?_, ?_, hjSeed.symm, ?_,
      a2b_findRecvChain_trDhRatchetState_self_isSome st msg.ratchetKey tr.length c' spqr'⟩
    · have hjLt' : j < msg.counter.toNat - c.index.toNat := by change j < msg.counter.toNat - 0; omega
      have h0 : c.index + UInt32.ofNat j = UInt32.ofBitVec mk.counter := by
        rw [hjU32]; change (0 : UInt32) + UInt32.ofNat j = UInt32.ofNat j
        exact UInt32.zero_add (UInt32.ofNat j)
      rw [← hsinfo, ← h0]
      exact hsk'_decTailTr_of_new_exact_tr tr_pre p stateIdx st1 c c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter hjLt'
    · rw [skippedKeyUsedB_decTailTr]
      change (!skippedKeyUsedB tr_pre (tr_pre.length + j)) = true
      dsimp only [tr_pre]
      rw [a2b_skippedKeyUsedB_decRatchetPreTr]
      have hge : tr.length ≤ tr_pre.length + j := by
        simp only [tr_pre, decRatchetPreTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega
      rw [Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.skippedKeyUsedB_of_ge_length_tr hreach hge]; rfl
    · rw [← hsinfo, receiverKeyUsedB_decTailTr, hsinfo]
      have hne_ctr : ¬ (msg.counter = UInt32.ofBitVec mk.counter) := fun h => hjNe h.symm
      simp only [hne_ctr, false_and, and_false, decide_false, Bool.or_false]
      rw [a2b_receiverKeyUsedB_decRatchetPreTr,
          Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.receiverKeyUsedB_false_of_gt_rIdx_tr hF hgt_rIdx]; rfl
    · show their.serialize = _
      rw [← htheir]; rfl
  · rw [hR1Rc] at hrc_r1
    have hne_new : rc' ≠ ⟨their, some ck, []⟩ := fun h => by subst h; cases hmk
    have hrc_app := List.mem_of_mem_drop hrc_r1
    rw [List.mem_append, List.mem_singleton] at hrc_app
    rcases hrc_app with hrc_old | rfl
    swap
    · cases hmk
    have hc_old : receiverChainToChainRec rc' ∈ (sessionToRecordRec s).current.receiverChains := by
      simp only [sessionToRecordRec, sessionToSessionRec]; exact List.mem_map_of_mem hrc_old
    have hk_old : (mk.counter, mk.seed) ∈ (receiverChainToChainRec rc').messageKeys := by
      simp only [receiverChainToChainRec, List.mem_map]; exact ⟨mk, hmk, rfl⟩
    obtain ⟨pk_k, rIdx_k, srcIdx_k, skIdx_k, seed_k, hlog, hsu, hru, hgam, hlink, hfind_old⟩ :=
      hrsiSk _ hc_old _ hk_old
    have hlt_tr : skIdx_k < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := TREntry) tr skIdx_k
      have hlog' := hlog
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog'
      rw [hlog'] at this; exact this
    have hlt_pre : skIdx_k < tr_pre.length := by
      simp only [tr_pre, decRatchetPreTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega
    have hlog_pre : tr_pre.EventLoggedAt
        (TREvent.SkippedKeyStored (st1.sessionInfo p) pk_k (UInt32.ofBitVec mk.counter) seed_k rIdx_k
          srcIdx_k) skIdx_k := by
      rw [hsinfo]; dsimp only [tr_pre]
      rw [a2b_eventLoggedAt_decRatchetPreTr_lt _ _ _ _ _ hlt_tr]
      exact hlog
    have hsu_pre : !skippedKeyUsedB tr_pre skIdx_k := by
      dsimp only [tr_pre]
      rw [a2b_skippedKeyUsedB_decRatchetPreTr]
      exact hsu
    have hru_pre : !receiverKeyUsedB tr_pre (st1.sessionInfo p) seed_k (UInt32.ofBitVec mk.counter)
        rIdx_k := by
      rw [hsinfo]; dsimp only [tr_pre]
      rw [a2b_receiverKeyUsedB_decRatchetPreTr]
      exact hru
    have hne_cnt : ¬ (seed = seed_k ∧ msg.counter = UInt32.ofBitVec mk.counter ∧ c.rIdx = rIdx_k) :=
      Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.not_consumed_of_skippedKeyStored_gt_rIdx_tr hF hgt_rIdx hlog
    obtain ⟨hlog_post, hsu_post, hru_post⟩ :=
      a2b_hsk'_decTailTr_of_pre_tr hlog_pre hsu_pre hru_pre hlt_pre hne_cnt
    rw [hsinfo] at hlog_post hru_post
    exact ⟨pk_k, rIdx_k, srcIdx_k, skIdx_k, seed_k, hlog_post, hsu_post, hru_post, hgam, hlink,
      a2b_findRecvChain_trDhRatchetState_old_isSome hrel hnd hrc_r1 hne_new hlink hfind_old⟩

/-- Preserves `PureTRRecordStateInv` and `TRNsBound` across a DH-ratchet `Move.decrypt` in an
accepting block `rcvAccBlk body [.rng rngBytes] r`. -/
theorem a2b_tieB_ratchet_of_block
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (hik : IkShape interpretation r₀)
    (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc : List MachineEvent) (sent : List HwBytes)
    (p : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (rec body rngBytes : HwBytes) (r : StateAndMessage)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (rcvAccBlk body [.rng rngBytes] r))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r₀ (ms₀ ++ pre))
        (.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped) = some t →
      ¬ RecvCollision interpretation r₀ S g (ms₀ ++ pre) t)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body
      (.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped))
    (hrr : PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g (ms₀ ++ pre)
      (fun q => if q = p then some rec else none))
    (hns : TRNsBound r₀ (ms₀ ++ pre) sent)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r₀ S g (ms₀ ++ pre))
    (hABS' : Symbolic.Swarm.CREF.TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g (ms₀ ++ pre))
    (g_rw : RecvWireGhost) (m : SignalMessage)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hstate_lt : r.state.length < 2 ^ 64)
    (hcanon' : r.state.length < 2 ^ 32 - 2 ^ 20 → (pureTrSlots r₀).canon p r.state)
    (hwho : g_rw.who = if p = r₀.alice then 0 else 1)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q
      Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (hrng_len : rngBytes.length = 32)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc_none : ∀ rc ∈ g_rw.sess.state.receiverChains, rc.senderRatchetKey ≠ m.senderRatchetKey)
    (hcoins_ok : Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.PureDecryptCoinsOk
      (cryptoOf' interpretation) g_rw.sess.state m.senderRatchetKey
      (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)))
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureEvalRecvWireWithCoinsW
        (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw
        (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)) = some (r.state, r.message)) :
    PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = p then some r.state else none) ∧
      TRNsBound r₀ (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) sent := by
  let ms := ms₀ ++ pre
  have hmatch := a2b_block_vis hB hpre hpost
  have hrng_blk : .rng rngBytes ∈ rcvAccBlk body [.rng rngBytes] r := by
    simp [rcvAccBlk]
  have hacc_blk : ∃ e ∈ rcvAccBlk body [.rng rngBytes] r, eventKind e = .accept :=
    ⟨.accept r.message, by simp [rcvAccBlk], rfl⟩
  obtain ⟨hRng, st, t, msg, c', seed, spqr', key, pqSalt, ptTerm,
      hst, hmsg, hparse, hver, hfind, hlow, hcons, hspqr, hpqSalt, hmac_eq, hdec, _hpt⟩ :=
    ratchet_of_matched hmatch hrng_blk hacc_blk
  have hreach : (runTraceMoves r₀ ms).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 ms.length
    rwa [← List.append_assoc, List.take_left] at h
  have hrun : ModelRun r₀ ms := by
    have h := hB.run
    rw [← List.append_assoc] at h
    exact modelRun_prefix_of_reachable h hreach
  have hrep : t ∈ recvRepresentations interpretation r₀ S g ms body := hcurR.2 t hmsg
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrr p rec (by simp)
  have hidx : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hnorm_eq : normPending rec₀ = normPending (sessionToRecordRecPending g_rw.sess) :=
    Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains =
      (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff]; change StateRel interpretation S g st (normPending (sessionToRecordRecPending g_rw.sess)); rw [← hnorm_eq, stateRel_normPending_iff]; exact hrel₀
  have hsk_pre_sess : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains,
      ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r₀ ms).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        !skippedKeyUsedB (runTraceMoves r₀ ms) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r₀ ms) (st.sessionInfo p) seed (UInt32.ofBitVec k.1) rIdx ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain st.toDRState.recv pk).isSome = true :=
    hrc_rec₀ ▸ hsk_pre₀
  have hnd_sess : RecordChainsWF3 (sessionToRecordRec g_rw.sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  obtain ⟨role, remIk, ck, ck_adv, ck_next, r1, r_adv, r2, mkGen, st',
      _hRole, _hVer, _hRem, hFind, hDh, hNotLt, hJump, hAdv, hNext, hSet,
      _hMkGen, _hMac, _hDec, hSt', hr_enc⟩ :=
    a2b_evalRecvWireWithCoinsW_ratchetDH_inv interpretation body rngBytes r g_rw m
      newPqrState pqrKey hwire htry hrc_none hrecv_spqr heval
  let s' : Session (List (BitVec 8)) :=
    { g_rw.sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  obtain ⟨_, _, hpq_sess, _, _, _hver_sess, _⟩ :=
    Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure
      interpretation S g rec rec₀ st st g_rw hrecBytes₀ hrel₀ hcanon_q rfl
  have hspqr'_eq : spqr' =
      ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvState.SubF DY.Bytes).pack :=
    DY.Spqr.spqrRecv_state _ _ _ _ hspqr
  have hspqr'_gam : gamma interpretation S g spqr' = newPqrState := by
    rw [hspqr'_eq]
    exact (spqrRecv_step_gamma_state_and_key interpretation hceh r₀ S hS g ms body st g_rw t msg m
      newPqrState pqrKey hpq_sess hrep hparse htry hrecv_spqr).1
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld m htry
  have hTheir' : m.senderRatchetKey.bytes.toList = gamma interpretation S g msg.ratchetKey :=
    hrk_m.symm
  have hPkLen : (gamma interpretation S g msg.ratchetKey).length = 32 :=
    hTheir' ▸ m.senderRatchetKey.bytes.2
  have hTheir : m.senderRatchetKey = ⟨vec32 (gamma interpretation S g msg.ratchetKey)⟩ := by
    cases hmk : m.senderRatchetKey with | mk b =>
    have hb : b.toList = (vec32 (gamma interpretation S g msg.ratchetKey)).toList := by
      rw [hmk] at hTheir'; exact hTheir'.trans (vec32_toList_of_length_eq_tr hPkLen).symm
    exact congrArg PublicKey.mk (Subtype.ext hb)
  have hctr_eq : UInt32.ofBitVec m.counter = msg.counter := UInt32.ext hctr_m.symm
  have hst_rci : TrStateRkCkIk r₀ st := trStateRkCkIk_of_getLocalState hrun hst₀
  have hRkLen : (gamma interpretation S g st.rk).length = 32 :=
    hst_rci.rk_len interpretation S g hwf hB.pre.1
  have hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32 :=
    hst_rci.recv_ck_len interpretation S g hwf hB.pre.1
  have hJump' : (m.counter - ck.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps := by
    obtain ⟨_, _, _, _, _, _, _, hr1⟩ := Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
    rw [hr1] at hJump; exact hJump
  obtain ⟨_hfind₀, mks', seed₀, c₀', hcons₀_bv, _hSeedEq, _hCntEq,
      _hc'_rk, _hc'_rIdx, _hc_idx0, _hc_rIdx, hR2Eq', hRel_c, hRcMem, hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_dhRatchetStep_tr interpretation S g hceh (hrel := hrel_sess)
      (hRkLen := hRkLen) (hDhsLen := hks₀.1) (hCkLens := hCkLens) (hTheir := hTheir) (hPkLen := hPkLen)
      (hRng := hRng) (hRngLen := hrng_len) (hspqr' := hspqr'_gam)
      (hFindNone := hFind) (hStep := hDh)
      (hNotLt := hNotLt) (hJump := hJump') (hAdv := hAdv) (hNext := hNext) (hSet := hSet)
  have hcons_eq : some (seed₀, c₀') = some (seed, c') :=
    hcons₀_bv.symm.trans (hctr_eq ▸ hcons)
  injection hcons_eq with hpair_eq; injection hpair_eq with hseed_eq hc'_eq
  cases hseed_eq; cases hc'_eq
  have hnew : r.state = recordBytes (sessionToRecordRec s') := by
    have hst_lt : (CryptoVerification.E2E.Record.encodeRecord ⟨some s'⟩).length < 2 ^ 64 :=
      hr_enc ▸ hstate_lt
    have hsess'_len : (CryptoVerification.E2E.Record.encSession s').length < 2 ^ 64 := by
      have hle : (CryptoVerification.E2E.Record.encSession s').length ≤
          (CryptoVerification.E2E.Record.encodeRecord ⟨some s'⟩).length := by
        unfold CryptoVerification.E2E.Record.encodeRecord
        dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
          CryptoVerification.E2E.Record.lenField]
        simp only [List.length_append]; omega
      omega
    have hpq'_len : s'.state.pqRatchetState.length < 2 ^ 64 := by
      have h15 : s'.state.pqRatchetState.length ≤
          (CryptoVerification.E2E.Record.bytesField 15 s'.state.pqRatchetState).length := by
        unfold CryptoVerification.E2E.Record.bytesField CryptoVerification.E2E.Record.lenField
        by_cases h : s'.state.pqRatchetState = []
        · rw [h]; simp
        · simp only [h, ↓reduceIte, List.length_append]; omega
      have hle : (CryptoVerification.E2E.Record.bytesField 15 s'.state.pqRatchetState).length ≤
          (CryptoVerification.E2E.Record.encSession s').length := by
        unfold CryptoVerification.E2E.Record.encSession
        simp only [List.length_append]; omega
      omega
    obtain ⟨_, _, ⟨_, _, hchains_sc, _, _, _, _⟩⟩ := hcanon_q
    have hseeds : ∀ rc0 ∈ g_rw.sess.state.receiverChains, ∀ mk ∈ rc0.messageKeys,
        mk.seed.length < 2 ^ 63 := by
      intro rc0 hrc0 mk hmk; have h32 := (hchains_sc rc0 hrc0).2 mk hmk; omega
    have hseeds' : ∀ rc' ∈ s'.state.receiverChains, ∀ mk ∈ rc'.messageKeys,
        mk.seed.length < 2 ^ 63 := by
      intro rc' hrc' mk hmk
      rcases hRcMem rc' (by simpa [s', hSt'] using hrc') with hrc_old | rfl
      · exact hseeds rc' hrc_old mk hmk
      · obtain ⟨_, _, _, _, _, _, hlen32⟩ := hMks' mk hmk; omega
    have heq_rec : sessionToRecordRec s' = SendRetCoins.sessionToRecordRecPending s' := rfl
    rw [hr_enc, heq_rec, recordBytes_sessionToRecordRecPending_eq_encodeRecord_64 s'
      (by dsimp only [s']; omega) hpq'_len hseeds' hsess'_len]
  have hrel' : StateRel interpretation S g
      { (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1 with
        recv := setRecvChain (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.recv c',
        spqr := spqr' }
      (sessionToRecordRec s') := by
    dsimp only [s']; rw [hSt']; exact hRel_c
  have hR1Rc : r1.receiverChains =
      RatchetState.evictReceiverChains
        (g_rw.sess.state.receiverChains ++ [⟨m.senderRatchetKey, some ck, []⟩]) :=
    (dhRatchetStep_ok_eq_gamma_trDhRatchetState interpretation S g hceh (hrel := hrel_sess)
      (hRkLen := hRkLen) (hDhsLen := hks₀.1) (hCkLens := hCkLens) (hTheir := hTheir) (hPkLen := hPkLen)
      (hRng := hRng) (hRngLen := hrng_len) (hStep := hDh)).2.2.2.2.2.2.2.2.2.1
  have hMks'_c : ∀ k ∈ mks',
      ∃ j < msg.counter.toNat,
        k.counter = BitVec.ofNat 32 j ∧ UInt32.ofBitVec k.counter = UInt32.ofNat j ∧
        UInt32.ofBitVec k.counter ≠ msg.counter ∧
        k.seed = gamma interpretation S g
          (kdfCk (chainKeyAt
            (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2.chainKey j)).2 ∧
        k.seed.length = 32 := by
    intro k hk
    obtain ⟨j, hj, hk1, hk2, hk3, hk4, hk5⟩ := hMks' k hk
    have hj' : j < msg.counter.toNat := by
      change j < (UInt32.ofBitVec m.counter).toNat - 0 at hj
      rw [Nat.sub_zero, hctr_eq] at hj; exact hj
    have hk1' : k.counter = BitVec.ofNat 32 j :=
      hk1.trans (BitVec.zero_add (BitVec.ofNat 32 j))
    have hk2' : UInt32.ofBitVec k.counter = UInt32.ofNat j :=
      hk2.trans (UInt32.zero_add (UInt32.ofNat j))
    exact ⟨j, hj', hk1', hk2', hctr_eq ▸ hk3, hk4, hk5⟩
  have hFresh : TRRecvCountersFresh (runTraceMoves r₀ ms) p st :=
    (hat.fresh p stateIdx st hp_mem hst₀ hcur₀).1
  have htr := a2b_runTrace_decrypt_ratchet (wrapped := wrapped)
    hst₀ hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec
  have hs'_rc : s'.state.receiverChains = r2.receiverChains := by
    change st'.receiverChains = r2.receiverChains; rw [hSt']
  have hsk' := a2b_skippedOk_ratchet_decTail hreach hFresh htr hrel_sess hnd_sess.1 hsk_pre_sess hTheir' hR1Rc
    (congrArg RatchetState.receiverChains hR2Eq') hMks'_c hs'_rc
  have hnd' : RecordChainsWF3 (sessionToRecordRec s') :=
    nodup_and_lt_of_dhRatchetStep_tr hFind hDh hNotLt hAdv hNext hSet hs'_rc hnd_sess
  have hRngLen_g : (g.σ (runTraceMoves r₀ ms).length 32).length = 32 := hRng.symm ▸ hrng_len
  exact ⟨a2b_trRecordStateInv_decRatchet_single hp_mem htr hnew hrel' hsk' hcanon' hks₀
      hRngLen_g hnd',
    a2b_trNsBound_decRatchet hns htr⟩

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
