/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvFreshLinkPureA
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
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHProvPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.TRREF.B3DefsPure -- shake: keep
import Symbolic.Proofs.SR.RecvSpecWPure -- shake: keep
import Symbolic.Proofs.Refinement.RngFree.SendSpecPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# DH-Ratchet Decrypt Step Lemmas at General Traces

Characterizes the post-move trace for a DH-ratchet `decrypt` move at an arbitrary
`runTraceMoves r₀ ms`, and establishes `TRNsBound`, singleton `PureTRRecordStateInv`, and
skipped-key preservation across `decRatchetPreTr` and `decTailTr`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr gamma_concat gamma_dhPk leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc uOf_leBytes uOf_lt

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.DiffieHellman DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain setRecvChain consumeMessageKey
  chainKeyAt kdfCk computeMac messageVersion x25519LowOrder)
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
open Proofs.libsignal.Refinement
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2 Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3

open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec
  receiverChainToChainRec)
open CryptoVerification.SessionModel.AdvanceAndFrame (mem_set_or)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState decRatchetPreTr decrypt_next_ratchet_eq
  trNsBound_of_append_stEntry)
open Symbolic.Swarm.CREF.TR.Pure

private theorem a2b_skippedKeyUsedB_decRatchetPreTr
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes) (skIdx : Nat) :
    skippedKeyUsedB (decRatchetPreTr tr me st1 pk key) skIdx = skippedKeyUsedB tr skIdx := by
  unfold decRatchetPreTr
  rw [skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h),
      skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h),
      skippedKeyUsedB_append_non_tr_a2 _ _ rfl,
      skippedKeyUsedB_append_non_tr_a2 _ _ rfl]

private theorem a2b_receiverKeyUsedB_decRatchetPreTr
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes)
    (s' : SessionInfo) (seed' : DY.Bytes) (cnt' : UInt32) (rIdx' : Nat) :
    receiverKeyUsedB (decRatchetPreTr tr me st1 pk key) s' seed' cnt' rIdx' =
      receiverKeyUsedB tr s' seed' cnt' rIdx' := by
  unfold decRatchetPreTr
  rw [receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h),
      receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h),
      receiverKeyUsedB_append_non_tr_a2 _ _ rfl,
      receiverKeyUsedB_append_non_tr_a2 _ _ rfl]

private theorem a2b_eventLoggedAt_decRatchetPreTr_lt
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes)
    {ev : TREvent} {i : Nat} (hi : i < tr.length) :
    (decRatchetPreTr tr me st1 pk key).EventLoggedAt ev i ↔ tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  unfold decRatchetPreTr
  rw [at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl]

private theorem a2b_hsk'_decTailTr_of_pre_tr
    {tr_pre : ExecTrace} {me : Participant} {stateIdx : Nat}
    {st1 : TRState} {c c' : RecvChain} {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {pk_k seed_k : DY.Bytes} {n_k : UInt32} {rIdx_k srcIdx_k skIdx_k : Nat}
    (hlog_pre : tr_pre.EventLoggedAt
      (TREvent.SkippedKeyStored (st1.sessionInfo me) pk_k n_k seed_k rIdx_k srcIdx_k) skIdx_k)
    (hsu_pre : !skippedKeyUsedB tr_pre skIdx_k)
    (hru_pre : !receiverKeyUsedB tr_pre (st1.sessionInfo me) seed_k n_k rIdx_k)
    (hlt_pre : skIdx_k < tr_pre.length)
    (hne_cnt : ¬ (seed = seed_k ∧ n = n_k ∧ c.rIdx = rIdx_k)) :
    (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.SkippedKeyStored (st1.sessionInfo me) pk_k n_k seed_k rIdx_k srcIdx_k) skIdx_k ∧
    !skippedKeyUsedB (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) skIdx_k ∧
    !receiverKeyUsedB (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n)
      (st1.sessionInfo me) seed_k n_k rIdx_k := by
  refine ⟨?_, ?_, ?_⟩
  · rw [eventLoggedAt_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ hlt_pre]; exact hlog_pre
  · rw [skippedKeyUsedB_decTailTr]; exact hsu_pre
  · rw [receiverKeyUsedB_decTailTr]
    have hfalse : decide (st1.sessionInfo me = st1.sessionInfo me ∧ seed = seed_k ∧ n = n_k ∧ c.rIdx = rIdx_k) = false := by
      simp [hne_cnt]
    rw [hfalse, Bool.or_false]; exact hru_pre

theorem a2b_runTrace_decrypt_ratchet
    {r₀ : ProtocolSetup} {ms : List Move} {p : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {wrapped : Bool}
    {st : TRState} {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c' : RecvChain}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2
      msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.spqr
      msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((((runTraceMoves r₀ ms).append (⟨32⟩ : DY.Random.ExecEntryT)).append
      (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.peerIk
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm) :
    let st1 := (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1
    let c := (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2
    runTraceMoves r₀ (ms ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) =
      decTailTr (decRatchetPreTr (runTraceMoves r₀ ms) p st1 msg.ratchetKey key) p stateIdx st1 c c'
        msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
  dsimp only
  rw [runTrace_snoc, ← decTailTr_eq_recvDec]
  exact decrypt_next_ratchet_eq hst hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec

private theorem a2b_at?_stEntry_decRatchetPreTr
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes) (i : Nat) :
    ((decRatchetPreTr tr me st1 pk key).at? i : Option StEntry) = (tr.at? i : Option StEntry) := by
  unfold decRatchetPreTr
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl]

theorem a2b_trNsBound_decRatchet
    {r₀ : ProtocolSetup} {ms : List Move} {sent : List HwBytes} {m : Move}
    {p : Participant} {stateIdx : Nat} {st : TRState}
    {key seed pqSalt ptTerm spqr' pk : DY.Bytes} {c' : RecvChain} {n : UInt32}
    (hns : TRNsBound r₀ ms sent)
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      decTailTr
        (decRatchetPreTr (runTraceMoves r₀ ms) p
          (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1 pk key)
        p stateIdx
        (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1
        (trDhRatchetState st pk (runTraceMoves r₀ ms).length).2
        c' pk seed pqSalt ptTerm spqr' n) :
    TRNsBound r₀ (ms ++ [m]) sent := by
  let tr₀ := runTraceMoves r₀ ms
  let st1 := (trDhRatchetState st pk tr₀.length).1
  let c := (trDhRatchetState st pk tr₀.length).2
  let tr_pre := decRatchetPreTr tr₀ p st1 pk key
  let tr_sk := logSkippedKeysTr (st1.sessionInfo p) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  let tr_rcv := tr_sk.append (⟨TREvent.Received p st1.peer pk n ptTerm⟩ : TREntry)
  let tr_mid := tr_rcv.append (⟨TREvent.MessageKey (st1.sessionInfo p) .receiver seed pqSalt
    n c.rIdx stateIdx⟩ : TREntry)
  have htr' : runTraceMoves r₀ (ms ++ [m]) =
      tr_mid.append (⟨⟨p, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : StEntry) := by
    rw [htr]; rfl
  refine trNsBound_of_append_stEntry (tr₀ := tr_mid) (me := p)
      (st' := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' })
    htr' (fun i => ?_) (Nat.zero_le sent.length) hns
  dsimp only [tr_mid, tr_rcv, tr_sk, tr_pre]
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_stEntry_logSkippedKeysTr, a2b_at?_stEntry_decRatchetPreTr]

/-- Establishes `PureTRRecordStateInv` for the singleton update assigning `newBytes` to `p`
after a DH-ratchet `decrypt` step. -/
theorem a2b_trRecordStateInv_decRatchet_single
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : SpqrSem} {Z : PureTRSlots}
    {g : Ghost} {ms : List Move} {m : Move}
    {p : Participant} {stateIdx : Nat} {st : TRState} {rec' : RecordRec} {newBytes : HwBytes}
    {key seed pqSalt ptTerm spqr' pk : DY.Bytes} {c' : RecvChain} {n : UInt32}
    (hp_mem : p = r₀.alice ∨ p = r₀.bob)
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      decTailTr
        (decRatchetPreTr (runTraceMoves r₀ ms) p
          (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1 pk key)
        p stateIdx
        (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1
        (trDhRatchetState st pk (runTraceMoves r₀ ms).length).2
        c' pk seed pqSalt ptTerm spqr' n)
    (hnew : newBytes = recordBytes rec')
    (hrel' : StateRel interpretation S g
      { (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1 with
        recv := setRecvChain (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1.recv c',
        spqr := spqr' }
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
        (findRecvChain
          { (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1 with
            recv := setRecvChain (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1.recv c',
            spqr := spqr' }.toDRState.recv pk_k).isSome = true)
    (hcanon' : newBytes.length < 2 ^ 32 - 2 ^ 20 → Z.canon p newBytes)
    (hks : TRKeyShape interpretation S g st)
    (hRngLen : (g.σ (runTraceMoves r₀ ms).length 32).length = 32)
    (hnd' : (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
      (∀ c_k ∈ rec'.current.receiverChains, (c_k.messageKeys.map Prod.fst).Nodup) ∧
      ∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys,
        ∃ ck, c_k.chainKey = some ck ∧ k.1 < ck.1) :
    PureTRRecordStateInv interpretation r₀ S Z g (ms ++ [m])
      (fun q => if q = p then some newBytes else none) := by
  let st1 := (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1
  let c := (trDhRatchetState st pk (runTraceMoves r₀ ms).length).2
  let tr_pre := decRatchetPreTr (runTraceMoves r₀ ms) p st1 pk key
  intro q b hqb
  by_cases hqp : q = p
  · subst hqp; simp only [↓reduceIte, Option.some.injEq] at hqb; subst hqb
    refine ⟨hp_mem, rec', { st1 with recv := setRecvChain st1.recv c', spqr := spqr' },
      tr_pre.length + (n.toNat - c.index.toNat) + 2, hnew, ?_, ?_, hrel', ?_, hcanon',
      trKeyShape_trDhRatchetState_recv_spqr interpretation S g hks hRngLen, hnd'⟩
    · rw [htr, getLocalState_decTailTr_last]
    · rw [htr, isCurrentSnapshot_decTailTr_last]
    · exact hsk'
  · simp only [hqp, ↓reduceIte] at hqb; cases hqb

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

/-- Preserves and extends the skipped-key invariant across a DH-ratchet `decrypt` move at
`runTraceMoves r₀ ms`. -/
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
  have hlen_pre : tr_pre.length = tr.length + 4 :=
    Symbolic.Swarm.CREF.TR.RecvDec.decRatchetPreTr_length tr p st1 msg.ratchetKey key
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
        rw [hlen_pre]; omega
      rw [skippedKeyUsedB_of_ge_length_tr hreach hge]; rfl
    · rw [← hsinfo, receiverKeyUsedB_decTailTr, hsinfo]
      have hne_ctr : ¬ (msg.counter = UInt32.ofBitVec mk.counter) := fun h => hjNe h.symm
      simp only [hne_ctr, false_and, and_false, decide_false, Bool.or_false]
      rw [a2b_receiverKeyUsedB_decRatchetPreTr,
          receiverKeyUsedB_false_of_gt_rIdx_tr hF hgt_rIdx]; rfl
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
      have hlog' := hlog
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog'
      have := Trace.at?_eq_some_implies_length_le (EntryT := TREntry) tr skIdx_k
      rw [hlog'] at this; exact this
    have hlt_pre : skIdx_k < tr_pre.length := by
      rw [hlen_pre]; omega
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
      not_consumed_of_skippedKeyStored_gt_rIdx_tr hF hgt_rIdx hlog
    obtain ⟨hlog_post, hsu_post, hru_post⟩ :=
      a2b_hsk'_decTailTr_of_pre_tr hlog_pre hsu_pre hru_pre hlt_pre hne_cnt
    rw [hsinfo] at hlog_post hru_post
    exact ⟨pk_k, rIdx_k, srcIdx_k, skIdx_k, seed_k, hlog_post, hsu_post, hru_post, hgam, hlink,
      a2b_findRecvChain_trDhRatchetState_old_isSome hrel hnd hrc_r1 hne_new hlink hfind_old⟩

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
