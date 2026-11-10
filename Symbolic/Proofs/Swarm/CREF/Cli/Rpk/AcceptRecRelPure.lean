/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieRec
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvFreshLinkPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Trace Lemmas for Bob's Pre-Key Session Start

Expresses `bobStartTr` as `decTailTr` over `bobStartPreSkipTr`, establishes skipped-key and
receiver-key freshness properties across `bobStartTr`, and reduces `PureTRRecordStateInv` for a
`bobStart` move to `RpkRecRel` and `TRKeyShape`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (skippedKeyUsedB receiverKeyUsedB)
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep (decTailTr)

/-- Reduces `PureTRRecordStateInv` for Bob's singleton record after a `bobStart` move to
`RpkRecRel` and `TRKeyShape` on `rpkR_finalSt`. -/
theorem rpkR_pureTieRec_reduce {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {Z : TR.PureTRSlots} {g : Ghost} {ms : List Move} {m : Move} {bytes : HwBytes}
    (hbs : BobStartBy r.bob m)
    (hcanon : bytes.length < 2 ^ 32 - 2 ^ 20 → Z.canon r.bob bytes)
    (hcore : ∀ a kh regA mh pqIdx spqrMsgIdx shown,
      m = .bobStart r.bob a kh regA mh pqIdx spqrMsgIdx shown →
      ∃ w : BobStartOk (runTraceMoves r ms) r.bob a kh regA mh pqIdx spqrMsgIdx,
        RpkRecRel interpretation S g (runTraceMoves r (ms ++ [m])) r.bob (rpkR_finalSt w) bytes ∧
        TR.TRKeyShape interpretation S g (rpkR_finalSt w)) :
    TR.PureTRRecordStateInv interpretation r S Z g (ms ++ [m])
      (fun q => if q = r.bob then some bytes else none) := by
  cases m with
  | bobStart p a kh regA mh pqIdx spqrMsgIdx shown =>
    have hp : p = r.bob := hbs; subst hp
    obtain ⟨w, ⟨rec, hb, hrel, hsk, hnd⟩, hks⟩ := hcore a kh regA mh pqIdx spqrMsgIdx shown rfl
    intro q b' hq
    by_cases hqb : q = r.bob
    · subst hqb; simp only [ite_true] at hq; cases hq
      obtain ⟨stateIdx, hget, hcur⟩ := rpkR_final_current (shown := shown) w
      exact ⟨Or.inr rfl, rec, rpkR_finalSt w, stateIdx, hb, hget, hcur, hrel, hsk, hcanon, hks, hnd⟩
    · simp only [hqb, ite_false] at hq; cases hq
  | _ => exact False.elim hbs

private theorem rpkRR_logSkippedKeysTr_eq (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx sourceStateIdx : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    TR.RecvDec.logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr =
      TR.RecvDecStep.logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih =>
    unfold TR.RecvDec.logSkippedKeysTr TR.RecvDecStep.logSkippedKeysTr; exact ih _ _ _

/-- Rewrites `bobStartTr` as `decTailTr` applied to `bobStartPreSkipTr` and Bob's ratcheted
session state. -/
theorem rpkRR_bobStartTr_eq (tr : ExecTrace) (b a : Participant) (o : PQXDH.BobHandshakeOut)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) (c' : DY.Libsignal.TripleRatchet.RecvChain)
    (spqr' key seed pqSalt m : DY.Bytes) :
    let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey (randTerm tr.length 32)
    let c := bobRatchetedChain o.keys msg.ratchetKey o.spkSk
    let tr_hs := bobStartPreSkipTr tr b a o msg key
    bobStartTr tr b a o msg c' spqr' key seed pqSalt m =
      decTailTr tr_hs b (tr_hs.length + (msg.counter.toNat - c.index.toNat) + 2) st c c'
        msg.ratchetKey seed pqSalt m spqr' msg.counter := by
  intro st c tr_hs
  unfold bobStartTr decTailTr
  dsimp only
  rw [(TR.RecvDec.logSkippedKeys_run _ _ _ _ _ _ _ _).2, rpkRR_logSkippedKeysTr_eq]

open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep in
theorem rpkRR_skippedKeyUsedB_preSkip (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) (k : Nat) :
    skippedKeyUsedB (bobStartPreSkipTr tr b a o msg key) k = skippedKeyUsedB tr k := by
  unfold bobStartPreSkipTr
  dsimp only
  rw [skippedKeyUsedB_append_non_tr_a2 _ _ rfl,
    skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h),
    skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h),
    skippedKeyUsedB_append_non_tr_a2 _ _ rfl]
  cases o.opk with
  | none =>
    dsimp only
    rw [skippedKeyUsedB_append_non_tr_a2 _ _ rfl, skippedKeyUsedB_append_non_tr_a2 _ _ rfl]
  | some opkPk =>
    dsimp only
    rw [skippedKeyUsedB_append_non_tr_a2 _ _ rfl, skippedKeyUsedB_append_non_tr_a2 _ _ rfl,
      skippedKeyUsedB_append_non_tr_a2 _ _ rfl]

open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep in
theorem rpkRR_receiverKeyUsedB_preSkip (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) (s : DY.Libsignal.TripleRatchet.SessionInfo) (seed : DY.Bytes) (n : UInt32)
    (rIdx : Nat) :
    receiverKeyUsedB (bobStartPreSkipTr tr b a o msg key) s seed n rIdx =
      receiverKeyUsedB tr s seed n rIdx := by
  unfold bobStartPreSkipTr
  dsimp only
  rw [receiverKeyUsedB_append_non_tr_a2 _ _ rfl,
    receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h),
    receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h),
    receiverKeyUsedB_append_non_tr_a2 _ _ rfl]
  cases o.opk with
  | none =>
    dsimp only
    rw [receiverKeyUsedB_append_non_tr_a2 _ _ rfl, receiverKeyUsedB_append_non_tr_a2 _ _ rfl]
  | some opkPk =>
    dsimp only
    rw [receiverKeyUsedB_append_non_tr_a2 _ _ rfl, receiverKeyUsedB_append_non_tr_a2 _ _ rfl,
      receiverKeyUsedB_append_non_tr_a2 _ _ rfl]

theorem rpkRR_length_preSkip (tr : ExecTrace) (b a : Participant)
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

open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep in
theorem rpkRR_skippedKeyUsedB_bobStartTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes) (k : Nat) :
    skippedKeyUsedB (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) k =
      skippedKeyUsedB tr k := by
  rw [rpkRR_bobStartTr_eq, skippedKeyUsedB_decTailTr, rpkRR_skippedKeyUsedB_preSkip]

open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep in
theorem rpkRR_receiverKeyUsedB_bobStartTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes)
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (seed' : DY.Bytes) (n : UInt32) (rIdx : Nat) :
    receiverKeyUsedB (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) s seed' n rIdx =
      (receiverKeyUsedB tr s seed' n rIdx ||
        decide ((bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey
            (randTerm tr.length 32)).sessionInfo b = s ∧
          seed = seed' ∧ msg.counter = n ∧ 2 = rIdx)) := by
  rw [rpkRR_bobStartTr_eq, receiverKeyUsedB_decTailTr, rpkRR_receiverKeyUsedB_preSkip]
  rfl

open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep in
theorem rpkRR_skipped_logged (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes)
    {j : Nat} (hj : j < msg.counter.toNat) :
    let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey (randTerm tr.length 32)
    let c := bobRatchetedChain o.keys msg.ratchetKey o.spkSk
    let tr_hs := bobStartPreSkipTr tr b a o msg key
    (bobStartTr tr b a o msg c' spqr' key seed pqSalt m).EventLoggedAt
      (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored (st.sessionInfo b) msg.ratchetKey
        (UInt32.ofNat j) (DY.Libsignal.TripleRatchet.kdfCk
          (DY.Libsignal.TripleRatchet.chainKeyAt c.chainKey j)).2 2
        (tr_hs.length + msg.counter.toNat + 2))
      (tr_hs.length + j) := by
  intro st c tr_hs
  rw [rpkRR_bobStartTr_eq]
  have h := hsk'_decTailTr_of_new_exact_tr tr_hs b
    (tr_hs.length + (msg.counter.toNat - c.index.toNat) + 2) st c c' msg.ratchetKey seed pqSalt m
    spqr' msg.counter (j := j) (by simpa [c, bobRatchetedChain] using hj)
  simpa [c, bobRatchetedChain] using h

open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep in
theorem rpkRR_skipped_T3 (tr : ExecTrace) (hreach : tr.Reachable reachability)
    (b a : Participant) (o : PQXDH.BobHandshakeOut)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes)
    {j : Nat} (hj : j < msg.counter.toNat) :
    let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey (randTerm tr.length 32)
    let c := bobRatchetedChain o.keys msg.ratchetKey o.spkSk
    let tr_hs := bobStartPreSkipTr tr b a o msg key
    let seedj := (DY.Libsignal.TripleRatchet.kdfCk
      (DY.Libsignal.TripleRatchet.chainKeyAt c.chainKey j)).2
    let trF := bobStartTr tr b a o msg c' spqr' key seed pqSalt m
    receiverKeyUsedB tr (st.sessionInfo b) seedj (UInt32.ofNat j) 2 = false →
    trF.EventLoggedAt
        (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored (st.sessionInfo b) msg.ratchetKey
          (UInt32.ofNat j) seedj 2 (tr_hs.length + msg.counter.toNat + 2))
        (tr_hs.length + j) ∧
      skippedKeyUsedB trF (tr_hs.length + j) = false ∧
      receiverKeyUsedB trF (st.sessionInfo b) seedj (UInt32.ofNat j) 2 = false := by
  intro st c tr_hs seedj trF hfresh
  refine ⟨rpkRR_skipped_logged tr b a o msg c' spqr' key seed pqSalt m hj, ?_, ?_⟩
  · show skippedKeyUsedB (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) _ = false
    rw [rpkRR_skippedKeyUsedB_bobStartTr]
    exact TR.skippedKeyUsedB_of_ge_length_tr hreach
      (Nat.le_trans (rpkRR_length_preSkip tr b a o msg key) (Nat.le_add_right _ _))
  · show receiverKeyUsedB (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) _ _ _ _ = false
    rw [rpkRR_receiverKeyUsedB_bobStartTr, hfresh, Bool.false_or, decide_eq_false_iff_not]
    rintro ⟨-, -, hcnt, -⟩
    have h1 : msg.counter.toNat = (UInt32.ofNat j).toNat := congrArg UInt32.toNat hcnt
    have h2 : (UInt32.ofNat j).toNat = j % 2 ^ 32 := UInt32.toNat_ofNat
    have h3 : msg.counter.toNat < 2 ^ 32 := msg.counter.toNat_lt
    omega

theorem rpkRR_skipped_T3_run {r : ProtocolSetup} {ms : List Move} {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat}
    {spqrMsgIdx : UInt32} (shown : Nat)
    (w : BobStartOk (runTraceMoves r ms) b a kh regA mh pqIdx spqrMsgIdx)
    (hreach : (runTraceMoves r ms).Reachable reachability) {j : Nat} (hj : j < w.msg.counter.toNat) :
    let seedj := (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt
      (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey j)).2
    let trF := runTraceMoves r (ms ++ [.bobStart b a kh regA mh pqIdx spqrMsgIdx shown])
    receiverKeyUsedB (runTraceMoves r ms) ((rpkR_finalSt w).sessionInfo b) seedj (UInt32.ofNat j) 2 = false →
    ∃ skIdx srcIdx,
      trF.EventLoggedAt
          (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored ((rpkR_finalSt w).sessionInfo b)
            w.msg.ratchetKey (UInt32.ofNat j) seedj 2 srcIdx) skIdx ∧
        skippedKeyUsedB trF skIdx = false ∧
        receiverKeyUsedB trF ((rpkR_finalSt w).sessionInfo b) seedj (UInt32.ofNat j) 2 = false := by
  intro seedj trF hfresh
  have h := rpkRR_skipped_T3 (runTraceMoves r ms) hreach b a w.out w.msg w.c' w.spqr' w.key w.seed
    w.pqSalt w.m hj hfresh
  have htr : trF = bobStartTr (runTraceMoves r ms) b a w.out w.msg w.c' w.spqr' w.key w.seed
      w.pqSalt w.m := by
    show runTraceMoves r (ms ++ [_]) = _
    rw [TR.runTrace_snoc, w.next_eq]
  rw [htr]
  exact ⟨_, _, h⟩

end Symbolic.Swarm.CREF.CliPure
