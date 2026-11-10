/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
public import Symbolic.Proofs.Refinement.RecordBytesBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Shared Receiver-Chain and Decrypt Trace Tail Definitions

Defines `logSkippedKeysTr`, `decTailTr`, and `modelRecvChainOfTr`, and proves foundational trace
indexing, `setRecvChain`, and `consumeMessageKey` lemmas for Triple Ratchet decrypt steps.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR

cref_open
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain setRecvChain consumeMessageKey
  chainKeyAt kdfCk maxForwardJumps u32Max)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)

abbrev SpqrSem := OpaqueSymbolSemantics

abbrev StEntry := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev TREntry := DY.ProtocolEvent.ExecEntryT TREvent

private theorem extractLsb'_zero_bytesToKey32_cons_tr (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons_tr (b : BitVec 8) (acc : BitVec 256) (j : Nat)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32_tr (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (CryptoGames.HKDF.bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [CryptoGames.HKDF.bytesToKey32] using
        extractLsb'_zero_bytesToKey32_cons_tr b (CryptoGames.HKDF.bytesToKey32 rest)
    | succ j =>
      have hcons : CryptoGames.HKDF.bytesToKey32 (b :: rest) =
          (CryptoGames.HKDF.bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons_tr b (CryptoGames.HKDF.bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem keyToBytes32_bytesToKey32_tr (bs : List (BitVec 8)) (h : bs.length = 32) :
    CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [CryptoGames.HMAC.keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [CryptoGames.HMAC.keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32_tr bs j h2 (by omega)

theorem length_hmacWith_tr (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState)
    (k m : List (BitVec 8)) :
    (CryptoGames.HMAC.hmacWith F k m).length = 32 := by
  unfold CryptoGames.HMAC.hmacWith CryptoGames.HMAC.sha256With
  generalize (CryptoGames.HMAC.chunks64 (CryptoGames.HMAC.sha256Pad _)).foldl F CryptoGames.HMAC.sha256IV = s
  rcases s with ⟨l, hl⟩
  simp [CryptoGames.HMAC.toBEBytes, List.length_flatMap, hl]

theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem getLocalState_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option StEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1, _root_.guard]
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only
    rw [Traceful.run_pure]
    dsimp only
    by_cases hp : p = me <;> simp [hp, run_bind_fst, Traceful.run_pure, Traceful.run_failure]

theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

theorem at?_eq_none_of_le {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) {i : Nat}
    (hi : tr.length ≤ i) : (tr.at? i : Option E) = none := by
  have h : ¬ i < tr.length := by omega
  simp only [Trace.at?, h, ↓reduceDIte]

theorem trace_snoc_at_length {Entry : Type} (tr : DY.Trace Entry) (x : Entry)
    (h : tr.length < (tr.snoc x).length) :
    (tr.snoc x).at tr.length h = x := by
  simp only [Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte]

theorem trace_append_at_length {Entry E1 : Type} [DY.TraceEntryHas E1 Entry]
    (tr : DY.Trace Entry) (e : E1) (h : tr.length < (tr.append e).length) :
    (tr.append e).at tr.length h = DY.TraceEntryHas.inj e := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1] at h ⊢
  exact trace_snoc_at_length tr (DY.TraceEntryHas.inj e) h

theorem at?_append_non_entry {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none)
    (i : Nat) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  by_cases hlt : i < tr.length
  · exact at?_append_of_lt tr e hlt
  · by_cases heq : i = tr.length
    · subst heq
      have h1 : tr.length < (tr.append e).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      have h2 : ¬ tr.length < tr.length := Nat.lt_irrefl _
      simp only [Trace.at?, h1, h2, ↓reduceDIte, trace_append_at_length, hnone]
    · rw [at?_eq_none_of_le (tr.append e) (by
            simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
          at?_eq_none_of_le tr (by omega)]

theorem isCurrentSnapshot_append_non_st {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    (stateIdx : Nat) :
    isCurrentSnapshot (tr.append e) stateIdx = isCurrentSnapshot tr stateIdx := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [at?_append_non_entry tr e hnone]
  rcases h : (tr.at? stateIdx : Option StEntry) with _ | s
  · rfl
  · dsimp only
    have hlen : (tr.append e).length - (stateIdx + 1) = (tr.length - (stateIdx + 1)) + 1 := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr stateIdx
      rw [h] at this
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
    have hsum : (stateIdx + 1) + 1 * (tr.length - (stateIdx + 1)) = tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr stateIdx
      rw [h] at this; omega
    have hlast : (tr.at? tr.length : Option StEntry) = none :=
      at?_eq_none_of_le tr (Nat.le_refl _)
    rw [hlen, List.range'_concat, hsum]
    simp only [List.all_append, List.all_cons, List.all_nil,
      at?_append_non_entry tr e hnone, hlast, Bool.and_true]

def logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat) :
    DY.Bytes → UInt32 → Nat → ExecTrace → ExecTrace
  | _, _, 0, tr => tr
  | ck, n, k + 1, tr =>
    logSkippedKeysTr s pk rIdx sourceStateIdx (kdfCk ck).1 (n + 1) k
      (tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : TREntry))

theorem logSkippedKeysTr_length (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    (logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).length = tr.length + k := by
  induction k generalizing ck n tr with
  | zero => exact (Nat.add_zero _).symm
  | succ k ih =>
    unfold logSkippedKeysTr; rw [ih]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega

theorem logSkippedKeysTr_le (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    tr ≤ logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero => exact Trace.le_refl tr
  | succ k ih =>
    unfold logSkippedKeysTr
    exact Trace.le_trans _ _ _ (Trace.append_le tr _) (ih (kdfCk ck).1 (n + 1) _)

theorem at?_stEntry_logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) (i : Nat) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? i : Option StEntry) =
      (tr.at? i : Option StEntry) := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih => unfold logSkippedKeysTr; rw [ih, at?_append_non_entry _ _ rfl]

theorem at?_trEntry_logSkippedKeysTr_lt (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) {i : Nat} (hi : i < tr.length) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? i : Option TREntry) =
      (tr.at? i : Option TREntry) := by
  have hle := logSkippedKeysTr_le s pk rIdx sourceStateIdx ck n k tr
  have hi' : i < (logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).length :=
    Nat.lt_of_lt_of_le hi (Trace.length_le _ _ hle)
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le _ _ i hi hle]

theorem at?_trEntry_logSkippedKeysTr_add (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) {j : Nat} (hj : j < k) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? (tr.length + j) : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored s pk (n + UInt32.ofNat j) (kdfCk (chainKeyAt ck j)).2 rIdx sourceStateIdx⟩ := by
  induction k generalizing ck n tr j with
  | zero => omega
  | succ k ih =>
    unfold logSkippedKeysTr
    cases j with
    | zero =>
      rw [Nat.add_zero]
      rw [at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _
        (show tr.length < (tr.append _).length by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)]
      rw [Trace.at?_append]
      have hn : n + UInt32.ofNat 0 = n := UInt32.add_zero n
      rw [hn]; rfl
    | succ j' =>
      have hj' : j' < k := by omega
      have hlen : tr.length + (j' + 1) =
          (tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : TREntry)).length + j' := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      rw [hlen, ih (kdfCk ck).1 (n + 1) _ hj']
      have hn : (n + 1) + UInt32.ofNat j' = n + UInt32.ofNat (j' + 1) := by
        apply UInt32.eq_of_toBitVec_eq
        change n.toBitVec + 1#32 + BitVec.ofNat 32 j' = n.toBitVec + BitVec.ofNat 32 (j' + 1)
        rw [BitVec.ofNat_add]; ac_rfl
      rw [hn]; rfl

def decTailTr (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) : ExecTrace :=
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  let tr_rcv := tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)
  (tr_rcv.append
    (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx⟩ : TREntry)).append
    (⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : StEntry)

theorem decTailTr_length (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).length =
      tr_pre.length + (n.toNat - c.index.toNat) + 3 := by
  unfold decTailTr; dsimp only
  have hlen := logSkippedKeysTr_length (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega

theorem at?_trEntry_decTailTr_lt (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) {i : Nat} (hi : i < tr_pre.length) :
    ((decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).at? i : Option TREntry) =
      (tr_pre.at? i : Option TREntry) := by
  unfold decTailTr; dsimp only
  have hlen := logSkippedKeysTr_length (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  rw [at?_append_non_entry _ _ rfl,
      at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_of_lt _ _ (by omega), at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ hi]

theorem mem_setRecvChain_tr {chains : List RecvChain} {chain c : RecvChain}
    (hc : c ∈ setRecvChain chains chain) : c = chain ∨ c ∈ chains := by
  unfold setRecvChain at hc; rw [List.mem_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := hc
  split
  · exact Or.inl rfl
  · exact Or.inr hc0
theorem findRecvChain_eq_some_of_getElem?_nodup_tr (chains : List RecvChain) (ci : Nat) (c : RecvChain)
    (hNodup : (chains.map RecvChain.ratchetKey).Nodup) (hGet : chains[ci]? = some c) :
    findRecvChain chains c.ratchetKey = some c := by
  induction chains generalizing ci with
  | nil => simp at hGet
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNodup
    rcases hNodup with ⟨hNotMem, hNodupTl⟩
    cases ci with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
      subst hGet; simp [findRecvChain, List.find?]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hGet
      have hNe : (hd.ratchetKey == c.ratchetKey) = false :=
        beq_false_of_ne fun hEq => hNotMem (hEq ▸ List.mem_map_of_mem (List.mem_of_getElem? hGet))
      unfold findRecvChain at ih ⊢; simp [List.find?, hNe, ih k hNodupTl hGet]
theorem map_ite_ratchetKey_eq_self_tr {ys : List RecvChain} {c' : RecvChain}
    (hNo : ∀ y ∈ ys, y.ratchetKey ≠ c'.ratchetKey) :
    (ys.map fun c0 => if (c0.ratchetKey == c'.ratchetKey) = true then c' else c0) = ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    have hNe : (y.ratchetKey == c'.ratchetKey) = false := beq_false_of_ne (hNo y (List.mem_cons_self ..))
    simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte]
    exact congrArg (y :: ·) (ih fun z hz => hNo z (List.mem_cons_of_mem y hz))
theorem setRecvChain_eq_set_of_getElem?_nodup_tr (chains : List RecvChain) (ci : Nat) (c c' : RecvChain)
    (hNodup : (chains.map RecvChain.ratchetKey).Nodup) (hGet : chains[ci]? = some c) (hKey : c'.ratchetKey = c.ratchetKey) :
    setRecvChain chains c' = chains.set ci c' := by
  induction chains generalizing ci with
  | nil => simp at hGet
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNodup
    rcases hNodup with ⟨hNotMem, hNodupTl⟩
    cases ci with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet; subst hGet
      have hBeq : (hd.ratchetKey == c'.ratchetKey) = true := beq_iff_eq.mpr hKey.symm
      have hNoTl : ∀ y ∈ tl, y.ratchetKey ≠ c'.ratchetKey :=
        fun y hy hEq => hNotMem (hKey ▸ hEq ▸ List.mem_map_of_mem hy)
      unfold setRecvChain; simp only [List.map_cons, hBeq, ↓reduceIte, List.set_cons_zero]
      exact congrArg (c' :: ·) (map_ite_ratchetKey_eq_self_tr hNoTl)
    | succ k =>
      simp only [List.getElem?_cons_succ] at hGet
      have hNe : (hd.ratchetKey == c'.ratchetKey) = false :=
        beq_false_of_ne fun hEq => hNotMem (hEq ▸ hKey ▸ List.mem_map_of_mem (List.mem_of_getElem? hGet))
      unfold setRecvChain at ih ⊢
      simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte, List.set_cons_succ]
      exact congrArg (hd :: ·) (ih k hNodupTl hGet)
theorem consumeMessageKey_eq_some_iff_tr (c : RecvChain) (counter : UInt32) (seed : DY.Bytes) (c' : RecvChain) :
    consumeMessageKey c counter = some (seed, c') ↔
      ¬ counter < c.index ∧ counter.toNat - c.index.toNat ≤ DY.Libsignal.TripleRatchet.maxForwardJumps ∧
      counter ≠ u32Max ∧ seed = (kdfCk (chainKeyAt c.chainKey (counter.toNat - c.index.toNat))).2 ∧
      c' = { c with chainKey := (kdfCk (chainKeyAt c.chainKey (counter.toNat - c.index.toNat))).1, index := counter + 1 } := by
  unfold consumeMessageKey; constructor
  · intro h
    split at h; · simp at h
    next h1 =>
      split at h; · simp at h
      next h2 =>
        split at h; · simp at h
        next h3 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨h1, Nat.le_of_not_gt h2, h3, h.1.symm, h.2.symm⟩
  · rintro ⟨h1, h2, h3, rfl, rfl⟩
    have h2' : ¬ (counter.toNat - c.index.toNat > DY.Libsignal.TripleRatchet.maxForwardJumps) := Nat.not_lt.mpr h2
    simp [h1, h2', h3]

theorem stateRel_sessionToRecordRec_iff_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (st : TRState) (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))) :
    StateRel interpretation S g st (sessionToRecordRec s) ↔
      eraseSkipped (eraseUnmodelled (sessionToSessionRec s)) =
        sessionOf interpretation (gamma interpretation S g) st := by simp [StateRel, sessionToRecordRec]
def modelRecvChainOfTr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (c : RecvChain) : ReceiverChain :=
  { senderRatchetKey := ⟨vec32 (gamma interpretation S g c.ratchetKey)⟩
    chainKey := some ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g c.chainKey), c.index.toBitVec⟩
    messageKeys := [] }
@[simp] theorem eraseRecvChain_modelRecvChainOfTr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (c : RecvChain) :
    eraseRecvChain (modelRecvChainOfTr interpretation S g c) = modelRecvChainOfTr interpretation S g c := rfl
theorem vec32_toList_of_length_eq_tr {b : HwBytes} (hLen : b.length = 32) : (vec32 b).toList = b :=
  vec32_toList_of_length_eq hLen

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
