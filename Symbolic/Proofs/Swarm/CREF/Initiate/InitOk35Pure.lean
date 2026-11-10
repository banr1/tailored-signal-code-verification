/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Refinement.X25519Covered
public import Symbolic.Proofs.Swarm.Leaves.IC12_Stage1MatchedPrefixPure
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
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
import Symbolic.DYBridge.DY.EquationalTheory.Literal

/-!
# `session_initiate` Accept Trace and X25519 One-Time Prekey Variations

Characterizes `setupTrace` entry lookups and concretized bundle keys, relates X25519 u-coordinate
variations to `DY.X25519.x25519Variant`, and evaluates the 9-entry `Composed.aliceStart` trace at
`shown = 35` together with its 34-draw RNG correspondence.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY DY.Comparse DY.Libsignal
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState BundleHandles AliceHandshakeOut)
open DY.Libsignal.PQXDH.Refinement (preKeyBundleByteLength)
open DY.Libsignal.Refinement (ExternCryptoLawsHold torsionShift)
open DY.Libsignal.TripleRatchet (TREvent TRState x25519LowOrder)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

/-! ## `IniOkBin`, `setupTrace` lookups, and signed bundle keys -/

/-- Binary postcondition facts of an accepted `session_initiate` call used on the model side. -/
structure IniOkBin (bundle : HwBytes) (ds : List HwBytes) : Prop where
  lens : ds.map List.length = initiateFullDrawLengths
  bundle_len : bundle.length = preKeyBundleByteLength
  opk : BundleOpkAccepted bundle

theorem at?_of_setupTrace {T : Type} [ExecTraceTypes.Has T] {r : ProtocolSetup} {ms : List Move}
    {i : Nat} {e : T} (hat : (setupTrace r).at? i = some e) :
    (runTraceMoves r ms).at? i = some e := by
  have h := Trace.at?_le (EntryT := T) (setupTrace r) (runTraceMoves r ms) i
    (Symbolic.Swarm.Leaves.IC12Stage1MP.setupTrace_le_runTrace r ms)
  rwa [hat] at h

theorem setupRandomsAt_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupRandomsAt r =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] ++
        (if r.withOpk then [(22, 32)] else []) :=
  b1_setupRandomsAt_eq r hNe

private theorem ini_setupSent_nil :
    List.filterMap (fun i => (Trace.nil : ExecTrace).getMessageSentAt i)
      (newIndices Trace.nil Trace.nil) = [] := by
  simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem ini_newIndices_nil_append {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) :
    newIndices Trace.nil (tr.append e) = newIndices Trace.nil tr ++ [tr.length] := by
  simp only [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1,
    Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
    Nat.sub_zero, List.range'_concat, Nat.one_mul, Nat.zero_add]

private theorem ini_filterMap_sent_prefix {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) :
    List.filterMap (fun i => (tr.append e).getMessageSentAt i) (newIndices Trace.nil tr) =
      List.filterMap (fun i => tr.getMessageSentAt i) (newIndices Trace.nil tr) := by
  apply List.filterMap_congr
  intro i hi
  simp only [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero,
    List.mem_range'_1, Nat.zero_add] at hi
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
    at?_append_of_lt tr e hi.2]

private theorem ini_setupSent_append_net (tr : ExecTrace) (b : DY.Bytes) :
    List.filterMap (fun i => (tr.append (TR.NetE b)).getMessageSentAt i)
      (newIndices Trace.nil (tr.append (TR.NetE b))) =
      List.filterMap (fun i => tr.getMessageSentAt i) (newIndices Trace.nil tr) ++ [b] := by
  rw [ini_newIndices_nil_append, List.filterMap_append, ini_filterMap_sent_prefix]
  simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, Trace.at?_append]

private theorem ini_setupSent_append_nonNet {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Network.ExecEntryT) = none) :
    List.filterMap (fun i => (tr.append e).getMessageSentAt i)
      (newIndices Trace.nil (tr.append e)) =
      List.filterMap (fun i => tr.getMessageSentAt i) (newIndices Trace.nil tr) := by
  rw [ini_newIndices_nil_append, List.filterMap_append, ini_filterMap_sent_prefix]
  simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
    at?_append_eq_of_eq tr e rfl, hproj]

theorem setupPublic_4 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupPublic r 4 = DY.DiffieHellman.dhPk (randTerm 10 32) := by
  rw [setupPublic, setupSent, TR.setupTrace_eq r hNe]
  cases r.withOpk <;> (
    simp only [Bool.false_eq_true, ↓reduceIte,
      TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat first
      | rw [ini_setupSent_append_net]
      | rw [ini_setupSent_append_nonNet _ _ rfl]
    rw [ini_setupSent_nil]
    rfl)

abbrev setupPublic_5 := b1_setupPublic_5

abbrev setupPublic_6 := b1_setupPublic_6

abbrev setupPublic_7 := b1_setupPublic_7

theorem setupPublic_8 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) (hOpk : r.withOpk = true) :
    setupPublic r 8 = DY.DiffieHellman.dhPk (randTerm 22 32) := by
  rw [setupPublic, setupSent, TR.setupTrace_eq r hNe, hOpk]
  simp only [↓reduceIte, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
  repeat first
    | rw [ini_setupSent_append_net]
    | rw [ini_setupSent_append_nonNet _ _ rfl]
  rw [ini_setupSent_nil]
  rfl

theorem setupSecret_0 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupSecret r 0 = randTerm 0 32 := by
  rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl

theorem setupSecret_1 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupSecret r 1 = randTerm 5 32 := by
  rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl

theorem setupSecret_2 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupSecret r 2 = randTerm 10 32 := by
  rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl

theorem setupSecret_4 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupSecret r 4 = randTerm 16 64 := by
  rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl

theorem setupSecret_6 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) (hOpk : r.withOpk = true) :
    setupSecret r 6 = randTerm 22 32 := by
  rw [setupSecret, TR.setupRandoms_eq r hNe, hOpk]; rfl

private theorem ini_run_bind_le {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    (x.run tr).2.val ≤ ((x >>= f).run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, t, _⟩
  · exact Trace.le_refl t
  · exact ((f a).run t).2.property

private theorem ini_at?_run_bind_of_some {E : Type} [ExecTraceTypes.Has E]
    {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr : ExecTrace} {i : Nat} {e : E}
    (h : ((x.run tr).2.val.at? i : Option E) = some e) :
    (((x >>= f).run tr).2.val.at? i : Option E) = some e := by
  have hat := Trace.at?_le (EntryT := E) _ _ i (ini_run_bind_le x f tr)
  rwa [h] at hat

private theorem ini_at?_append_of_some {E E' : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E']
    {tr : ExecTrace} {e : E'} {i : Nat} {res : E} (h : tr.at? i = some res) :
    (tr.append e).at? i = some res := by
  have hle := Trace.at?_le (EntryT := E) tr (tr.append e) i (Trace.append_le tr e)
  rwa [h] at hle

private theorem ini_at?_append_eq {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : tr.length = i) :
    (tr.append e).at? i = some e :=
  hi ▸ Trace.at?_append tr e

theorem setupTrace_at?_4 (r : ProtocolSetup) (_hNe : r.alice ≠ r.bob) :
    ((setupTrace r).at? 4 : Option (DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState PQXDHState))) =
      some (ini_StE r.alice { kind := .identity, sk := randTerm 0 32 }) := by
  rw [TR.setupTrace_eq r _hNe]
  cases r.withOpk <;> (
    dsimp only [Bool.false_eq_true, ↓reduceIte, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat' first
      | exact ini_at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
      | apply ini_at?_append_of_some)

theorem setupTrace_at?_6 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    ((setupTrace r).at? 6 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
      some (ini_EvE (.IdentityRegistered r.bob
        (DY.DiffieHellman.dhPk (randTerm 5 32))
        (DY.Signature.vk (randTerm 5 32)) true)) := by
  rw [TR.setupTrace_eq r hNe]
  cases r.withOpk <;> (
    dsimp only [Bool.false_eq_true, ↓reduceIte, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat' first
      | exact ini_at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
      | apply ini_at?_append_of_some)

theorem setupTrace_at?_14 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    ((setupTrace r).at? 14 : Option DY.Network.ExecEntryT) =
      some (ini_NetE (setupPublic r 4)) := by
  rw [setupPublic_4 r hNe, TR.setupTrace_eq r hNe]
  cases r.withOpk <;> (
    dsimp only [Bool.false_eq_true, ↓reduceIte, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat' first
      | exact ini_at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
      | apply ini_at?_append_of_some)

theorem setupTrace_at?_15 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    ((setupTrace r).at? 15 : Option DY.Network.ExecEntryT) =
      some (ini_NetE (setupPublic r 5)) := by
  rw [setupPublic_5 r hNe, TR.setupTrace_eq r hNe]
  cases r.withOpk <;> (
    dsimp only [Bool.false_eq_true, ↓reduceIte, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat' first
      | exact ini_at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
      | apply ini_at?_append_of_some)

theorem setupTrace_at?_20 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    ((setupTrace r).at? 20 : Option DY.Network.ExecEntryT) =
      some (ini_NetE (setupPublic r 6)) := by
  rw [setupPublic_6 r hNe, TR.setupTrace_eq r hNe]
  cases r.withOpk <;> (
    dsimp only [Bool.false_eq_true, ↓reduceIte, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat' first
      | exact ini_at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
      | apply ini_at?_append_of_some)

theorem setupTrace_at?_21 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    ((setupTrace r).at? 21 : Option DY.Network.ExecEntryT) =
      some (ini_NetE (setupPublic r 7)) := by
  rw [setupPublic_7 r hNe, TR.setupTrace_eq r hNe]
  cases r.withOpk <;> (
    dsimp only [Bool.false_eq_true, ↓reduceIte, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat' first
      | exact ini_at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
      | apply ini_at?_append_of_some)

theorem setupTrace_at?_25 (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) (hOpk : r.withOpk = true) :
    ((setupTrace r).at? 25 : Option DY.Network.ExecEntryT) =
      some (ini_NetE (setupPublic r 8)) := by
  rw [setupPublic_8 r hNe hOpk, TR.setupTrace_eq r hNe, hOpk]
  dsimp only [↓reduceIte, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
  exact ini_at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])

theorem runTrace_getMessageSentAt_25 (r : ProtocolSetup) (ms : List Move)
    (hNe : r.alice ≠ r.bob) (hOpk : r.withOpk = true) :
    (runTraceMoves r ms).getMessageSentAt 25 = some (setupPublic r 8) :=
  getMessageSentAt_of_at? (at?_of_setupTrace (setupTrace_at?_25 r hNe hOpk))

theorem received_setupHandles (r : ProtocolSetup) (ms : List Move) (hNe : r.alice ≠ r.bob) :
    received (runTraceMoves r ms) [14, 15, 20, 21] =
      [setupPublic r 4, setupPublic r 5, setupPublic r 6, setupPublic r 7] := by
  have h14 := getMessageSentAt_of_at? (at?_of_setupTrace (ms := ms) (setupTrace_at?_14 r hNe))
  have h15 := getMessageSentAt_of_at? (at?_of_setupTrace (ms := ms) (setupTrace_at?_15 r hNe))
  have h20 := getMessageSentAt_of_at? (at?_of_setupTrace (ms := ms) (setupTrace_at?_20 r hNe))
  have h21 := getMessageSentAt_of_at? (at?_of_setupTrace (ms := ms) (setupTrace_at?_21 r hNe))
  simp [received, h14, h15, h20, h21]

theorem received_setupHandles_some (r : ProtocolSetup) (ms : List Move) (hNe : r.alice ≠ r.bob)
    {j : Nat} {t : DY.Bytes} (hj : (runTraceMoves r ms).getMessageSentAt j = some t) :
    received (runTraceMoves r ms) ([14, 15, 20, 21] ++ (some j).toList) =
      [setupPublic r 4, setupPublic r 5, setupPublic r 6, setupPublic r 7, t] := by
  have h14 := getMessageSentAt_of_at? (at?_of_setupTrace (ms := ms) (setupTrace_at?_14 r hNe))
  have h15 := getMessageSentAt_of_at? (at?_of_setupTrace (ms := ms) (setupTrace_at?_15 r hNe))
  have h20 := getMessageSentAt_of_at? (at?_of_setupTrace (ms := ms) (setupTrace_at?_20 r hNe))
  have h21 := getMessageSentAt_of_at? (at?_of_setupTrace (ms := ms) (setupTrace_at?_21 r hNe))
  simp [received, h14, h15, h20, h21, hj]

theorem setupRandomsAt_fst_lt_setupTrace_length (r : ProtocolSetup) (hNe : r.alice ≠ r.bob)
    {p : Nat × Nat} (hp : p ∈ setupRandomsAt r) :
    p.1 < (setupTrace r).length := by
  rcases p with ⟨i, sz⟩
  have hlen : (setupTrace r).length = if r.withOpk then 26 else 22 := by
    rw [TR.setupTrace_eq r hNe]
    cases r.withOpk <;> simp [TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]
  rw [setupRandomsAt_eq r hNe] at hp
  rw [hlen]
  cases hopk : r.withOpk <;>
    simp only [hopk, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp ⊢ <;>
    omega

theorem ini_gamma_lit (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    gamma i S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma gamma' DY.Literal.literalToBytes
  show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)]
  rfl

theorem ini_gamma_concat (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (l r : DY.Bytes) :
    gamma i S g (DY.Concat.concat l r) = gamma i S g l ++ gamma i S g r := by
  unfold gamma gamma'
  show ((({ lhs := l, rhs := r } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g)]
  rfl

theorem ini_gamma_kemPk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (seed : DY.Bytes) :
    gamma i S g (DY.PQKem.kemPk seed) = S.kemPk (gamma i S g seed) := by
  unfold gamma gamma' DY.PQKem.kemPk
  show ((({ sk := seed } : DY.PQKem.Pk.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll i S g)]
  rfl

theorem ini_gamma_sign (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (sk nonce msg : DY.Bytes) :
    gamma i S g (DY.Signature.sign sk nonce msg) =
      S.sign (gamma i S g sk) (gamma i S g nonce) (gamma i S g msg) := by
  unfold gamma gamma' DY.Signature.sign
  show ((({ sk := sk, nonce := nonce, msg := msg } : DY.Signature.Sign.SubF DY.Bytes).pack).rec
    (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign S) (concretizeAll i S g)]
  rfl

theorem ini_gamma_encodeEC (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (pk : DY.Bytes) :
    gamma i S g (DY.Libsignal.PQXDH.encodeEC pk) = 0x05#8 :: gamma i S g pk := by
  unfold DY.Libsignal.PQXDH.encodeEC DY.Libsignal.TripleRatchet.litByte
  rw [ini_gamma_concat, ini_gamma_lit]
  rfl

theorem ini_gamma_encodeKEM (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (pk : DY.Bytes) :
    gamma i S g (DY.Libsignal.PQXDH.encodeKEM pk) = 0x08#8 :: gamma i S g pk := by
  unfold DY.Libsignal.PQXDH.encodeKEM DY.Libsignal.TripleRatchet.litByte
  rw [ini_gamma_concat, ini_gamma_lit]
  rfl

theorem compat_of_sigma_eq_lt {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (hNe : r.alice ≠ r.bob) (ms : List Move) {g g' : Ghost}
    (hC : GhostAndSemMatchSetup interpretation r S g)
    (_haddr : g'.addr = g.addr)
    (hσ : ∀ i j, i < (runTraceMoves r ms).length → g'.σ i j = g.σ i j) :
    GhostAndSemMatchSetup interpretation r S g' := by
  have hle : (setupTrace r).length ≤ (runTraceMoves r ms).length :=
    Trace.length_le _ _ (Symbolic.Swarm.Leaves.IC12Stage1MP.setupTrace_le_runTrace r ms)
  have hσ_setup : ∀ i sz, (i, sz) ∈ setupRandomsAt r → g'.σ i sz = g.σ i sz := fun i sz hp =>
    hσ i sz (Nat.lt_of_lt_of_le (setupRandomsAt_fst_lt_setupTrace_length r hNe hp) hle)
  have h5_32 : g'.σ 5 32 = g.σ 5 32 := hσ_setup 5 32 (by rw [setupRandomsAt_eq r hNe]; simp)
  have h10_32 : g'.σ 10 32 = g.σ 10 32 := hσ_setup 10 32 (by rw [setupRandomsAt_eq r hNe]; simp)
  have h11_64 : g'.σ 11 64 = g.σ 11 64 := hσ_setup 11 64 (by rw [setupRandomsAt_eq r hNe]; simp)
  have h16_64 : g'.σ 16 64 = g.σ 16 64 := hσ_setup 16 64 (by rw [setupRandomsAt_eq r hNe]; simp)
  have h17_64 : g'.σ 17 64 = g.σ 17 64 := hσ_setup 17 64 (by rw [setupRandomsAt_eq r hNe]; simp)
  refine ⟨fun p hp => (hσ_setup p.1 p.2 hp).trans (hC.1 p hp), fun t ht => ?_, hC.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · have heq : gamma interpretation S g' r.spkSigTerm =
        gamma interpretation S g r.spkSigTerm := by
      change gamma interpretation S g' (setupPublic r 5) =
        gamma interpretation S g (setupPublic r 5)
      rw [setupPublic_5 r hNe]
      simp only [ini_gamma_sign, ini_gamma_encodeEC, ini_gamma_dhPk, gamma_randTerm,
        h5_32, h11_64, h10_32]
    exact heq.trans (hC.2.1 r.spkSigTerm (by simp))
  · have heq : gamma interpretation S g' r.pqpkPubTerm =
        gamma interpretation S g r.pqpkPubTerm := by
      change gamma interpretation S g' (setupPublic r 6) =
        gamma interpretation S g (setupPublic r 6)
      rw [setupPublic_6 r hNe]
      simp only [ini_gamma_kemPk, gamma_randTerm, h16_64]
    exact heq.trans (hC.2.1 r.pqpkPubTerm (by simp))
  · have heq : gamma interpretation S g' r.pqpkSigTerm =
        gamma interpretation S g r.pqpkSigTerm := by
      change gamma interpretation S g' (setupPublic r 7) =
        gamma interpretation S g (setupPublic r 7)
      rw [setupPublic_7 r hNe]
      simp only [ini_gamma_sign, ini_gamma_encodeKEM, ini_gamma_kemPk, gamma_randTerm,
        h5_32, h17_64, h16_64]
    exact heq.trans (hC.2.1 r.pqpkSigTerm (by simp))

theorem gamma_setupSecret (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (hNe : r.alice ≠ r.bob) (S : OpaqueSymbolSemantics) (g : Ghost) (hC : GhostAndSemMatchSetup interpretation r S g) :
    gamma interpretation S g (setupSecret r 0) = secretBytes r 0 ∧
    gamma interpretation S g (setupSecret r 1) = secretBytes r 1 ∧
    gamma interpretation S g (setupSecret r 2) = secretBytes r 2 ∧
    gamma interpretation S g (setupSecret r 4) = secretBytes r 4 ∧
    (r.withOpk = true → gamma interpretation S g (setupSecret r 6) = secretBytes r 6) := by
  have hmem0 : (0, 32) ∈ setupRandomsAt r := by rw [setupRandomsAt_eq r hNe]; cases r.withOpk <;> simp
  have hmem1 : (5, 32) ∈ setupRandomsAt r := by rw [setupRandomsAt_eq r hNe]; cases r.withOpk <;> simp
  have hmem2 : (10, 32) ∈ setupRandomsAt r := by rw [setupRandomsAt_eq r hNe]; cases r.withOpk <;> simp
  have hmem4 : (16, 64) ∈ setupRandomsAt r := by rw [setupRandomsAt_eq r hNe]; cases r.withOpk <;> simp
  have hsec : secretBytes r 0 = r.fresh 0 32 ∧ secretBytes r 1 = r.fresh 5 32 ∧
      secretBytes r 2 = r.fresh 10 32 ∧ secretBytes r 4 = r.fresh 16 64 ∧
      (r.withOpk = true → secretBytes r 6 = r.fresh 22 32) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [secretBytes, setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
    · rw [secretBytes, setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
    · rw [secretBytes, setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
    · rw [secretBytes, setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
    · intro hOpk; rw [secretBytes, setupRandomsAt_eq r hNe, hOpk]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [setupSecret_0 r hNe, gamma_randTerm, hC.1 _ hmem0, hsec.1]; rfl
  · rw [setupSecret_1 r hNe, gamma_randTerm, hC.1 _ hmem1, hsec.2.1]; rfl
  · rw [setupSecret_2 r hNe, gamma_randTerm, hC.1 _ hmem2, hsec.2.2.1]; rfl
  · rw [setupSecret_4 r hNe, gamma_randTerm, hC.1 _ hmem4, hsec.2.2.2.1]; rfl
  · intro hOpk
    have hmem6 : (22, 32) ∈ setupRandomsAt r := by rw [setupRandomsAt_eq r hNe, hOpk]; simp
    rw [setupSecret_6 r hNe hOpk, gamma_randTerm, hC.1 _ hmem6, hsec.2.2.2.2 hOpk]; rfl

theorem gamma_setupPublic_4 (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (hNe : r.alice ≠ r.bob) (S : OpaqueSymbolSemantics) (g : Ghost) (hC : GhostAndSemMatchSetup interpretation r S g) :
    gamma interpretation S g (setupPublic r 4) = pubBytes interpretation (secretBytes r 2) := by
  rw [setupPublic_4 r hNe, ← setupSecret_2 r hNe, ini_gamma_dhPk,
    (gamma_setupSecret interpretation r hNe S g hC).2.2.1]
  rfl

theorem gamma_setupPublic_8 (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (hNe : r.alice ≠ r.bob) (hOpk : r.withOpk = true) (S : OpaqueSymbolSemantics) (g : Ghost)
    (hC : GhostAndSemMatchSetup interpretation r S g) :
    gamma interpretation S g (setupPublic r 8) = pubBytes interpretation (secretBytes r 6) := by
  rw [setupPublic_8 r hNe hOpk, ← setupSecret_6 r hNe hOpk, ini_gamma_dhPk,
    (gamma_setupSecret interpretation r hNe S g hC).2.2.2.2 hOpk]
  rfl

theorem bundleCore_of_honestBundle (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (hNe : r.alice ≠ r.bob) (S : OpaqueSymbolSemantics) (g : Ghost) (hC : GhostAndSemMatchSetup interpretation r S g)
    (bundle : HwBytes) (hbundle : HonestBundle interpretation r bundle)
    (hlen : bundle.length = preKeyBundleByteLength) :
    BundleSignedKeysMatch interpretation S g bundle
      (setupPublic r 4) (setupPublic r 5) (setupPublic r 6) (setupPublic r 7) := by
  obtain ⟨h46, h79, h147, h1716, _⟩ := hbundle hlen
  refine ⟨hlen, ?_, ?_, ?_, ?_⟩
  · rw [gamma_setupPublic_4 interpretation r hNe S g hC]; exact h46
  · rw [show setupPublic r 5 = r.spkSigTerm from rfl, hC.2.1 r.spkSigTerm (by simp)]; exact h79
  · rw [show setupPublic r 6 = r.pqpkPubTerm from rfl, hC.2.1 r.pqpkPubTerm (by simp)]; exact h147
  · rw [show setupPublic r 7 = r.pqpkSigTerm from rfl, hC.2.1 r.pqpkSigTerm (by simp)]; exact h1716

/-! ## Canonical X25519 OPK variations and attacker knowledge -/

theorem attackerKnows_compHwLit (bs : HwBytes) (tr : ExecTrace) :
    (compHwLit bs).AttackerKnows tr :=
  DY.Literal.attacker_knows_literalToBytes ⟨(bs.map UInt8.ofBitVec).toArray⟩ tr

theorem baseAttackerKnows_of_at?_net {msg : DY.Bytes} {idx : Nat} {tr : ExecTrace}
    (h : (tr.at? idx : Option DY.Network.ExecEntryT) = some (ini_NetE msg)) :
    DY.Trace.BaseAttackerKnows tr msg := by
  apply DY.Trace.prove_BaseAttackerKnows DY.Network.baseAttackerKnowledge tr (ini_NetE msg) msg idx
  · exact h
  · rw [Symbolic.DYBridge.DY.Network.baseAttackerKnowledge_attackerKnows]

theorem attackerKnows_opkPub (r : ProtocolSetup) (ms : List Move) (hNe : r.alice ≠ r.bob)
    (hWith : r.withOpk = true) :
    (setupPublic r 8).AttackerKnows (runTraceMoves r ms) := by
  apply DY.Bytes.AttackerKnows.prove_from_base
  exact baseAttackerKnows_of_at?_net (at?_of_setupTrace (setupTrace_at?_25 r hNe hWith))

theorem attackerKnows_x25519Variant_opkPub (r : ProtocolSetup) (ms : List Move) (hNe : r.alice ≠ r.bob)
    (hWith : r.withOpk = true) (v : Fin 4) :
    (DY.X25519.x25519Variant (setupPublic r 8) v).AttackerKnows (runTraceMoves r ms) := by
  apply DY.Bytes.AttackerKnows.prove DY.X25519.x25519Variant.attackerKnowledge
  exact ⟨setupPublic r 8, v, 0, by simp [DY.X25519.x25519Variant, DY.X25519.x25519TorsionVariant],
    attackerKnows_opkPub r ms hNe hWith⟩

private theorem ini_view_variant_dhPk (sk : DY.Bytes) :
    (DY.DiffieHellman.dhPk sk).view? DY.X25519.Variant.SubF = none :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
    ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)

private theorem ini_view_lit_dhPk (sk : DY.Bytes) :
    (DY.DiffieHellman.dhPk sk).view? DY.Literal.Literal.SubF = none :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
    ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)

private theorem ini_normalizeX25519Key_dhPk (sk : DY.Bytes) :
    DY.X25519.normalizeX25519Key (DY.DiffieHellman.dhPk sk) = DY.DiffieHellman.dhPk sk := by
  unfold DY.X25519.normalizeX25519Key
  rw [ini_view_variant_dhPk]

private theorem ini_bytesToLiteral_dhPk (sk : DY.Bytes) :
    DY.Literal.bytesToLiteral (DY.DiffieHellman.dhPk sk) = none := by
  dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]
  rw [ini_view_lit_dhPk]

private theorem ini_x25519LowOrder_dhPk (sk : DY.Bytes) :
    x25519LowOrder (DY.DiffieHellman.dhPk sk) = false := by
  unfold x25519LowOrder
  rw [ini_normalizeX25519Key_dhPk, ini_bytesToLiteral_dhPk]

theorem x25519Key_x25519Variant_opkPub (r : ProtocolSetup) (hNe : r.alice ≠ r.bob)
    (hWith : r.withOpk = true) (v : Fin 4) :
    DY.X25519.normalizeX25519Key (DY.X25519.x25519Variant (setupPublic r 8) v) = setupPublic r 8 := by
  have hkey_opk : DY.X25519.normalizeX25519Key (setupPublic r 8) = setupPublic r 8 := by
    rw [setupPublic_8 r hNe hWith]; exact ini_normalizeX25519Key_dhPk _
  simp only [DY.X25519.x25519Variant, hkey_opk]
  split
  · exact hkey_opk
  · simp [DY.X25519.normalizeX25519Key, DY.BytesView.view_pack]

theorem x25519LowOrder_x25519Variant_opkPub (r : ProtocolSetup) (hNe : r.alice ≠ r.bob)
    (hWith : r.withOpk = true) (v : Fin 4) :
    x25519LowOrder (DY.X25519.x25519Variant (setupPublic r 8) v) = false := by
  unfold x25519LowOrder
  rw [x25519Key_x25519Variant_opkPub r hNe hWith v, setupPublic_8 r hNe hWith,
    ini_bytesToLiteral_dhPk]

unseal DY.Bytes in
local instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_variant_pack (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (v : DY.X25519.Variant.SubF DY.Bytes) :
    gamma interpretation S g v.pack =
      variantBytes (torsionShift interpretation (gamma interpretation S g v.key) v.torsion)
        v.variation := by
  unfold gamma gamma'
  show ((v.pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeVariant interpretation) (concretizeAll interpretation S g)]
  rfl

theorem gamma_variant_pack_t0 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k : DY.Bytes) (v : Fin 4) :
    gamma interpretation S g (({ key := k, variation := v } : DY.X25519.Variant.SubF DY.Bytes)).pack =
      variantBytes (gamma interpretation S g k) v := by
  rw [gamma_variant_pack]
  show variantBytes (torsionShift interpretation (gamma interpretation S g k) 0) v = _
  unfold torsionShift; simp

theorem pubBytes_secretBytes_6_length {interpretation : ExternInterpretation}
    (hEq : ExternCryptoLawsHold interpretation) (r : ProtocolSetup) :
    (pubBytes interpretation (secretBytes r 6)).length = 32 := by
  unfold pubBytes
  exact hEq.x25519_public_key_length _

theorem leBytes_uOf_eq_of_canonical {b : HwBytes} (hb : b.length = 32)
    (hcanon : DY.X25519.leValue (b.map BitVec.toNat) < DY.X25519.p25519) :
    leBytes 32 (x25519UCoord b) = b := by
  have hp := p25519_lt
  have hu : x25519UCoord b = DY.X25519.leValue (b.map BitVec.toNat) := by
    unfold x25519UCoord DY.X25519.uCoord
    rw [Nat.mod_eq_of_lt (a := DY.X25519.leValue (b.map BitVec.toNat)) (b := 2 ^ 255) (by omega),
      Nat.mod_eq_of_lt hcanon]
  rw [hu, ← hb]
  exact leBytes_leValue b

theorem variantBytes_keyVariation_eq {b₀ b : HwBytes}
    (hb₀ : b₀.length = 32) (hb : b.length = 32) (hu : x25519UCoord b = x25519UCoord b₀) :
    (if keyVariation b = 0 then leBytes 32 (x25519UCoord b₀)
     else variantBytes b₀ (keyVariation b)) = b := by
  have hL : keyValue b < 2 ^ 256 := by
    have := leValue_lt b; rw [hb] at this; unfold keyValue; omega
  have hb' : leBytes 32 (keyValue b) = b := by
    rw [← hb]; exact leBytes_leValue b
  have hu_def : x25519UCoord b = keyValue b % 2 ^ 255 % DY.X25519.p25519 := rfl
  have hp : DY.X25519.p25519 = 2 ^ 255 - 19 := rfl
  refine Eq.trans ?_ hb'
  unfold variantBytes keyVariation
  simp only [hb₀, ↓reduceIte, ← hu]
  by_cases h1 : 2 ^ 255 ≤ keyValue b <;> by_cases h2 : DY.X25519.p25519 ≤ keyValue b % 2 ^ 255 <;>
    simp only [h1, h2, ↓reduceIte]
  · have hne : (3 : Fin 4) ≠ 0 := by decide
    simp only [hne, ↓reduceIte]
    apply congrArg (leBytes 32)
    rw [show (((3 : Fin 4) : Nat)) = 3 from rfl]
    rw [hp] at hu_def h2 ⊢
    generalize keyValue b = L at *
    generalize x25519UCoord b = u at *
    by_cases hc : u + (2 ^ 255 - 19) < 2 ^ 255 <;>
      simp (config := { decide := true }) only [hc, and_true, and_false, ↓reduceIte] <;> omega
  · have hne : (1 : Fin 4) ≠ 0 := by decide
    simp only [hne, ↓reduceIte]
    apply congrArg (leBytes 32)
    rw [show (((1 : Fin 4) : Nat)) = 1 from rfl]
    rw [hp] at hu_def h2 ⊢
    generalize keyValue b = L at *
    generalize x25519UCoord b = u at *
    by_cases hc : u + (2 ^ 255 - 19) < 2 ^ 255 <;>
      simp (config := { decide := true }) only [hc, and_true, and_false, ↓reduceIte] <;> omega
  · have hne : (2 : Fin 4) ≠ 0 := by decide
    simp only [hne, ↓reduceIte]
    apply congrArg (leBytes 32)
    rw [show (((2 : Fin 4) : Nat)) = 2 from rfl]
    rw [hp] at hu_def h2 ⊢
    generalize keyValue b = L at *
    generalize x25519UCoord b = u at *
    by_cases hc : u + (2 ^ 255 - 19) < 2 ^ 255 <;>
      simp (config := { decide := true }) only [hc, and_true, and_false, ↓reduceIte] <;> omega
  · apply congrArg (leBytes 32)
    rw [hp] at hu_def h2
    generalize keyValue b = L at *
    omega

theorem gamma_x25519Variant_opkPub {interpretation : ExternInterpretation}
    (hEq : ExternCryptoLawsHold interpretation)
    (hPubCanon : X25519PubCanonical interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) (hWith : r.withOpk = true)
    (S : OpaqueSymbolSemantics) (g : Ghost) (hC : GhostAndSemMatchSetup interpretation r S g)
    {opkBytes : HwBytes} (hlen32 : opkBytes.length = 32)
    (hu : x25519UCoord opkBytes = x25519UCoord (pubBytes interpretation (secretBytes r 6))) :
    gamma interpretation S g (DY.X25519.x25519Variant (setupPublic r 8) (keyVariation opkBytes)) =
      opkBytes := by
  have hb₀_len : (pubBytes interpretation (secretBytes r 6)).length = 32 :=
    pubBytes_secretBytes_6_length hEq r
  have hb₀_canon :
      DY.X25519.leValue ((pubBytes interpretation (secretBytes r 6)).map BitVec.toNat) <
        DY.X25519.p25519 :=
    hPubCanon (clamp (secretBytes r 6))
  have hle_b₀ : leBytes 32 (x25519UCoord (pubBytes interpretation (secretBytes r 6))) =
      pubBytes interpretation (secretBytes r 6) :=
    leBytes_uOf_eq_of_canonical hb₀_len hb₀_canon
  have hkey_opk : DY.X25519.normalizeX25519Key (setupPublic r 8) = setupPublic r 8 := by
    rw [setupPublic_8 r hwf.1 hWith]; exact ini_normalizeX25519Key_dhPk _
  have hgam_opk : gamma interpretation S g (setupPublic r 8) =
      pubBytes interpretation (secretBytes r 6) :=
    gamma_setupPublic_8 interpretation r hwf.1 hWith S g hC
  have hvar := variantBytes_keyVariation_eq hb₀_len hlen32 hu
  simp only [DY.X25519.x25519Variant, hkey_opk]
  by_cases hv : keyVariation opkBytes = 0
  · simp only [hv, ↓reduceIte] at hvar ⊢
    rw [hgam_opk, ← hle_b₀]
    exact hvar
  · simp only [hv, ↓reduceIte] at hvar ⊢
    rw [gamma_variant_pack_t0, hgam_opk]
    exact hvar

theorem slice_9_33_eq_ecKey {b : HwBytes} (hlen : b.length = preKeyBundleByteLength)
    (hb9 : b[9]? = some 5#8) :
    slice b 9 33 = ecKey (slice b 10 32) ∧ (slice b 10 32).length = 32 := by
  unfold preKeyBundleByteLength at hlen
  have hlt9 : 9 < b.length := by omega
  have h9 : b[9] = 5#8 := by
    rw [List.getElem?_eq_getElem hlt9, Option.some.injEq] at hb9; exact hb9
  refine ⟨?_, ?_⟩
  · unfold slice ecKey
    rw [List.drop_eq_getElem_cons hlt9, h9]; rfl
  · unfold slice
    simp [List.length_take, List.length_drop, hlen]

/-! ## Composed `aliceStart` symbolic execution -/

section AliceStartExec

attribute [local irreducible] Bind.bind

/-- The `AliceHandshakeOut` returned by `PQXDH.aliceHandshake` starting at `tr`. -/
def iniAliceOut (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes)
    (opk : Option DY.Bytes) : AliceHandshakeOut :=
  let ek := randTerm tr.length 32
  let e := randTerm (tr.length + 1) 32
  { ikA := DY.DiffieHellman.dhPk ikA, ikB := ikBPk, spk := spkPk, pqpk := pqPk, opk,
    ek := DY.DiffieHellman.dhPk ek,
    ct := (DY.Libsignal.PQXDH.aliceAgreement ikA ek ikBPk spkPk pqPk opk e).1,
    keys := (DY.Libsignal.PQXDH.aliceAgreement ikA ek ikBPk spkPk pqPk opk e).2 }

theorem Runs.aliceHandshake {tr : ExecTrace} {a b : DY.Participant} {idH regB : Nat}
    {h : BundleHandles}
    {ikA ikBPk vkB spkPk spkSig pqPk pqSig : DY.Bytes} {opk : Option DY.Bytes} {honest : Bool}
    (hid : tr.at? idH = some (ini_StE a { kind := .identity, sk := ikA }))
    (hreg : tr.at? regB = some (ini_EvE (.IdentityRegistered b ikBPk vkB honest)))
    (hspk : tr.at? h.spk = some (ini_NetE spkPk))
    (hspkSig : tr.at? h.spkSig = some (ini_NetE spkSig))
    (hpq : tr.at? h.pqpk = some (ini_NetE pqPk))
    (hpqSig : tr.at? h.pqpkSig = some (ini_NetE pqSig))
    (hv1 : DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeEC spkPk) spkSig = true)
    (hv2 : DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeKEM pqPk) pqSig = true)
    (hopk : NetOpt tr h.opk opk)
    (hlow : x25519LowOrder spkPk = false)
    (hlowO : (opk.all fun o => !x25519LowOrder o) = true) :
    Runs (DY.Libsignal.PQXDH.aliceHandshake a b idH regB h) tr
      (iniAliceOut tr ikA ikBPk spkPk pqPk opk)
      ((tr.append (ini_RndE 32)).append (ini_RndE 32)) := by
  rcases h with ⟨_, _, _, _, oi⟩
  rcases oi with _ | i <;> rcases opk with _ | o <;> simp only [NetOpt] at hopk
  all_goals
    unfold DY.Libsignal.PQXDH.aliceHandshake
    refine Runs.bind (Runs.getKey hid) (Runs.bind (Runs.ini_lookupIdentity hreg)
      (Runs.bind (Runs.ini_receiveMessage hspk) (Runs.bind (Runs.ini_receiveMessage hspkSig)
        (Runs.bind (Runs.ini_receiveMessage hpq) (Runs.bind (Runs.ini_receiveMessage hpqSig)
          (Runs.bind (Runs.guard _ hv1) (Runs.bind (Runs.guard _ hv2) ?_)))))))
    dsimp only; try refine Runs.bind (Runs.ini_receiveMessage hopk) ?_
    have hlow' : (!DY.Libsignal.PQXDH.x25519LowOrder spkPk) = true := by
      change (!x25519LowOrder spkPk) = true
      rw [hlow]; rfl
    exact Runs.bind (Runs.pure _ _) (Runs.bind (Runs.genRand _ _)
      (Runs.bind (Runs.guard _ hlow') (Runs.bind (Runs.guard _ hlowO)
        (Runs.bind (Runs.genRand _ _) (by
          convert Runs.pure (iniAliceOut tr ikA ikBPk spkPk pqPk _)
            ((tr.append (ini_RndE 32)).append (ini_RndE 32)) using 2
          simp [iniAliceOut, Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2])))))

/-- Initial `TRState` stored by `Composed.aliceStart` starting at `tr`. -/
def iniAliceStartState (tr : ExecTrace) (b : DY.Participant) (o : AliceHandshakeOut) : TRState :=
  let dhsA := randTerm (tr.length + 2) 32
  let (rkA, cksA) := DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk dhsA
  { peer := b,
    myIk := DY.Libsignal.PQXDH.serializedIk o.ikA,
    peerIk := DY.Libsignal.PQXDH.serializedIk o.ikB,
    rk := rkA,
    dhs := dhsA,
    cks := cksA,
    ns := 0,
    pn := 0,
    sid := Concat.concat (DY.DiffieHellman.dhPk dhsA) o.keys.rk,
    initiator := true,
    rIdx := 1,
    recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
    spqr := DY.Spqr.spqrInit o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B }

/-- Exact 9-entry post-trace produced by `Composed.aliceStart` starting at `tr`. -/
def iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : AliceHandshakeOut) : ExecTrace :=
  let dhsA := randTerm (tr.length + 2) 32
  let stA := iniAliceStartState tr b o
  ((((((((tr.append (ini_RndE 32)).append (ini_RndE 32)).append (ini_RndE 32)).append
    (ini_NetE o.ek)).append
    (ini_NetE o.ct)).append
    (ini_EvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
    (ini_TREvE (.InitSession a b (DY.DiffieHellman.dhPk dhsA) o.spk))).append
    (ini_CEvE (.HandshakeSession (stA.sessionInfo a) (tr.length + 5)))).append
    (ini_TRStE a stA)

theorem Runs.aliceStart {tr : ExecTrace} {a b : DY.Participant} {idH regB : Nat}
    {h : BundleHandles}
    {ikA ikBPk vkB spkPk spkSig pqPk pqSig : DY.Bytes} {opk : Option DY.Bytes} {honest : Bool}
    (hid : tr.at? idH = some (ini_StE a { kind := .identity, sk := ikA }))
    (hreg : tr.at? regB = some (ini_EvE (.IdentityRegistered b ikBPk vkB honest)))
    (hspk : tr.at? h.spk = some (ini_NetE spkPk))
    (hspkSig : tr.at? h.spkSig = some (ini_NetE spkSig))
    (hpq : tr.at? h.pqpk = some (ini_NetE pqPk))
    (hpqSig : tr.at? h.pqpkSig = some (ini_NetE pqSig))
    (hv1 : DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeEC spkPk) spkSig = true)
    (hv2 : DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeKEM pqPk) pqSig = true)
    (hopk : NetOpt tr h.opk opk)
    (hlow : x25519LowOrder spkPk = false)
    (hlowO : (opk.all fun o => !x25519LowOrder o) = true) :
    Runs (DY.Libsignal.Composed.aliceStart a b idH regB h) tr (tr.length + 8)
      (iniAliceStartTr tr a b (iniAliceOut tr ikA ikBPk spkPk pqPk opk)) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine Runs.bind
    (Runs.aliceHandshake hid hreg hspk hspkSig hpq hpqSig hv1 hv2 hopk hlow hlowO) ?_
  dsimp only
  refine Runs.bind (Runs.genRand _ 32) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.ini_traceLength _) ?_
  refine Runs.bind (Runs.logPQEvent _ _) ?_
  refine Runs.bind (Runs.logTREvent _ _) ?_
  refine Runs.bind (Runs.logCEvent _ _) ?_
  convert Runs.storeTRState _ a (iniAliceStartState tr b (iniAliceOut tr ikA ikBPk spkPk pqPk opk)) using 1 <;>
    simp [iniAliceStartTr, iniAliceStartState,
      Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      Nat.add_assoc]

theorem next_aliceStart_on_runTrace {r : ProtocolSetup} {ms : List Move} (hNe : r.alice ≠ r.bob)
    (shown : Nat) {oi : Option Nat} {opk : Option DY.Bytes}
    (hopk : NetOpt (runTraceMoves r ms) oi opk)
    (hlow : (opk.all fun o => !x25519LowOrder o) = true) :
    let tr := runTraceMoves r ms
    let h : BundleHandles := { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi }
    (Move.aliceStart r.alice r.bob 4 6 h shown).next tr =
      iniAliceStartTr tr r.alice r.bob
        (iniAliceOut tr (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32))
          (DY.DiffieHellman.dhPk (randTerm 10 32)) (DY.PQKem.kemPk (randTerm 16 64)) opk) := by
  have h14 : ((runTraceMoves r ms).at? 14 : Option DY.Network.ExecEntryT) =
      some (ini_NetE (DY.DiffieHellman.dhPk (randTerm 10 32))) := by
    rw [← setupPublic_4 r hNe]; exact at?_of_setupTrace (setupTrace_at?_14 r hNe)
  have h15 : ((runTraceMoves r ms).at? 15 : Option DY.Network.ExecEntryT) =
      some (ini_NetE (DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
        (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32))))) := by
    rw [← setupPublic_5 r hNe]; exact at?_of_setupTrace (setupTrace_at?_15 r hNe)
  have h20 : ((runTraceMoves r ms).at? 20 : Option DY.Network.ExecEntryT) =
      some (ini_NetE (DY.PQKem.kemPk (randTerm 16 64))) := by
    rw [← setupPublic_6 r hNe]; exact at?_of_setupTrace (setupTrace_at?_20 r hNe)
  have h21 : ((runTraceMoves r ms).at? 21 : Option DY.Network.ExecEntryT) =
      some (ini_NetE (DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
        (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64))))) := by
    rw [← setupPublic_7 r hNe]; exact at?_of_setupTrace (setupTrace_at?_21 r hNe)
  have hlow_spk : x25519LowOrder (DY.DiffieHellman.dhPk (randTerm 10 32)) = false :=
    ini_x25519LowOrder_dhPk _
  have hruns := Runs.aliceStart
    (h := { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi })
    (at?_of_setupTrace (setupTrace_at?_4 r hNe))
    (at?_of_setupTrace (setupTrace_at?_6 r hNe))
    h14 h15 h20 h21
    (DY.Signature.verify_sign _ _ _) (DY.Signature.verify_sign _ _ _)
    hopk hlow_spk hlow
  exact (Runs.bind hruns (Runs.pure () _)).2

end AliceStartExec

@[simp] private theorem ini_length_append_entry {T : Type} [ExecTraceTypes.Has T]
    (tr : ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 := by
  simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem length_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : AliceHandshakeOut) :
    (iniAliceStartTr tr a b o).length = tr.length + 9 := by
  unfold iniAliceStartTr
  simp only [ini_length_append_entry]

theorem newIndices_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : AliceHandshakeOut) :
    newIndices tr (iniAliceStartTr tr a b o) =
      [tr.length, tr.length + 1, tr.length + 2, tr.length + 3, tr.length + 4,
       tr.length + 5, tr.length + 6, tr.length + 7, tr.length + 8] := by
  unfold newIndices
  rw [length_iniAliceStartTr, Nat.add_sub_cancel_left]
  simp [List.range', Nat.add_assoc]

local macro "ini_at?_tr9_tac" : tactic =>
  `(tactic| (dsimp only [iniAliceStartTr]
             repeat (rw [at?_append_of_lt _ _ (by simp only [ini_length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp [ini_length_append_entry])]; rfl))

theorem newRandoms_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : AliceHandshakeOut) :
    newRandoms tr (iniAliceStartTr tr a b o) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) 32, 32), (randTerm (tr.length + 2) 32, 32)] := by
  unfold newRandoms; rw [newIndices_iniAliceStartTr]
  have h0 : ((iniAliceStartTr tr a b o).at? tr.length : Option DY.Random.ExecEntryT) =
      some (ini_RndE 32) := by ini_at?_tr9_tac
  have h1 : ((iniAliceStartTr tr a b o).at? (tr.length + 1) : Option DY.Random.ExecEntryT) =
      some (ini_RndE 32) := by ini_at?_tr9_tac
  have h2 : ((iniAliceStartTr tr a b o).at? (tr.length + 2) : Option DY.Random.ExecEntryT) =
      some (ini_RndE 32) := by ini_at?_tr9_tac
  have h3 : ((iniAliceStartTr tr a b o).at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by ini_at?_tr9_tac
  have h4 : ((iniAliceStartTr tr a b o).at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by ini_at?_tr9_tac
  have h5 : ((iniAliceStartTr tr a b o).at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by ini_at?_tr9_tac
  have h6 : ((iniAliceStartTr tr a b o).at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by ini_at?_tr9_tac
  have h7 : ((iniAliceStartTr tr a b o).at? (tr.length + 7) : Option DY.Random.ExecEntryT) = none := by ini_at?_tr9_tac
  have h8 : ((iniAliceStartTr tr a b o).at? (tr.length + 8) : Option DY.Random.ExecEntryT) = none := by ini_at?_tr9_tac
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, ini_RndE]

theorem getEventAt_pq_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : AliceHandshakeOut) :
    let tr' := iniAliceStartTr tr a b o
    tr'.getEventAt PQXDHEvent tr.length = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 1) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 2) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 3) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 4) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 5) =
      some (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) ∧
    tr'.getEventAt PQXDHEvent (tr.length + 6) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 7) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((iniAliceStartTr tr a b o).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by ini_at?_tr9_tac
  have h1 : ((iniAliceStartTr tr a b o).at? (tr.length + 1) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by ini_at?_tr9_tac
  have h2 : ((iniAliceStartTr tr a b o).at? (tr.length + 2) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by ini_at?_tr9_tac
  have h3 : ((iniAliceStartTr tr a b o).at? (tr.length + 3) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by ini_at?_tr9_tac
  have h4 : ((iniAliceStartTr tr a b o).at? (tr.length + 4) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by ini_at?_tr9_tac
  have h5 : ((iniAliceStartTr tr a b o).at? (tr.length + 5) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
      some (ini_EvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)) := by ini_at?_tr9_tac
  have h6 : ((iniAliceStartTr tr a b o).at? (tr.length + 6) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by ini_at?_tr9_tac
  have h7 : ((iniAliceStartTr tr a b o).at? (tr.length + 7) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by ini_at?_tr9_tac
  have h8 : ((iniAliceStartTr tr a b o).at? (tr.length + 8) : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by ini_at?_tr9_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8, ini_EvE]

theorem getEventAt_tr_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : AliceHandshakeOut) :
    let tr' := iniAliceStartTr tr a b o
    tr'.getEventAt TREvent tr.length = none ∧
    tr'.getEventAt TREvent (tr.length + 1) = none ∧
    tr'.getEventAt TREvent (tr.length + 2) = none ∧
    tr'.getEventAt TREvent (tr.length + 3) = none ∧
    tr'.getEventAt TREvent (tr.length + 4) = none ∧
    tr'.getEventAt TREvent (tr.length + 5) = none ∧
    tr'.getEventAt TREvent (tr.length + 6) =
      some (.InitSession a b (DY.DiffieHellman.dhPk (randTerm (tr.length + 2) 32)) o.spk) ∧
    tr'.getEventAt TREvent (tr.length + 7) = none ∧
    tr'.getEventAt TREvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((iniAliceStartTr tr a b o).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by ini_at?_tr9_tac
  have h1 : ((iniAliceStartTr tr a b o).at? (tr.length + 1) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by ini_at?_tr9_tac
  have h2 : ((iniAliceStartTr tr a b o).at? (tr.length + 2) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by ini_at?_tr9_tac
  have h3 : ((iniAliceStartTr tr a b o).at? (tr.length + 3) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by ini_at?_tr9_tac
  have h4 : ((iniAliceStartTr tr a b o).at? (tr.length + 4) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by ini_at?_tr9_tac
  have h5 : ((iniAliceStartTr tr a b o).at? (tr.length + 5) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by ini_at?_tr9_tac
  have h6 : ((iniAliceStartTr tr a b o).at? (tr.length + 6) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
      some (ini_TREvE (.InitSession a b (DY.DiffieHellman.dhPk (randTerm (tr.length + 2) 32)) o.spk)) := by ini_at?_tr9_tac
  have h7 : ((iniAliceStartTr tr a b o).at? (tr.length + 7) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by ini_at?_tr9_tac
  have h8 : ((iniAliceStartTr tr a b o).at? (tr.length + 8) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by ini_at?_tr9_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8, ini_TREvE]

theorem eventIdx_isAliceDone_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : AliceHandshakeOut) :
    eventIdx isAliceDone tr (iniAliceStartTr tr a b o) = some (tr.length + 5) := by
  unfold eventIdx; rw [newIndices_iniAliceStartTr]
  obtain ⟨h0, h1, h2, h3, h4, h5, _, _, _⟩ := getEventAt_pq_iniAliceStartTr tr a b o
  simp [h0, h1, h2, h3, h4, h5, isAliceDone]

theorem exposures_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : AliceHandshakeOut) :
    exposures tr (iniAliceStartTr tr a b o) = [] := by
  unfold exposures pqExposureAt trExposureAt; rw [newIndices_iniAliceStartTr]
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := getEventAt_pq_iniAliceStartTr tr a b o
  obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8⟩ := getEventAt_tr_iniAliceStartTr tr a b o
  simp [hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8]

theorem vis_aliceStart_35_on_runTrace {r : ProtocolSetup} {ms : List Move} (hNe : r.alice ≠ r.bob)
    {oi : Option Nat} {opk : Option DY.Bytes}
    (hopk : NetOpt (runTraceMoves r ms) oi opk)
    (hlow : (opk.all fun o => !x25519LowOrder o) = true) :
    let tr := runTraceMoves r ms
    let h : BundleHandles := { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi }
    (Move.aliceStart r.alice r.bob 4 6 h 35).vis tr =
      (⟨.recv, received tr ([14, 15, 20, 21] ++ oi.toList), .bundle, none⟩ : VisEntry) ::
        (rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
          [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]) := by
  dsimp only [Move.vis]
  rw [next_aliceStart_on_runTrace hNe 35 hopk hlow, exposures_iniAliceStartTr, List.append_nil]
  unfold aliceVis
  rw [newRandoms_iniAliceStartTr, eventIdx_isAliceDone_iniAliceStartTr]
  dsimp only [List.take, List.map, aliceDraws]
  have hlen : (rngEntry (randTerm (runTraceMoves r ms).length 32) ::
      kyberCoinEntries (randTerm ((runTraceMoves r ms).length + 1) 32) ++
      [{ rngEntry (randTerm ((runTraceMoves r ms).length + 2) 32) with
        anchor := some ((runTraceMoves r ms).length + 5) }]).length = 34 := by
    simp [kyberCoinEntries]
  rw [List.take_of_length_le (Nat.le_of_eq hlen)]

theorem moveOK_aliceStart_35_on_runTrace {r : ProtocolSetup} {ms : List Move}
    (hNe : r.alice ≠ r.bob)
    {oi : Option Nat} {opk : Option DY.Bytes}
    (hopk : NetOpt (runTraceMoves r ms) oi opk)
    (hlow : (opk.all fun o => !x25519LowOrder o) = true) :
    Symbolic.Swarm.Leaves.IC12Stage1MP.MoveOK r
      (.aliceStart r.alice r.bob 4 6
        { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi } 35)
      (runTraceMoves r ms) := by
  refine ⟨rfl, ?_, rfl, trivial, trivial⟩
  refine ⟨by decide, fun i hi => ?_⟩
  rw [next_aliceStart_on_runTrace hNe 35 hopk hlow, eventIdx_isAliceDone_iniAliceStartTr] at hi
  cases hi
  rw [vis_aliceStart_35_on_runTrace hNe hopk hlow]
  exact ⟨{ rngEntry (randTerm ((runTraceMoves r ms).length + 2) 32) with
            anchor := some ((runTraceMoves r ms).length + 5) }, by simp, rfl⟩

theorem ini_forall₂_initiate_rng_34 (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (ds : List HwBytes)
    (hds : ds.map List.length = initiateFullDrawLengths)
    (hσ0 : g.σ ts 32 = ds.getD 0 [])
    (hσ1 : g.σ (ts + 1) 32 = entropyBytes ds)
    (hσ2 : g.σ (ts + 2) 32 = ds.getD 33 []) :
    List.Forall₂ (EventMatchesEntry interpretation r S g)
      (ds.map MachineEvent.rng)
      (rngEntry (randTerm ts 32) :: kyberCoinEntries (randTerm (ts + 1) 32) ++
        [{ rngEntry (randTerm (ts + 2) 32) with anchor := some (ts + 5) }]) := by
  have hds_len : ds.length = 34 := by
    have h := congrArg List.length hds; simp [initiateFullDrawLengths] at h; exact h
  have hkc_len : (kyberCoinEntries (randTerm (ts + 1) 32)).length = 32 := by
    simp [kyberCoinEntries]
  refine forall₂_of_getElem? (by simp [hds_len, hkc_len]) (fun i e v he hv => ?_)
  rw [List.getElem?_map] at he; obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp he
  have hd_getD : ds.getD i [] = d := by rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
  have hd_len : d.length = initiateFullDrawLengths.getD i 0 := by
    rw [← hd_getD, length_getD_of_map_length hds]
  rcases i with _ | j
  · simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
    refine ⟨rfl, ?_⟩; dsimp only [rngEntry, List.map]
    rw [gamma_randTerm]
    simp only [Nat.reduceEqDiff, ↓reduceIte, hσ0, hd_getD]; rfl
  · simp only [List.cons_append, List.getElem?_cons_succ] at hv
    by_cases hj : j < 32
    · rw [List.getElem?_append_left (by simp [hkc_len, hj])] at hv; unfold kyberCoinEntries at hv
      rw [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at hv
      subst hv
      have hd4 : d.length = 4 := hd_len.trans (initiateFullDrawLengths_getD_succ hj)
      refine ⟨rfl, hd4, randTerm (ts + 1) 32, rfl, ?_, ?_⟩
      · rw [gamma_randTerm]
        simp only [Nat.reduceEqDiff, ↓reduceIte, hσ1, length_entropyBytes]
      · dsimp only [eventBytes]
        rw [List.head?_eq_getElem?, gamma_randTerm]
        simp only [Nat.reduceEqDiff, ↓reduceIte, hσ1, ← hd_getD]
        exact (getElem?_entropyBytes ds hj (by rw [hd_getD]; exact hd4)).symm
    · rw [List.getElem?_append_right (by simp [hkc_len]; omega)] at hv
      simp only [hkc_len] at hv
      rcases hsub : j - 32 with _ | k
      · have hj32 : j = 32 := by
          have hlt : j + 1 < ds.length := (List.getElem?_eq_some_iff.mp hd).1; omega
        subst hj32; rw [hsub] at hv; cases hv
        refine ⟨rfl, ?_⟩; dsimp only [rngEntry, List.map]
        rw [gamma_randTerm]
        simp only [Nat.reduceEqDiff, ↓reduceIte, hσ2, hd_getD]; rfl
      · rw [hsub] at hv; cases hv

abbrev aliceStart_reachable := @b5_aliceStart_reachable

end Symbolic.Swarm.CREF
