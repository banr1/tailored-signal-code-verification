/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
public import Symbolic.Proofs.Swarm.CREF.RoleSnapshots
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyFrame
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
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
# Bob's Session Base-Key Invariant Across Session Start

Proves `bksS_bobStartTr` and `bks_bobStart`: after an accepting `bobStart` block, `BobBaseKeyOn`
holds on the extended trace for the wire prekey message's base key `q.baseKey.take 33`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry at?_le_some)
open DY.Libsignal.TripleRatchet (TRState SessionInfo)

theorem bksS_getEventAt_append_self (EventT : Type)
    [ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT EventT)] (tr : ExecTrace) (ev : EventT) :
    (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT EventT)).getEventAt EventT tr.length =
      some ev := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [DY.Trace.at?_append]

theorem bksS_mem_sbkOf_link {E₁ E₂ : Type} [ExecTraceTypes.Has E₁] [ExecTraceTypes.Has E₂]
    {t : ExecTrace} {b a : Participant} {ikB ikA spk pqpk : DY.Bytes} {opk : Option DY.Bytes}
    {ek ct : DY.Bytes} {keys : PQXDH.HandshakeKeys} {x₁ : E₁} {x₂ : E₂} {s : SessionInfo} :
    ek ∈ sbkOf ((((t.append (TR.EvE (.BobDone b a ikB ikA spk pqpk opk ek ct keys))).append
      x₁).append x₂).append
        (Symbolic.Swarm.COMPOSED.CompTrace.CEvE (.HandshakeSession s t.length))) s := by
  set X₁ := t.append (TR.EvE (.BobDone b a ikB ikA spk pqpk opk ek ct keys)) with hX₁
  set X₂ := X₁.append x₁ with hX₂
  set X₃ := X₂.append x₂ with hX₃
  have hl₁ : X₁.length = t.length + 1 := by
    simp only [hX₁, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl₂ : X₂.length = t.length + 2 := by
    simp only [hX₂, hl₁, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl₃ : X₃.length = t.length + 3 := by
    simp only [hX₃, hl₂, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  unfold sbkOf
  refine List.mem_filterMap.mpr ⟨X₃.length,
    List.mem_range.mpr (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega), ?_⟩
  rw [bksS_getEventAt_append_self ComposedEvent]
  show (if s = s then _ else none) = some ek
  simp only [ ↓reduceIte]
  rw [bks_getEventAt_of_le _ (DY.Trace.append_le X₃ _) (by omega : t.length < X₃.length),
    bks_getEventAt_of_le _ (DY.Trace.append_le X₂ x₂) (by omega : t.length < X₂.length),
    bks_getEventAt_of_le _ (DY.Trace.append_le X₁ x₁) (by omega : t.length < X₁.length), hX₁,
    bksS_getEventAt_append_self PQXDH.PQXDHEvent]

theorem bksS_mem_sbkOf_preSkip (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) :
    o.ek ∈ sbkOf (bobStartPreSkipTr tr b a o msg key)
      ((bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey (randTerm tr.length 32)).sessionInfo
        b) := by
  unfold bobStartPreSkipTr
  dsimp only
  exact bksS_mem_sbkOf_link

theorem bksS_le_append₃ {E₁ E₂ E₃ : Type} [ExecTraceTypes.Has E₁] [ExecTraceTypes.Has E₂]
    [ExecTraceTypes.Has E₃] (L : ExecTrace) (x : E₁) (y : E₂) (z : E₃) :
    L ≤ ((L.append x).append y).append z :=
  DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
    (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _))

theorem bksS_preSkip_le_bobStartTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes) :
    bobStartPreSkipTr tr b a o msg key ≤ bobStartTr tr b a o msg c' spqr' key seed pqSalt m := by
  unfold bobStartTr
  dsimp only
  exact DY.Trace.le_trans _ _ _
    ((DY.Libsignal.TripleRatchet.logSkippedKeys _ _ _ _ _ _ _).run _).2.property
    (bksS_le_append₃ _ _ _ _)

theorem bksS_length_preSkip (tr : ExecTrace) (b a : Participant)
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

/-- After a successful `bobStart`, if every Bob snapshot on `bobStartTr` has `initiator = false`,
`BobBaseKeyOn` holds for `ecKey (gamma interpretation S g w.ek)`. -/
theorem bksS_bobStartTr {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx)
    (hrole : ∀ (i : Nat) (st : TRState),
      ((bobStartTr tr b a w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m).at? i :
        Option TRStEntry) = some ⟨⟨b, st⟩⟩ → st.initiator = false) :
    BobBaseKeyOn interpretation S g b
      (bobStartTr tr b a w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m)
      (ecKey (gamma interpretation S g w.ek)) := by
  refine bobBaseKeyOn_start (tr := tr) hrole ?_ ?_
  · let c := bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk
    let st_r := bobRatchetedSt a w.out.ikB w.out.ikA w.out.keys w.out.spkSk w.msg.ratchetKey
      (randTerm tr.length 32)
    let tr_hs := bobStartPreSkipTr tr b a w.out w.msg w.key
    let skipped := w.msg.counter.toNat - c.index.toNat
    let childIdx := tr_hs.length + skipped + 2
    let tr_skip := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st_r.sessionInfo b) w.msg.ratchetKey
      c.rIdx childIdx c.chainKey c.index skipped).run tr_hs).2.val
    let tr_recv := tr_skip.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
      (.Received b st_r.peer w.msg.ratchetKey w.msg.counter w.m))
    let tr_mk := tr_recv.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
      (.MessageKey (st_r.sessionInfo b) .receiver w.seed w.pqSalt w.msg.counter c.rIdx
        childIdx))
    have hle : tr.length ≤ tr_mk.length :=
      Nat.le_trans (bksS_length_preSkip tr b a w.out w.msg w.key)
        (Nat.le_trans (DY.Trace.length_le _ _
          ((DY.Libsignal.TripleRatchet.logSkippedKeys (st_r.sessionInfo b) w.msg.ratchetKey
            c.rIdx childIdx c.chainKey c.index skipped).run tr_hs).2.property)
          (by
            simp only [tr_mk, tr_recv, tr_skip, Symbolic.DYBridge.DY.Trace.append_eq_1,
              Symbolic.DYBridge.DY.Trace.length_eq_2]
            omega))
    exact ⟨tr_mk.length, rpkR_finalSt w, hle,
      DY.Trace.at?_append tr_mk (Symbolic.Swarm.COMPOSED.CompTrace.TRStE b (rpkR_finalSt w))⟩
  · intro j st hj hat
    rcases rpkBH_trStateStoredAt_bobStartTr w hat with ⟨hlt, _⟩ | ⟨_, _, rfl⟩
    · omega
    · rw [sessionBaseKeys_eq_sbkOf hat]
      exact sbkOf_mono (bksS_preSkip_le_bobStartTr _ _ _ _ _ _ _ _ _ _ _) _
        (bksS_mem_sbkOf_preSkip tr b a w.out w.msg w.key)

/-- For an accepting `[recv b, rng d, accept pt]` explanation block `pre ++ m :: post` with `m`
a `BobStartBy r.bob` move surrounded by `InvisibleNoEffect` moves, `BobBaseKeyOn` holds on the
resulting trace for `q.baseKey.take 33`. -/
theorem bks_bobStart {interpretation : ExternInterpretation} {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc : List MachineEvent} {b d pt : HwBytes} {q : Composed.Refinement.PreKeyFields}
    (hq : parsePreKeyWire b = some q)
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc
      [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hbs : BobStartBy r.bob m)
    (hrole : RoleSnapshots r (runTraceMoves r (ms₀ ++ (pre ++ m :: post)))) :
    BobBaseKeyOn interpretation S g r.bob (runTraceMoves r (ms₀ ++ (pre ++ m :: post)))
      (q.baseKey.take 33) := by
  cases m with
  | bobStart p a kh regA mh pqIdx spqrMsgIdx shown =>
    have hp : p = r.bob := hbs
    subst hp
    obtain ⟨hF, ⟨w⟩⟩ := rpkT_bobStart_block hB hpre
    obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 :=
      ⟨shown - 1, by have := rpkT_bobStart_shown_pos hB; omega⟩
    rw [← rpkT_bobStart_gamma w hF hq]
    let m₀ : Move := .bobStart r.bob a kh regA mh pqIdx spqrMsgIdx (k + 1)
    have htr_pre : (runMoves pre (runTraceMoves r ms₀)).1 = runTraceMoves r (ms₀ ++ pre) :=
      (DY.Libsignal.Composed.Refinement.runTrace_append r ms₀ pre).symm
    have htr₁ : runTraceMoves r (ms₀ ++ pre ++ [m₀]) = m₀.next (runMoves pre (runTraceMoves r ms₀)).1 := by
      rw [htr_pre, DY.Libsignal.Composed.Refinement.runTrace_snoc]
    have htr_end : runTraceMoves r (ms₀ ++ (pre ++ m₀ :: post)) =
        (runMoves post (runTraceMoves r (ms₀ ++ pre ++ [m₀]))).1 := by
      have hassoc : ms₀ ++ (pre ++ m₀ :: post) = (ms₀ ++ pre ++ [m₀]) ++ post := by
        simp [List.append_assoc]
      rw [hassoc, DY.Libsignal.Composed.Refinement.runTrace_append]
    have hpost_no : MovesFrom (fun tr m => NoSessionEffect tr m)
        (runTraceMoves r (ms₀ ++ pre ++ [m₀])) post := by
      rw [htr₁]
      exact movesFrom_mono (fun _ _ h => h.2) _ post hpost
    have hle_post : runTraceMoves r (ms₀ ++ pre ++ [m₀]) ≤
        runTraceMoves r (ms₀ ++ (pre ++ m₀ :: post)) := by
      rw [htr_end]
      exact bksF_le_runMoves _ post
    have hnew_post : NewBobSinfo r.bob (runTraceMoves r (ms₀ ++ pre ++ [m₀]))
        (runTraceMoves r (ms₀ ++ (pre ++ m₀ :: post))) := by
      rw [htr_end]
      exact newBobSinfo_of_movesFrom_noSessionEffect hpost_no
    have htr : runTraceMoves r (ms₀ ++ pre ++ [m₀]) =
        bobStartTr (runTraceMoves r (ms₀ ++ pre)) r.bob a w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt
          w.m := by
      rw [DY.Libsignal.Composed.Refinement.runTrace_snoc, w.next_eq]
    have hrole₁ : ∀ (i : Nat) (st : TRState),
        ((bobStartTr (runTraceMoves r (ms₀ ++ pre)) r.bob a w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt
          w.m).at? i : Option TRStEntry) = some ⟨⟨r.bob, st⟩⟩ → st.initiator = false := by
      intro i st hat
      rw [← htr] at hat
      have hat' := at?_le_some hle_post hat
      rw [hrole r.bob st i hat']
      exact decide_eq_false (Ne.symm hwf.1)
    have h1 := bksS_bobStartTr (interpretation := interpretation) (S := S) (g := g) w hrole₁
    rw [← htr] at h1
    exact bobBaseKeyOn_ext hle_post hnew_post h1
  | _ => exact False.elim hbs

end Symbolic.Swarm.CREF
