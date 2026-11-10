/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
public import ProofLib.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import VCVio.Prelude.Core

/-!
# Pure Triple-Ratchet Ghost, Prefix, and Session-State Definitions

Machine-free prefix-matching algebra, `gamma` address-independence predicates, and Triple Ratchet
session-state relations (`sessionOf`, `StateRel`, `TRKeyShape`, `IkShape`, `TRNsBound`) over the
composed model (`DY.Libsignal.Composed`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)

abbrev spqrNode := opaqueNode

/-! ## `ModelTraces` Append Algebra and `MatchedPrefix` Extension -/

theorem runMoves_append (ms₁ ms₂ : List Move) (tr : ExecTrace) :
    runMoves (ms₁ ++ ms₂) tr =
      ((runMoves ms₂ (runMoves ms₁ tr).1).1,
        (runMoves ms₁ tr).2 ++ (runMoves ms₂ (runMoves ms₁ tr).1).2) := by
  induction ms₁ generalizing tr with
  | nil => simp [runMoves]
  | cons m ms₁ ih =>
    simp only [List.cons_append, runMoves, ih, List.append_assoc]

theorem runTrace_append (r₀ : ProtocolSetup) (ms₁ ms₂ : List Move) :
    runTraceMoves r₀ (ms₁ ++ ms₂) = (runMoves ms₂ (runTraceMoves r₀ ms₁)).1 := by
  unfold runTraceMoves
  rw [← List.cons_append, runMoves_append]

theorem runVis_append (r₀ : ProtocolSetup) (ms₁ ms₂ : List Move) :
    runVis r₀ (ms₁ ++ ms₂) = runVis r₀ ms₁ ++ (runMoves ms₂ (runTraceMoves r₀ ms₁)).2 := by
  unfold runVis runTraceMoves
  rw [← List.cons_append, runMoves_append]

theorem runTrace_snoc (r₀ : ProtocolSetup) (ms : List Move) (m : Move) :
    runTraceMoves r₀ (ms ++ [m]) = m.next (runTraceMoves r₀ ms) := by
  rw [runTrace_append]
  rfl

theorem runVis_snoc (r₀ : ProtocolSetup) (ms : List Move) (m : Move) :
    runVis r₀ (ms ++ [m]) = runVis r₀ ms ++ m.vis (runTraceMoves r₀ ms) := by
  rw [runVis_append]
  simp [runMoves]

/-- Extending Stage-1 `MatchedPrefix` by a single move `m` whose `m.vis` entries match `evs`. -/
theorem matchedPrefix_snoc {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {m : Move}
    {τ evs : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms τ)
    (hrun : ModelRun r₀ (ms ++ [m]))
    (hrole : RoleFaithful r₀ who (ms ++ [m]))
    (hpath : PathFaithful interpretation r₀ S g (ms ++ [m]) (τ ++ evs))
    (hread : ReadFaithful interpretation r₀ S g (ms ++ [m]) (τ ++ evs))
    (hevs : List.Forall₂ (EventMatchesEntry interpretation r₀ S g) evs
      (m.vis (runTraceMoves r₀ ms))) :
    MatchedPrefix interpretation r₀ S who g (ms ++ [m]) (τ ++ evs) := by
  refine ⟨hmp.1, hrun, hrole, hpath, hread, ?_⟩
  rw [runVis_snoc]
  exact List.rel_append hmp.2.2.2.2.2 hevs

/-- Extending Stage-1 `MatchedPrefix` by a non-call, non-recv environment move (`attackerSend`,
`compromise*`, `expose*`) whose `m.vis` entries have `kind ≠ .recv`, `kind ≠ .pt`. -/
theorem matchedPrefix_snoc_env {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {m : Move}
    {τ evs : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms τ)
    (hrun : ModelRun r₀ (ms ++ [m]))
    (hparty : m.party? = none)
    (hpath_none : m.prekeyPath? = none)
    (hnocs : ∀ ev ∈ evs, eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt)
    (hnorecv : ∀ v ∈ m.vis (runTraceMoves r₀ ms), v.kind ≠ .recv)
    (hevs : List.Forall₂ (EventMatchesEntry interpretation r₀ S g) evs
      (m.vis (runTraceMoves r₀ ms))) :
    MatchedPrefix interpretation r₀ S who g (ms ++ [m]) (τ ++ evs) := by
  have hrole : RoleFaithful r₀ who (ms ++ [m]) :=
    Stage1Wire.roleFaithful_snoc hmp.2.2.1 (fun p hp => by rw [hparty] at hp; cases hp)
  have hcs_nil : callStarts evs = [] := by
    unfold callStarts
    refine List.filter_eq_nil_iff.mpr fun ev hev => ?_
    obtain ⟨hnr, hnp⟩ := hnocs ev hev
    cases hk : eventKind ev <;> simp_all
  have hpath_τ : PathFaithful interpretation r₀ S g (ms ++ [m]) (τ ++ evs) := by
    have hp1 := Stage1Wire.pathFaithful_snoc_of_prekeyPath_none hmp.2.2.2.1 hpath_none
    intro i m' promote b p hi hpr hcs hp
    have hcs' : (callStarts τ)[callCount (runVis r₀ ((ms ++ [m]).take i))]? = some (.recv b) := by
      have happ : callStarts (τ ++ evs) = callStarts τ ++ callStarts evs := by
        unfold callStarts; exact List.filter_append ..
      rw [happ, hcs_nil, List.append_nil] at hcs
      exact hcs
    exact hp1 i m' promote b p hi hpr hcs' hp
  have hread : ReadFaithful interpretation r₀ S g (ms ++ [m]) (τ ++ evs) :=
    Stage1Wire.readFaithful_append_no_recv hmp.2.2.2.2.2.length_eq
      (by simpa [runMoves] using hnorecv)
      hmp.2.2.2.2.1
  exact matchedPrefix_snoc hmp hrun hrole hpath_τ hread hevs

/-! ## `gamma` Address-Independence (`NoTrWire`) -/

/-- Every memo entry in `res` has no `DY.TrWire.TrWireMsg.SubF` head. -/
def MemoNoTrWire (res : ConcretizedTerm) : Prop :=
  ∀ (sub sh : DY.Bytes) (v : HwBytes),
    (sub, sh, v) ∈ res.memo → (sub.view? DY.TrWire.TrWireMsg.SubF).isNone = true

/-- Term `t` contains no `trWireMsg` subterm. -/
def NoTrWire (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (t : DY.Bytes) : Prop :=
  MemoNoTrWire (gamma' interpretation S g t)

attribute [local irreducible]  node opaqueNode spqrKeyNode

/-! ## Triple Ratchet State and Record Relations -/

open DY.Libsignal.TripleRatchet

abbrev serializedKey (b : HwBytes) : HwBytes := ecKey b

def sessionOf (interpretation : ExternInterpretation) (gam : DY.Bytes → HwBytes) (st : TRState) :
    SessionRec :=
  let sk := clamp (gam st.dhs)
  { sessionVersion := 4
    localIdentityPublic := serializedKey ((gam st.myIk).drop 1)
    remoteIdentityPublic := serializedKey ((gam st.peerIk).drop 1)
    rootKey := gam st.rk
    previousCounter := st.pn.toBitVec
    senderChain := some
      { senderRatchetKey := serializedKey ((interpretation
          DY.Libsignal.Refinement.x25519PublicKeySymbol [sk]).getD [])
        senderRatchetKeyPrivate := sk
        chainKey := some (st.ns.toBitVec, gam st.cks)
        messageKeys := [] }
    receiverChains := st.recv.map fun c =>
      { senderRatchetKey := serializedKey (gam c.ratchetKey)
        senderRatchetKeyPrivate := []
        chainKey := some (c.index.toBitVec, gam c.chainKey)
        messageKeys := [] }
    pendingPreKey := none
    pendingKyberPreKey := none
    remoteRegistrationId := 0
    localRegistrationId := 0
    aliceBaseKey := []
    pqRatchetState := gam st.spqr }

def eraseUnmodelled (s : SessionRec) : SessionRec :=
  { s with
    aliceBaseKey := []
    remoteRegistrationId := 0
    localRegistrationId := 0
    pendingPreKey := none
    pendingKyberPreKey := none }

def eraseSkipped (s : SessionRec) : SessionRec :=
  { s with receiverChains := s.receiverChains.map fun c => { c with messageKeys := [] } }

def StateRel (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (st : TRState)
    (rec : RecordRec) : Prop :=
  rec.previous = [] ∧
    eraseSkipped (eraseUnmodelled rec.current) = sessionOf interpretation (gamma interpretation S g) st

def sentBodies (acc : List MachineEvent) : List HwBytes :=
  acc.filterMap fun
    | .send m => sentBody m
    | _ => none

@[simp] theorem sentBodies_nil : sentBodies [] = [] := rfl

@[simp] theorem sentBodies_append (a b : List MachineEvent) :
    sentBodies (a ++ b) = sentBodies a ++ sentBodies b := by
  simp [sentBodies, List.filterMap_append]

structure TRKeyShape (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (st : TRState) : Prop where
  dhs_len : (gamma interpretation S g st.dhs).length = 32
  cks_len : (gamma interpretation S g st.cks).length = 32
  myIk_ser :
    serializedKey ((gamma interpretation S g st.myIk).drop 1) = gamma interpretation S g st.myIk
  peerIk_ser :
    serializedKey ((gamma interpretation S g st.peerIk).drop 1) = gamma interpretation S g st.peerIk

def IkShape (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) : Prop :=
  (pubBytes interpretation (secretBytes r₀ 0)).length = 32 ∧
  (pubBytes interpretation (secretBytes r₀ 2)).length = 32

def TRNsBound (r₀ : ProtocolSetup) (ms : List Move) (sent : List HwBytes) : Prop :=
  ∀ (p : Participant) (stateIdx : Nat) (st : TRState),
    ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms)).1 =
      some st →
    st.ns.toNat ≤ sent.length

end Symbolic.Swarm.CREF.TR
