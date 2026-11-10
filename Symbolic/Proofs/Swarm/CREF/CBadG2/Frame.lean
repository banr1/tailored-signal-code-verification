/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
public import Symbolic.Proofs.Swarm.CREF.Stage1Trials -- shake: keep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Ghost Frame Agreement, Stamp Bounds, and Memo-Collision Invariance

Defines `CBadSigmaFrame`, `CBadGammaAgree`, and the stamp bound bundle `CBadStamps`, proving that
ghosts agreeing on `addr` and on `σ` below `n` produce identical `gamma'` evaluations and preserve
`MemoCollisionOn` on terms stamped below `n`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (parseTrSignalMsg)
open Symbolic.Swarm.CREF.TR.FreshSigma (updateFreshAt StampsLt MemoRel StateStampsLt VisStampsLt
  TraceEntriesLt TRSignalMsgStampsLt traceEntriesLt_knows)

/-- Ghosts `g` and `g₁` agree on `σ` at all timestamps below `n` and share `addr`. -/
def CBadSigmaFrame (g g₁ : Ghost) (n : Nat) : Prop :=
  (∀ ts < n, ∀ len, g₁.σ ts len = g.σ ts len) ∧ g₁.addr = g.addr

theorem cBadSigmaFrame_refl (g : Ghost) (n : Nat) : CBadSigmaFrame g g n :=
  ⟨fun _ _ _ => rfl, rfl⟩

theorem cBadSigmaFrame_updateFreshAt (g : Ghost) {n ts : Nat} (hn : n ≤ ts) (k : Nat)
    (m : HwBytes) : CBadSigmaFrame g { g with σ := updateFreshAt g.σ ts k m } n := by
  refine ⟨fun i hi len => ?_, rfl⟩
  have hne : i ≠ ts := by omega
  simp [updateFreshAt, hne]

/-- Ghosts `g` and `g₁` evaluate `gamma'` identically on every term satisfying `StampsLt ... n`. -/
def CBadGammaAgree (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g g₁ : Ghost) (n : Nat) :
    Prop :=
  ∀ b, StampsLt interpretation S g n b → gamma' interpretation S g₁ b = gamma' interpretation S g b

open Symbolic.Swarm.CREF.TR.FreshSigma in
theorem cbadG2_allFuns_pp2 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g g₁ : Ghost) (n : Nat)
    (hfr : CBadSigmaFrame g g₁ n) (rec1 rec2 : DY.Bytes → ConcretizedTerm) (id : Fin 12) :
    DY.Bytes.PartialProof2 (allFuns i S g id) (allFuns i S g₁ id) rec1 rec2 (MemoRel n) := by
  have ⟨hσ, haddr⟩ := hfr
  match id with
  | ⟨0, _⟩ =>
    dsimp only [allFuns, DY.Libsignal.Composed.SubF.internal]
    intro x _ h; dsimp only [concretizeRandom, MemoRel] at h ⊢
    split
    · rfl
    · next hsz =>
      simp only [hsz, ↓reduceIte] at h
      have hlt := h x.pack x.pack (g.σ x.timestamp x.size) x (List.mem_cons_self ..)
        (BytesView.view_pack x)
      rw [hσ x.timestamp hlt x.size]
  | ⟨1, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩ _ _ _; rfl
  | ⟨2, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩
    exact gConcat0_pp2 n rec1 rec2
  | ⟨3, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gDhPk_pp2 i n rec1 rec2
    | ⟨1, _⟩ => exact gDh_pp2 i n rec1 rec2
  | ⟨4, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩
    exact gKdf0_pp2 i n rec1 rec2
  | ⟨5, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩
    exact gSym0_pp2 i n rec1 rec2
  | ⟨6, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩
    exact gTrunc0_pp2 n rec1 rec2
  | ⟨7, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩
    exact gVariant0_pp2 n rec1 rec2
  | ⟨8, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gKemPk_pp2 S n rec1 rec2
    | ⟨1, _⟩ => exact gKemEncap_pp2 i n rec1 rec2
    | ⟨2, _⟩ => exact gKemSS_pp2 i S n rec1 rec2
    | ⟨3, _⟩ => exact gKemRej_pp2 S n rec1 rec2
  | ⟨9, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gVk_pp2 S n rec1 rec2
    | ⟨1, _⟩ => exact gSign_pp2 S n rec1 rec2
  | ⟨10, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gSpqrInit_pp2 S n rec1 rec2
    | ⟨1, _⟩ => exact gSpqrSendState_pp2 S n rec1 rec2
    | ⟨2, _⟩ => exact gSpqrSendKey_pp2 S n rec1 rec2
    | ⟨3, _⟩ => exact gSpqrSendMsg_pp2 S n rec1 rec2
    | ⟨4, _⟩ => exact gSpqrRecvState_pp2 S n rec1 rec2
    | ⟨5, _⟩ => exact gSpqrRecvKey_pp2 S n rec1 rec2
    | ⟨6, _⟩ => exact gSpqrChainKey_pp2 S n rec1 rec2
  | ⟨11, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩
    rcases g₁ with ⟨σ₁, addr₁⟩
    dsimp only at haddr; subst haddr
    exact gTrWire0_pp2 g n 0 [] rec1 rec2

theorem cbadG2_gammaAgree_of_sigmaFrame (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    {g g₁ : Ghost} {n : Nat} (hfr : CBadSigmaFrame g g₁ n) :
    CBadGammaAgree interpretation S g g₁ n := by
  intro b hb
  have hpf : DY.Bytes.Proof2 (concretizeAll interpretation S g) (concretizeAll interpretation S g₁) (MemoRel n) :=
    DY.Bytes.PartialProof2.combine (cbadG2_allFuns_pp2 interpretation S g g₁ n hfr _ _)
  exact hpf.prove b hb

theorem cbadG2_gamma_eq {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g g₁ : Ghost} {n : Nat}
    (hga : CBadGammaAgree interpretation S g g₁ n) {b : DY.Bytes}
    (hb : StampsLt interpretation S g n b) :
    gamma interpretation S g₁ b = gamma interpretation S g b :=
  congrArg ConcretizedTerm.bytes (hga b hb)

/-- Stamp bounds below `n` for all trace entries, visible entries, prefix terms, stored states,
salts, base keys, and `whisperTrials` terms at `(g, ms)`. -/
structure CBadStamps (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (n : Nat) : Prop where
  entries : TraceEntriesLt interpretation S g n (runTraceMoves r ms)
  vis : ∀ v ∈ runVis r ms, VisStampsLt interpretation S g n v
  pre : ∀ t ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), StampsLt interpretation S g n t
  bobBaseKeys : ∀ ek ∈ bobDoneBaseKeys (runTraceMoves r ms), StampsLt interpretation S g n ek
  states : ∀ st ∈ availableStates r (runTraceMoves r ms), StateStampsLt interpretation S g n st
  salts : ∀ s ∈ honestSalts r ms, StampsLt interpretation S g n s
  skippedLogged : ∀ i s pk ctr seed rIdx src,
    i < (runTraceMoves r ms).length →
    (runTraceMoves r ms).getEventAt DY.Libsignal.TripleRatchet.TREvent i =
      some (.SkippedKeyStored s pk ctr seed rIdx src) →
    StampsLt interpretation S g n seed ∧ StampsLt interpretation S g n pk
  own : ∀ st msg, TRSignalMsgStampsLt interpretation S g n msg →
    ∀ k ∈ ownKeys r (runTraceMoves r ms) st msg, StampsLt interpretation S g n k
  trials : ∀ msg, TRSignalMsgStampsLt interpretation S g n msg →
    ∀ ctx ∈ whisperTrials interpretation r S g (runTraceMoves r ms) msg,
      StampsLt interpretation S g n ctx.peerIk ∧
      StampsLt interpretation S g n ctx.myIk ∧
      (∀ u ∈ ctx.extra, StampsLt interpretation S g n u) ∧
      (∀ k ∈ ctx.ownSalts, StampsLt interpretation S g n k) ∧
      (∀ seed, ctx.seed? = some seed → StampsLt interpretation S g n seed)
  recvTerms : ∀ t msg, StampsLt interpretation S g n t →
    parseTrSignalMsg t = some msg →
    ∀ u ∈ t :: (whisperTrials interpretation r S g (runTraceMoves r ms) msg).flatMap
      (trialTerms (honestSalts r ms) msg),
    StampsLt interpretation S g n u

theorem CBadStamps.knows {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {n : Nat} (h : CBadStamps interpretation r S g ms n) {b : DY.Bytes}
    (hb : b.AttackerKnows (runTraceMoves r ms)) : StampsLt interpretation S g n b :=
  traceEntriesLt_knows h.entries hb

/-- `MemoCollisionOn` is invariant across `CBadGammaAgree` when `prefixTerms` and `newTerms` are
stamped below `n`. -/
theorem cbadG2_memoCollisionOn_iff {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g g₁ : Ghost} {n : Nat} (hga : CBadGammaAgree interpretation S g g₁ n)
    {known : DY.Bytes → Prop} {tr : ExecTrace} {vis : List VisEntry}
    {newTerms newPts : List DY.Bytes}
    (hpre : ∀ t ∈ prefixTerms r tr vis, StampsLt interpretation S g n t)
    (hnew : ∀ t ∈ newTerms, StampsLt interpretation S g n t) :
    MemoCollisionOn interpretation r S g₁ known tr vis newTerms newPts ↔
      MemoCollisionOn interpretation r S g known tr vis newTerms newPts := by
  have hm : ∀ L : List DY.Bytes, (∀ t ∈ L, StampsLt interpretation S g n t) →
      L.flatMap (fun t => (gamma' interpretation S g₁ t).memo) =
        L.flatMap (fun t => (gamma' interpretation S g t).memo) := by
    intro L hL
    induction L with
    | nil => rfl
    | cons a L ih =>
      simp only [List.flatMap_cons, hga a (hL a List.mem_cons_self),
        ih fun t ht => hL t (List.mem_cons_of_mem _ ht)]
  unfold MemoCollisionOn
  simp only [hm _ hnew, hm _ hpre]

end Symbolic.Swarm.CREF
