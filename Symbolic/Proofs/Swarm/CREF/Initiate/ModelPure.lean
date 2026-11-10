/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Sanitize
public import Symbolic.Proofs.Swarm.CREF.ReadFaithful
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
public import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35CliPure
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaHead
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix

/-!
# Model-Side Explanations for `session_initiate`

Proves `MatchedPrefix` and `ExplainsMoves` extensions for rejected (`ini_explains_reject`) and
accepted (`ini_explains_initOk`) `session_initiate` calls, `aliceStart` visible-entry normalization
to `shown = 35`, and `DeltaFaithful` extraction on `XplBlock`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.IniPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (x25519LowOrder)

theorem ini_callStarts_blk (b : HwBytes) (ds : List HwBytes) :
    callStarts (.recv b :: ds.map MachineEvent.rng) = [.recv b] :=
  callStarts_initiate_block b ds

/-! ## `ReadFaithful` and `aliceStart` visible-entry normalization -/

theorem iniReadOKWith_of_layout {R : HwBytes → Set DY.Bytes} {P : HwBytes → Set PreKeyRep}
    {e : MachineEvent} {v : VisEntry}
    (hl : v.layout = .bundle ∨ v.layout = .unconstrained) :
    ReadOKWith R P e v := by
  unfold ReadOKWith
  rcases hl with hl | hl <;> rw [hl] <;> trivial

theorem ini_aliceDraws_kind {done : Option Nat} :
    ∀ {L : List DY.Bytes} {v : VisEntry}, v ∈ aliceDraws done L → v.kind = .rng
  | [], _, hv => by simp [aliceDraws] at hv
  | [_], _, hv => by rcases List.mem_singleton.mp hv with rfl; rfl
  | _ :: _ :: _, _, hv => by
    simp only [aliceDraws, List.cons_append, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · rfl
    · unfold kyberCoinEntries at hv
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      rfl

theorem iniReadOKWith_aliceStart {R : HwBytes → Set DY.Bytes} {P : HwBytes → Set PreKeyRep}
    {tr : ExecTrace} {a b : Participant} {idStateIdx regIdxB : Nat}
    {bh : DY.Libsignal.PQXDH.BundleHandles} {shown : Nat} {e : MachineEvent} {v : VisEntry}
    (hv : v ∈ (Move.aliceStart a b idStateIdx regIdxB bh shown).vis tr)
    (hk : v.kind = .recv) : ReadOKWith R P e v := by
  unfold Move.vis at hv
  rcases List.mem_append.mp hv with hv | hv
  · have hv' := List.mem_of_mem_take hv
    unfold aliceVis at hv'
    rcases List.mem_cons.mp hv' with rfl | hv'
    · exact iniReadOKWith_of_layout (Or.inl rfl)
    · rw [ini_aliceDraws_kind hv'] at hk
      cases hk
  · rw [xpl_exposures_kind hv] at hk
    cases hk

theorem ini_aliceDraws_length_le_34 (done : Option Nat) :
    ∀ (L : List DY.Bytes), (aliceDraws done L).length ≤ 34
  | [] | [_] => by simp [aliceDraws]
  | _ :: _ :: _ => by
    simp only [aliceDraws, List.length_cons, List.length_append, kyberCoinEntries,
      List.length_map, List.length_range, List.length_take]
    omega

theorem ini_aliceVis_length_le_35 (tr tr' : ExecTrace) (bh : DY.Libsignal.PQXDH.BundleHandles) :
    (aliceVis tr tr' bh).length ≤ 35 := by
  simp only [aliceVis, List.length_cons]
  have := ini_aliceDraws_length_le_34 (eventIdx isAliceDone tr tr') ((newRandoms tr tr').map (·.1))
  omega

theorem ini_aliceStart_next_eq_35 (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) (tr : ExecTrace) :
    (Move.aliceStart a b idStateIdx regIdxB bh shown).next tr =
      (Move.aliceStart a b idStateIdx regIdxB bh 35).next tr := rfl

theorem ini_aliceStart_vis_eq_35 (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : DY.Libsignal.PQXDH.BundleHandles) {shown : Nat} (hshown : 35 ≤ shown)
    (tr : ExecTrace) :
    (Move.aliceStart a b idStateIdx regIdxB bh shown).vis tr =
      (Move.aliceStart a b idStateIdx regIdxB bh 35).vis tr := by
  have h1 : exposures tr ((Move.aliceStart a b idStateIdx regIdxB bh shown).next tr) = [] :=
    exposures_nil_of_not_leakKind rfl (fun h => nomatch h)
  have h2 : exposures tr ((Move.aliceStart a b idStateIdx regIdxB bh 35).next tr) = [] :=
    exposures_nil_of_not_leakKind rfl (fun h => nomatch h)
  have hlen := ini_aliceVis_length_le_35 tr
    ((Move.aliceStart a b idStateIdx regIdxB bh 35).next tr) bh
  rw [xpl_vis_eq, xpl_vis_eq, h1, h2, List.append_nil, List.append_nil]
  dsimp only [xpl_ownVis]
  rw [ini_aliceStart_next_eq_35, List.take_of_length_le (Nat.le_trans hlen hshown),
    List.take_of_length_le hlen]

/-! ## `sanitizeMoves` lifts for `PathFaithful`, `MatchedPrefix`, and `ExplainsMoves` -/

theorem prekeyPath?_of_clearStuckWrap {tr : ExecTrace} {m : Move} {promote : Bool}
    (hp : (Sanitize.clearStuckWrap tr m).prekeyPath? = some promote) :
    m.prekeyPath? = some promote := by
  cases m <;> simp only [Sanitize.clearStuckWrap, Move.prekeyPath?] at hp ⊢
  all_goals try exact hp
  · split at hp
    · obtain ⟨hw, _⟩ := Bool.and_eq_true_iff.mp ‹_›; rw [hw]; exact hp
    · cases hp
  · split at hp
    · obtain ⟨hw, _⟩ := Bool.and_eq_true_iff.mp ‹_›; rw [hw]; exact hp
    · cases hp

theorem pathFaithful_sanitizeMoves {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (hp : PathFaithful interpretation r S g ms acc) :
    PathFaithful interpretation r S g (Sanitize.sanitizeMoves (setupTrace r) ms) acc := by
  intro i m' promote b p hi hpath hcall hparse
  rw [Sanitize.getElem?_sanitizeMoves] at hi
  rcases hmi : ms[i]? with _ | m
  · simp [hmi] at hi
  · simp only [hmi, Option.map_some, Option.some.injEq] at hi
    subst hi
    simp only [Sanitize.sanitizeMoves_take, Sanitize.runVis_sanitizeMoves,
      Sanitize.runTrace_sanitizeMoves] at hcall ⊢
    exact hp i m promote b p hmi (prekeyPath?_of_clearStuckWrap hpath) hcall hparse

theorem matchedPrefix_sanitizeMoves {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (hm : MatchedPrefix interpretation r S who g ms acc) :
    MatchedPrefix interpretation r S who g (Sanitize.sanitizeMoves (setupTrace r) ms) acc :=
  ⟨hm.1, Sanitize.modelRun_sanitizeMoves hm.2.1, Sanitize.roleFaithful_sanitizeMoves hm.2.2.1,
    pathFaithful_sanitizeMoves hm.2.2.2.1, Sanitize.readFaithful_sanitizeMoves hm.2.2.2.2.1,
    by simpa only [Sanitize.runVis_sanitizeMoves] using hm.2.2.2.2.2⟩

theorem explains_sanitizeMoves {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent}
    (hex : ExplainsMoves interpretation r S who ok g ms acc) :
    ExplainsMoves interpretation r S who ok g (Sanitize.sanitizeMoves (setupTrace r) ms) acc :=
  ⟨matchedPrefix_sanitizeMoves hex.1, Sanitize.outcomeFaithful_sanitizeMoves hex.2⟩

theorem pathFaithful_snoc_blk_none {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {m_new : Move} {acc blk : List MachineEvent}
    (hp : PathFaithful interpretation r S g ms acc)
    (hlt_pre : ∀ i m promote, ms[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms.take i)) < (callStarts acc).length)
    (hm_new : m_new.prekeyPath? = none) :
    PathFaithful interpretation r S g (ms ++ [m_new]) (acc ++ blk) := by
  intro i m promote b p hi hpath hcall hparse
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hcall ⊢
    have hk := hlt_pre i m promote hi hpath
    rw [callStarts_append, List.getElem?_append_left hk] at hcall
    exact hp i m promote b p hi hpath hcall hparse
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
    rcases heq : i - ms.length with _ | _
    · rw [heq, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; rw [hm_new] at hpath; cases hpath
    · rw [heq] at hi; simp at hi

theorem callCount_take_lt_snoc_none {r : ProtocolSetup} {ms : List Move} {m_none : Move} {n : Nat}
    (hlt : ∀ i m promote, ms[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms.take i)) < n)
    (hm_none : m_none.prekeyPath? = none) :
    ∀ i m promote, (ms ++ [m_none])[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r ((ms ++ [m_none]).take i)) < n := by
  intro i m promote hi hpath
  by_cases hlt_i : i < ms.length
  · rw [List.getElem?_append_left hlt_i] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt_i)]
    exact hlt i m promote hi hpath
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt_i)] at hi
    rcases heq : i - ms.length with _ | _
    · rw [heq, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; rw [hm_none] at hpath; cases hpath
    · rw [heq] at hi; simp at hi

/-! ## Rejected `session_initiate` explanations -/

theorem ini_matchedPrefix_reject_of_lt {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (b : HwBytes) (ds : List HwBytes)
    (hm : MatchedPrefix interpretation r S who g ms acc)
    (hlt_pre : ∀ i m promote, ms[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms.take i)) < (callStarts acc).length) :
    MatchedPrefix interpretation r S who g (ms ++ [.reject (ds.map List.length)])
      (acc ++ (.recv b :: ds.map MachineEvent.rng)) :=
  matchedPrefix_append_reject hm hlt_pre b ds

/-- Extends `MatchedPrefix` across a rejected `session_initiate` call by appending
`reject (ds.map List.length)` to `sanitizeMoves (setupTrace r) ms`. -/
theorem ini_matchedPrefix_reject (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (b : HwBytes) (ds : List HwBytes)
    (hm : MatchedPrefix interpretation r S who g ms acc) :
    MatchedPrefix interpretation r S who g
      (Sanitize.sanitizeMoves (setupTrace r) ms ++ [.reject (ds.map List.length)])
      (acc ++ (.recv b :: ds.map MachineEvent.rng)) :=
  ini_matchedPrefix_reject_of_lt b ds (matchedPrefix_sanitizeMoves hm)
    fun _ _ _ hi hp => Sanitize.callCount_take_lt_of_sanitizeMoves_prekeyPath? hm hi hp

/-- Extends `ExplainsMoves` across a failed `session_initiate` call (`ok (callStarts acc).length = false`). -/
theorem ini_explains_reject (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (acc : List MachineEvent) (b : HwBytes) (ds : List HwBytes)
    (hex : ExplainsMoves interpretation r S who ok g ms acc)
    (hok : ok (callStarts acc).length = false) :
    ExplainsMoves interpretation r S who ok g
      (Sanitize.sanitizeMoves (setupTrace r) ms ++ [.reject (ds.map List.length)])
      (acc ++ (.recv b :: ds.map MachineEvent.rng)) := by
  have hex' := explains_sanitizeMoves hex
  refine ⟨ini_matchedPrefix_reject interpretation r S who g ms acc b ds hex.1,
    outcomeFaithful_snoc_reject (ds.map List.length) hex'.2 ?_⟩
  rwa [callCount_eq_callStarts_length hex'.1.2.2.2.2.2]

/-! ## Accepted `session_initiate` explanations (`aliceStart` at `shown = 35`) -/

theorem ini_moveOK_aliceStart_35 {r : ProtocolSetup} {ms : List Move}
    (hNe : r.alice ≠ r.bob) (hreach : (runTraceMoves r ms).Reachable reachability)
    {oi : Option Nat} {opk : Option DY.Bytes}
    (hopk : NetOpt (runTraceMoves r ms) oi opk)
    (hlow : (opk.all fun o => !x25519LowOrder o) = true) :
    MoveOK r (runTraceMoves r ms)
      (.aliceStart r.alice r.bob 4 6
        { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi } 35) := by
  have hm := moveOK_aliceStart_35_on_runTrace hNe hopk hlow
  exact ⟨rfl, aliceStart_reachable hreach _ _ _ _ _ _, hm.2.1, rfl, rfl,
    by simp [Move.MatchesSetupPeer], fun _ _ _ h => nomatch h⟩

theorem ini_aliceStart_ext_of_lt (interpretation : ExternInterpretation) (hext : PureExternContracts interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (who : List Participant) (g : Ghost) (ms ms_opk : List Move) (acc : List MachineEvent)
    (bundle : HwBytes) (ds : List HwBytes) (oi : Option Nat) (opk : Option DY.Bytes)
    (hok : IniOkBin bundle ds)
    (hm : MatchedPrefix interpretation r (compSemOf interpretation r) who g (ms ++ ms_opk) acc)
    (hwho : who[(callStarts acc).length]? = some r.alice)
    (hlt_pre : ∀ i m promote, (ms ++ ms_opk)[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r ((ms ++ ms_opk).take i)) < (callStarts acc).length)
    (hopk : NetOpt (runTraceMoves r (ms ++ ms_opk)) oi opk)
    (hlow : (opk.all fun o => !x25519LowOrder o) = true)
    (hBM : ∀ g' : Ghost, g'.addr = g.addr →
      (∀ i j, i < (runTraceMoves r (ms ++ ms_opk)).length → g'.σ i j = g.σ i j) →
      PreKeyBundleLayoutMatches interpretation (compSemOf interpretation r) g' bundle
        (received (runTraceMoves r (ms ++ ms_opk)) ([14, 15, 20, 21] ++ oi.toList))) :
    ∃ g' : Ghost, g'.addr = g.addr ∧
      (∀ i j, i < (runTraceMoves r (ms ++ ms_opk)).length → g'.σ i j = g.σ i j) ∧
      MatchedPrefix interpretation r (compSemOf interpretation r) who g'
        (ms ++ ms_opk ++ [.aliceStart r.alice r.bob 4 6
          { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi } 35])
        (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) := by
  let _ := hext
  let ms₁ := ms ++ ms_opk
  let ts := (runTraceMoves r ms₁).length
  let entropy := entropyBytes ds
  let g₁ : Ghost := { g with σ := TR.FreshSigma.updateFreshAt g.σ ts 32 (ds.getD 0 []) }
  let g₂ : Ghost := { g₁ with σ := TR.FreshSigma.updateFreshAt g₁.σ (ts + 1) 32 entropy }
  let g' : Ghost := { g₂ with σ := TR.FreshSigma.updateFreshAt g₂.σ (ts + 2) 32 (ds.getD 33 []) }
  have hm₁ : MatchedPrefix interpretation r (compSemOf interpretation r) who g₁ ms₁ acc :=
    TR.FreshSigma.matchedPrefix_updateFreshAt hm (Nat.le_refl ts) 32 (ds.getD 0 [])
  have hm₂ : MatchedPrefix interpretation r (compSemOf interpretation r) who g₂ ms₁ acc :=
    TR.FreshSigma.matchedPrefix_updateFreshAt hm₁ (Nat.le_succ ts) 32 entropy
  have hm' : MatchedPrefix interpretation r (compSemOf interpretation r) who g' ms₁ acc :=
    TR.FreshSigma.matchedPrefix_updateFreshAt hm₂ (by omega) 32 (ds.getD 33 [])
  have hσ_lt : ∀ i j, i < ts → g'.σ i j = g.σ i j := by
    intro i j hi
    simp [g', g₂, g₁, TR.FreshSigma.updateFreshAt, show i ≠ ts + 2 by omega,
      show i ≠ ts + 1 by omega, show i ≠ ts by omega]
  have hσ0 : g'.σ ts 32 = ds.getD 0 [] := by
    simp [g', g₂, g₁, TR.FreshSigma.updateFreshAt]
  have hσ1 : g'.σ (ts + 1) 32 = entropy := by
    simp [g', g₂, TR.FreshSigma.updateFreshAt]
  have hσ2 : g'.σ (ts + 2) 32 = ds.getD 33 [] := by
    simp [g', TR.FreshSigma.updateFreshAt]
  have hwho' : who[callCount (runVis r ms₁)]? = some r.alice := by
    rwa [callCount_eq_callStarts_length hm'.2.2.2.2.2]
  have hrf' : ReadFaithful interpretation r (compSemOf interpretation r) g'
      (ms₁ ++ [.aliceStart r.alice r.bob 4 6
        { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi } 35])
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) := by
    refine readFaithful_append (List.Forall₂.length_eq hm'.2.2.2.2.2) hm'.2.2.2.2.1
      fun ⟨e, v⟩ hev hk => ?_
    have hv : v ∈ (runMoves [.aliceStart r.alice r.bob 4 6
        { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := oi } 35]
        (runTraceMoves r ms₁)).2 := (List.of_mem_zip hev).2
    simp only [runMoves, List.append_nil] at hv
    exact iniReadOKWith_aliceStart hv hk
  refine ⟨g', rfl, hσ_lt, hm'.1,
    modelRun_snoc r ms₁ _ hm'.2.1
      (ini_moveOK_aliceStart_35 hwf.1 (b5_modelRun_reachable hm'.2.1) hopk hlow),
    roleFaithful_snoc_party hm'.2.2.1 rfl hwho',
    pathFaithful_snoc_blk_none hm'.2.2.2.1 hlt_pre rfl,
    hrf', ?_⟩
  rw [runVis_snoc, vis_aliceStart_35_on_runTrace hwf.1 hopk hlow]
  refine List.rel_append hm'.2.2.2.2.2 (.cons ⟨rfl, hBM g' rfl hσ_lt⟩ ?_)
  exact ini_forall₂_initiate_rng_34 interpretation r (compSemOf interpretation r) g' ts ds
    hok.lens hσ0 hσ1 hσ2

/-- Extends `MatchedPrefix` across an accepted `session_initiate` call by appending an optional OPK
`attackerSend` and `aliceStart r.alice r.bob 4 6 bh 35`. -/
theorem ini_matchedPrefix_initOk (interpretation : ExternInterpretation) (hext : PureExternContracts interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (who : List Participant) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (bundle : HwBytes) (ds : List HwBytes)
    (hm : MatchedPrefix interpretation r (compSemOf interpretation r) who g ms acc)
    (hwho : who[(callStarts acc).length]? = some r.alice)
    (hhon : HonestBundle interpretation r bundle) (hok : IniOkBin bundle ds) :
    let ms₀ := Sanitize.sanitizeMoves (setupTrace r) ms
    ∃ (ms_opk : List Move) (bh : DY.Libsignal.PQXDH.BundleHandles) (g' : Ghost),
      (ms_opk = [] ∨ ∃ t, ms_opk = [.attackerSend t] ∧ t.AttackerKnows (runTraceMoves r ms₀)) ∧
      g'.addr = g.addr ∧ (∀ i j, i < (runTraceMoves r ms).length → g'.σ i j = g.σ i j) ∧
      MatchedPrefix interpretation r (compSemOf interpretation r) who g'
        (ms₀ ++ ms_opk ++ [.aliceStart r.alice r.bob 4 6 bh 35])
        (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) := by
  intro ms₀
  have hm₀ : MatchedPrefix interpretation r (compSemOf interpretation r) who g ms₀ acc :=
    matchedPrefix_sanitizeMoves hm
  have hlt₀ : ∀ i m promote, ms₀[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms₀.take i)) < (callStarts acc).length :=
    fun _ _ _ hi hp => Sanitize.callCount_take_lt_of_sanitizeMoves_prekeyPath? hm hi hp
  obtain ⟨ms_opk, oi, opk, hms, hm₁, hopk, hlow, hBM⟩ :=
    ini_opkChoice interpretation hext r hwf who g ms₀ acc bundle ds hm₀ hhon hok
  have hlt₁ : ∀ i m promote, (ms₀ ++ ms_opk)[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r ((ms₀ ++ ms_opk).take i)) < (callStarts acc).length := by
    rcases hms with rfl | ⟨t, rfl, _⟩
    · simpa using hlt₀
    · exact callCount_take_lt_snoc_none hlt₀ rfl
  obtain ⟨g', haddr, hσ, hm''⟩ :=
    ini_aliceStart_ext_of_lt interpretation hext r hwf who g ms₀ ms_opk acc bundle ds oi opk hok
      hm₁ hwho hlt₁ hopk hlow hBM
  refine ⟨ms_opk, _, g', hms, haddr, fun i j hi => ?_, hm''⟩
  rw [← Sanitize.runTrace_sanitizeMoves r ms] at hi
  exact hσ i j (Nat.lt_of_lt_of_le hi (DY.Trace.length_le _ _ (runTrace_le_append r ms₀ ms_opk)))

/-- Extends `ExplainsMoves` across an accepted `session_initiate` call (`ok (callStarts acc).length = true`). -/
theorem ini_explains_initOk (interpretation : ExternInterpretation) (hext : PureExternContracts interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (acc : List MachineEvent) (bundle : HwBytes) (ds : List HwBytes)
    (hex : ExplainsMoves interpretation r (compSemOf interpretation r) who ok g ms acc)
    (hwho : who[(callStarts acc).length]? = some r.alice)
    (hok_call : ok (callStarts acc).length = true)
    (hhon : HonestBundle interpretation r bundle) (hok : IniOkBin bundle ds) :
    let ms₀ := Sanitize.sanitizeMoves (setupTrace r) ms
    ∃ (ms_opk : List Move) (bh : DY.Libsignal.PQXDH.BundleHandles) (g' : Ghost),
      (ms_opk = [] ∨ ∃ t, ms_opk = [.attackerSend t] ∧ t.AttackerKnows (runTraceMoves r ms₀)) ∧
      g'.addr = g.addr ∧ (∀ i j, i < (runTraceMoves r ms).length → g'.σ i j = g.σ i j) ∧
      ExplainsMoves interpretation r (compSemOf interpretation r) who ok g'
        (ms₀ ++ ms_opk ++ [.aliceStart r.alice r.bob 4 6 bh 35])
        (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) := by
  intro ms₀
  have hex₀ := explains_sanitizeMoves hex
  obtain ⟨ms_opk, bh, g', hms, haddr, hσ, hm''⟩ :=
    ini_matchedPrefix_initOk interpretation hext r hwf who g ms acc bundle ds hex.1 hwho hhon hok
  have hout₁ : OutcomeFaithful r ok (ms₀ ++ ms_opk) := by
    rcases hms with rfl | ⟨t, rfl, hk⟩
    · simpa using hex₀.2
    · exact (explains_attackerSend hex₀ hk).2
  have hvis₁ : runVis r (ms₀ ++ ms_opk) = runVis r ms₀ := by
    rcases hms with rfl | ⟨t, rfl, _⟩
    · simp
    · rw [runVis_snoc, vis_attackerSend_nil, List.append_nil]
  have hok_call' : ok (callCount (runVis r ms₀)) = true := by
    rwa [callCount_eq_callStarts_length hex₀.1.2.2.2.2.2]
  have hout'' : OutcomeFaithful r ok (ms₀ ++ ms_opk ++ [.aliceStart r.alice r.bob 4 6 bh 35]) := by
    refine outcomeFaithful_append hout₁ fun j _ hj => ?_
    rcases j with _ | j
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [List.take_zero, List.append_nil, hvis₁]
      exact ⟨(fun _ h => nomatch h), fun _ => hok_call'⟩
    · simp at hj
  exact ⟨ms_opk, bh, g', hms, haddr, hσ, hm'', hout''⟩

/-! ## `XplBlock` faithfulness and pinning lemmas for `session_initiate` -/

private theorem ini_invisible_visActors :
    ∀ (δ : List Move) (tr : ExecTrace),
      MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = [] ∧ visActorsFrom δ tr = []
  | [], _, _ => ⟨rfl, rfl⟩
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    obtain ⟨h1, h2⟩ := ini_invisible_visActors δ (m.next tr) hδ
    exact ⟨by simp only [runMoves, hv, h1, List.nil_append],
      by simp only [visActorsFrom, hv, h2, List.length_nil, List.replicate_zero, List.nil_append]⟩

private theorem ini_getElem?_append_middle_mp5df {α : Type} (l₁ l₂ l₃ : List α) (x : α) :
    (l₁ ++ (l₂ ++ x :: l₃))[l₁.length + l₂.length]? = some x := by
  rw [← List.append_assoc, ← List.length_append, List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem ini_take_append_middle_mp5df {α : Type} (l₁ l₂ l₃ : List α) (x : α) :
    (l₁ ++ (l₂ ++ x :: l₃)).take (l₁.length + l₂.length) = l₁ ++ l₂ := by
  rw [← List.append_assoc, ← List.length_append, List.take_left]

theorem ini_deltaFaithful_of_matchedPrefix {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₀ δ : List Move}
    {acc : List MachineEvent} {bundle : HwBytes} {ds : List HwBytes}
    (hB : XplBlock interpretation r S who g ms₀ δ acc (.recv bundle :: ds.map MachineEvent.rng))
    (hmp : MatchedPrefix interpretation r S who g (ms₀ ++ δ)
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)))
    (hwho : who[(callStarts acc).length]? = some r.alice) :
    DeltaFaithful r.alice (runTraceMoves r ms₀) δ := by
  let blk := MachineEvent.recv bundle :: ds.map MachineEvent.rng
  have hne : blk ≠ [] := List.cons_ne_nil _ _
  have hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [blk, List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have htail : ∀ e ∈ blk.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    simp only [blk, List.tail_cons, List.mem_map] at he
    obtain ⟨d, _, rfl⟩ := he; simp [eventKind]
  obtain ⟨pre, m, post, rfl, hpre, ⟨_, _, hm⟩, hpost⟩ := xpl_oneMove hB hhead hne htail
  obtain ⟨hpreV, hpreA⟩ := ini_invisible_visActors pre (runTraceMoves r ms₀) hpre
  obtain ⟨_, hpostA⟩ := ini_invisible_visActors post _ hpost
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hm (e := .recv bundle) rfl
  have hrk := xpl_recvHeadKind m _ hv hvk
  have hact_eq : moveActor m = m.party? := by
    cases m <;> first | rfl | exact False.elim hrk
  have hagree : ActorAgrees (moveActor m) (some r.alice) := by
    rw [hact_eq]
    rcases hp : m.party? with _ | q
    · exact Or.inl rfl
    · refine Or.inr (Or.inr ?_)
      have hrf' := hmp.2.2.1 (ms₀.length + pre.length) m q
        (ini_getElem?_append_middle_mp5df ms₀ pre post m) hp
      have hvis_pre : runVis r (ms₀ ++ pre) = runVis r ms₀ := by
        rw [runVis_append, hpreV, List.append_nil]
      rw [ini_take_append_middle_mp5df ms₀ pre post m, hvis_pre,
        callCount_eq_callStarts_length hB.pre.2.2.2.2.2, hwho] at hrf'
      exact hrf'.symm
  intro a ha
  rw [visActorsFrom_append, hpreA, List.nil_append] at ha
  simp only [visActorsFrom, hpostA, List.append_nil] at ha
  rw [List.eq_of_mem_replicate ha]
  exact hagree

theorem ini_deltaFaithful_of_explains {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms₀ δ : List Move}
    {acc : List MachineEvent} {bundle : HwBytes} {ds : List HwBytes}
    (hB : XplBlock interpretation r S who g ms₀ δ acc (.recv bundle :: ds.map MachineEvent.rng))
    (hex : ExplainsMoves interpretation r S who ok g (ms₀ ++ δ)
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)))
    (hwho : who[(callStarts acc).length]? = some r.alice) :
    DeltaFaithful r.alice (runTraceMoves r ms₀) δ :=
  ini_deltaFaithful_of_matchedPrefix hB hex.1 hwho

end Symbolic.Swarm.CREF.CliPure.IniPure
