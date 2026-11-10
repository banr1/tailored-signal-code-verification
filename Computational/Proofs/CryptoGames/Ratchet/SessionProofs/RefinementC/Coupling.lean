/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Coupling combinators for the C side

Combinators for `CloseByRefinesH` and `CloseByStateC`, structural lemmas for the eager C run and
evicted stops, and monotonicity of the probe flag.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-! ## `CloseByRefinesH` -/

/-- `cWin` with `cHid` as slot `n`. -/
def cWinH (n : ℕ) (cWin : ℕ → ProbComp Bool) (cHid : ProbComp Bool) (k : ℕ) : ProbComp Bool :=
  if k = n then cHid else cWin k

theorem sum_range_cWinH (n : ℕ) (cWin : ℕ → ProbComp Bool) (cHid : ProbComp Bool) :
    (∑ k ∈ Finset.range (n + 1), 𝒟[cWinH n cWin cHid k] {true}) =
      (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + 𝒟[cHid] {true} := by
  rw [Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have : k ≠ n := (Finset.mem_range.mp hk).ne
    simp [cWinH, this]
  · simp [cWinH]

/-- `CloseByRefinesH n` is `CloseByRefines (n + 1)` with `cHid` as the last `cWin` slot. -/
theorem closeByRefinesH_iff {n : ℕ} {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 cHid : ProbComp Bool} :
    CloseByRefinesH n d cR cS cWin cEps0 cHid ↔
      CloseByRefines (n + 1) d cR cS (cWinH n cWin cHid) cEps0 := by
  unfold CloseByRefinesH CloseByRefines
  rw [sum_range_cWinH]
  have e : ∀ a b c d' e' : ℝ≥0∞, a + b + c + d' + e' = a + (b + e') + c + d' := by
    intro a b c d' e'; ring
  simp only [e]

theorem boolDist_le_of_closeByRefinesH {n : ℕ} {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 cHid : ProbComp Bool}
    (h : CloseByRefinesH n d cR cS cWin cEps0 cHid) :
    (𝒟[cR]).boolDist (𝒟[cS]) ≤
      (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + 𝒟[cHid] {true} + d + 𝒟[cEps0] {true} := by
  have h' := boolDist_le_of_closeByRefines (closeByRefinesH_iff.mp h)
  rwa [sum_range_cWinH] at h'

theorem closeByRefinesH_of_eq (n : ℕ) {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 cHid : ProbComp Bool}
    (h : cR = cS) :
    CloseByRefinesH n d cR cS cWin cEps0 cHid :=
  closeByRefinesH_iff.mpr (closeByRefines_of_eq (n + 1) h)

theorem closeByRefinesH_mono_d {n : ℕ} {d₁ d₂ : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 cHid : ProbComp Bool}
    (hd : d₁ ≤ d₂) (h : CloseByRefinesH n d₁ cR cS cWin cEps0 cHid) :
    CloseByRefinesH n d₂ cR cS cWin cEps0 cHid :=
  closeByRefinesH_iff.mpr (closeByRefines_mono_d hd (closeByRefinesH_iff.mp h))

theorem closeByRefinesH_of_win_eq_one {n : ℕ} {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 cHid : ProbComp Bool}
    {k₀ : ℕ} (hk₀ : k₀ ∈ Finset.range n) (hone : 𝒟[cWin k₀] {true} = 1) :
    CloseByRefinesH n d cR cS cWin cEps0 cHid := by
  refine closeByRefinesH_iff.mpr (closeByRefines_of_win_eq_one (k₀ := k₀) ?_ ?_)
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hk₀))
  · have : k₀ ≠ n := (Finset.mem_range.mp hk₀).ne
    simpa [cWinH, this] using hone

theorem closeByRefinesH_of_eps0_eq_one {n : ℕ} {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 cHid : ProbComp Bool}
    (hone : 𝒟[cEps0] {true} = 1) :
    CloseByRefinesH n d cR cS cWin cEps0 cHid :=
  closeByRefinesH_iff.mpr (closeByRefines_of_eps0_eq_one hone)

theorem closeByRefinesH_of_hid_eq_one {n : ℕ} {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 cHid : ProbComp Bool}
    (hone : 𝒟[cHid] {true} = 1) :
    CloseByRefinesH n d cR cS cWin cEps0 cHid := by
  refine closeByRefinesH_iff.mpr (closeByRefines_of_win_eq_one (k₀ := n) (by simp) ?_)
  simpa [cWinH] using hone

theorem closeByRefinesH_congr_all {n : ℕ} {d : ℝ≥0∞}
    {cR₁ cR₂ cS₁ cS₂ : ProbComp Bool} {cWin₁ cWin₂ : ℕ → ProbComp Bool}
    {cEps0₁ cEps0₂ cHid₁ cHid₂ : ProbComp Bool}
    (hR : 𝒟[cR₁] = 𝒟[cR₂]) (hS : 𝒟[cS₁] = 𝒟[cS₂])
    (hWin : ∀ idx ∈ Finset.range n, 𝒟[cWin₁ idx] = 𝒟[cWin₂ idx])
    (hEps0 : 𝒟[cEps0₁] = 𝒟[cEps0₂]) (hHid : 𝒟[cHid₁] = 𝒟[cHid₂])
    (h : CloseByRefinesH n d cR₂ cS₂ cWin₂ cEps0₂ cHid₂) :
    CloseByRefinesH n d cR₁ cS₁ cWin₁ cEps0₁ cHid₁ := by
  have hsum : (∑ idx ∈ Finset.range n, 𝒟[cWin₁ idx] {true}) =
      ∑ idx ∈ Finset.range n, 𝒟[cWin₂ idx] {true} :=
    Finset.sum_congr rfl fun idx hidx => by rw [hWin idx hidx]
  unfold CloseByRefinesH at h ⊢
  rw [hR, hS, hsum, hEps0, hHid]
  exact h

theorem closeByRefinesH_bind {α : Type} (n : ℕ) (d : ℝ≥0∞) (oa : ProbComp α)
    {fR fS : α → ProbComp Bool} {fWin : ℕ → α → ProbComp Bool} {fEps0 fHid : α → ProbComp Bool}
    (h : ∀ a, CloseByRefinesH n d (fR a) (fS a) (fun k => fWin k a) (fEps0 a) (fHid a)) :
    CloseByRefinesH n d (oa >>= fR) (oa >>= fS) (fun k => oa >>= fWin k) (oa >>= fEps0)
      (oa >>= fHid) := by
  refine closeByRefinesH_iff.mpr ?_
  have hb := closeByRefines_bind (n + 1) d oa
    (fWin := fun k a => cWinH n (fun k => fWin k a) (fHid a) k)
    (fun a => closeByRefinesH_iff.mp (h a))
  refine closeByRefines_congr_cWin (fun idx _ => ?_) hb
  by_cases hk : idx = n <;> simp [cWinH, hk]

theorem closeByRefinesH_bind_of_bad {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (n : ℕ) {d₁ d₂ : ℝ≥0∞} (oa : ProbComp α) (bad : α → Bool)
    (hbad : 𝒟[oa] {a | bad a = true} ≤ d₁)
    {fR fS : α → ProbComp Bool} {fWin : ℕ → α → ProbComp Bool} {fEps0 fHid : α → ProbComp Bool}
    (h : ∀ a, bad a = false →
      CloseByRefinesH n d₂ (fR a) (fS a) (fun k => fWin k a) (fEps0 a) (fHid a)) :
    CloseByRefinesH n (d₁ + d₂) (oa >>= fR) (oa >>= fS) (fun k => oa >>= fWin k) (oa >>= fEps0)
      (oa >>= fHid) := by
  refine closeByRefinesH_iff.mpr ?_
  have hb := closeByRefines_bind_of_bad (n + 1) oa bad hbad
    (fWin := fun k a => cWinH n (fun k => fWin k a) (fHid a) k)
    (fun a ha => closeByRefinesH_iff.mp (h a ha))
  refine closeByRefines_congr_cWin (fun idx _ => ?_) hb
  by_cases hk : idx = n <;> simp [cWinH, hk]

/-! ## Structural lemmas for the eager C run -/

theorem runSimCEager_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (a : α) (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    runSimCEager P ℓ Dh encPt encT decT idOf lam qep k (pure a) x ec = pure (a, (x, ec)) := by
  simp [runSimCEager]

theorem runSimCEager_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    runSimCEager P ℓ Dh encPt encT decT idOf lam qep k
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont) x ec =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep k (cont y) x ec := by
  simp only [runSimCEager, simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
    id_eq, StateT.run_bind]
  have h1 :
      (liftM ((QueryImpl.liftTarget
        (StateT (JointC PQ Pt ℓ × (Party → BitVec 256)) ProbComp)
        (QueryImpl.ofLift unifSpec ProbComp) +
        simEagerImplC P ℓ Dh encPt encT decT idOf lam qep k) (.inl u)) :
        StateT _ ProbComp (unifSpec.Range u)).run (x, ec) =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y => pure (y, (x, ec))) := rfl
  rw [h1]
  simp only [bind_assoc, pure_bind]

theorem runSimCEager_inr_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    runSimCEager P ℓ Dh encPt encT decT idOf lam qep k
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q)) >>= cont) x ec =
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q x ec >>= fun r =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1 r.2.2 := by
  simp only [runSimCEager, simEagerImplC, simulateQ_query_bind, OracleQuery.input_query,
    OracleQuery.cont_query, id_eq, StateT.run_bind]
  rfl

theorem simRecvStops_some_eq_none_of_not_div (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep idx : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hidx : idx ≠ st.1.amb) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some idx) Q w isDel st =
      simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w isDel st := by
  unfold simRecvStops
  rw [simRecvStep_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx Q w isDel 0 st hidx]

theorem stepSimC_some_eq_none_of_not_div (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep idx : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hidx : idx ≠ x.1.base.amb) :
    stepSimC P ℓ Dh encPt encT decT idOf lam qep (some idx) q x =
      stepSimC P ℓ Dh encPt encT decT idOf lam qep none q x := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · rfl
  · simp only [stepSimC]
    rw [simRecvStops_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx Q w true
      x.sim hidx, stepSim_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx _ x.sim hidx]
  · simp only [stepSimC]
    rw [simRecvStops_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx Q w false
      x.sim hidx, stepSim_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx _ x.sim hidx]
  · rfl

theorem evictStopsC_none (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ) :
    evictStopsC P encT decT none Q w isDel x = false := by
  simp [evictStopsC]

theorem evictStopsC_some_of_ne (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idx : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ)
    (hidx : idx ≠ x.1.base.amb) :
    evictStopsC P encT decT (some idx) Q w isDel x = false := by
  simp [evictStopsC, hidx]

theorem evictStopsC_of_not_case (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ)
    (h : evictCaseC P encT decT Q w isDel x.1.base = false) :
    evictStopsC P encT decT k Q w isDel x = false := by
  simp [evictStopsC, h]

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem evictCaseC_of_stopped (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (s : SimState PQ Pt ℓ) (hstop : s.stopped = true) :
    evictCaseC P encT decT Q w isDel s = false := by
  simp [evictCaseC, hstop]

theorem evictStopsC_of_stopped (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ)
    (hstop : x.1.base.stopped = true) :
    evictStopsC P encT decT k Q w isDel x = false :=
  evictStopsC_of_not_case P encT decT k Q w isDel x (evictCaseC_of_stopped P encT decT Q w isDel _ hstop)

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem inWin_of_evictCaseC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (s : SimState PQ Pt ℓ) (h : evictCaseC P encT decT Q w isDel s = true) :
    inReceiveOnlyEpoch s.mir Q = true := by
  unfold evictCaseC at h
  dsimp only at h
  repeat' (split at h)
  all_goals simp_all

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem simRecvUsesCoin_eq_false_of_evictCaseC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : evictCaseC P encT decT Q w isDel st.1 = true) :
    simRecvUsesCoin P encT decT k Q w isDel st = false := by
  unfold evictCaseC at h
  unfold simRecvUsesCoin
  dsimp only at h ⊢
  repeat' (split at h)
  all_goals (try contradiction)
  obtain ⟨hev, -⟩ := (Bool.and_eq_true _ _).mp h
  simp only [*, ↓reduceIte, Bool.false_eq_true]

theorem simRecvUsesCoin_eq_false_of_evictStopsC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (x : JointC PQ Pt ℓ) (h : evictStopsC P encT decT k Q w isDel x = true) :
    simRecvUsesCoin P encT decT k Q w isDel x.sim = false :=
  simRecvUsesCoin_eq_false_of_evictCaseC P encT decT k Q w isDel x.sim
    ((Bool.and_eq_true _ _).mp h).1

theorem inWin_of_evictStopsC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (x : JointC PQ Pt ℓ) (h : evictStopsC P encT decT k Q w isDel x = true) :
    inReceiveOnlyEpoch x.1.base.mir Q = true :=
  inWin_of_evictCaseC P encT decT Q w isDel _ ((Bool.and_eq_true _ _).mp h).1

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem simRecvStepCGen_of_evictCaseC (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ)
    (h : evictCaseC P encT decT Q w isDel x.1.base = true) :
    simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x =
      (some .rejected, ({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1 } }, x.2)) := by
  unfold evictCaseC at h
  unfold simRecvStepCGen
  dsimp only at h ⊢
  repeat' (split at h)
  all_goals (try contradiction)
  obtain ⟨hev, hinw⟩ := (Bool.and_eq_true _ _).mp h
  simp only [hev, Bool.true_and] at *
  simp only [*, ↓reduceIte, Bool.false_eq_true, Bool.true_or]

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem evictCaseC_eq_false_of_res_amb (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ)
    (res : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ)
    (hres : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x = res)
    (hamb : res.2.1.base.amb = x.1.base.amb) :
    evictCaseC P encT decT Q w isDel x.1.base = false := by
  cases h : evictCaseC P encT decT Q w isDel x.1.base
  · rfl
  · rw [simRecvStepCGen_of_evictCaseC P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x h] at hres
    subst hres
    simp at hamb

theorem evictStopsC_of_res_amb (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ)
    (res : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ)
    (hres : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x = res)
    (hamb : res.2.1.base.amb = x.1.base.amb) :
    evictStopsC P encT decT k Q w isDel x = false :=
  evictStopsC_of_not_case P encT decT k Q w isDel x
    (evictCaseC_eq_false_of_res_amb P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x res hres hamb)

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem evictCaseC_of_inWin_false (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (s : SimState PQ Pt ℓ) (h : inReceiveOnlyEpoch s.mir Q = false) :
    evictCaseC P encT decT Q w isDel s = false := by
  cases hc : evictCaseC P encT decT Q w isDel s
  · rfl
  · rw [inWin_of_evictCaseC P encT decT Q w isDel s hc] at h
    exact absurd h (by decide)

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem simRecvStep_of_evictCaseC (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : evictCaseC P encT decT Q w isDel st.1 = true) :
    simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel c_cka st = (some .rejected, st) := by
  unfold evictCaseC at h
  unfold simRecvStep
  dsimp only at h ⊢
  repeat' (split at h)
  all_goals (try contradiction)
  obtain ⟨hev, hinw⟩ := (Bool.and_eq_true _ _).mp h
  simp only [*, ↓reduceIte, Bool.false_eq_true]

theorem evictStopsC_of_simRecvStep_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k k' : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256) (x : JointC PQ Pt ℓ)
    (h : (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel c_cka x.sim).2.1.stopped = true) :
    evictStopsC P encT decT k' Q w isDel x = false := by
  apply evictStopsC_of_not_case
  cases hc : evictCaseC P encT decT Q w isDel x.1.base
  · rfl
  · rw [simRecvStep_of_evictCaseC P ℓ Dh encPt encT decT idOf lam qep k Q w isDel c_cka x.sim hc] at h
    have h' := evictCaseC_of_stopped P encT decT Q w isDel x.1.base h
    rw [hc] at h'
    exact absurd h' (by decide)

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem evictCaseC_of_honestC_next (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (s : SimState PQ Pt ℓ) (c : Fig8C Pt)
    (hhonC : (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hep : c.1.1 = s.mir.epoch Q + 1) :
    evictCaseC P encT decT Q w isDel s = false := by
  cases hc : evictCaseC P encT decT Q w isDel s
  · rfl
  · exfalso
    unfold evictCaseC at hc
    dsimp only at hc
    repeat' (split at hc)
    all_goals (try contradiction)
    obtain ⟨hev, -⟩ := (Bool.and_eq_true _ _).mp hc
    rw [hhonC] at hev
    simp [hep] at hev

/-- Discharges `evictStopsC … = false` obligations from context or structural `evictCaseC` facts. -/
macro "evict_stops_tac" : tactic => `(tactic| first
  | exact evictStopsC_none _ _ _ _ _ _ _
  | assumption
  | exact evictStopsC_of_not_case _ _ _ _ _ _ _ _ (by assumption)
  | exact evictStopsC_of_res_amb (k := _) (hres := by assumption) (hamb := by rfl)
  | exact evictStopsC_of_not_case _ _ _ _ _ _ _ _
      (evictCaseC_of_honestC_next _ _ _ _ _ _ _ _ (by assumption) (by assumption))
  | exact evictStopsC_of_not_case _ _ _ _ _ _ _ _
      (evictCaseC_of_findIdx_some _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption))
  | exact evictStopsC_of_not_case _ _ _ _ _ _ _ _
      (evictCaseC_of_inWin_false _ _ _ _ _ _ _ (by assumption)))

theorem stepSimCEager_some_eq_none_of_not_div (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep idx : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (hidx : idx ≠ x.1.base.amb) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q x ec =
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q x ec := by
  have hC := stepSimC_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx q x hidx
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep (some idx) Q m₀ r x ec =
      stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep none Q m₀ r x ec
    unfold stepSimCEagerTransmit
    rw [show stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep (some idx) Q m₀ r x.sim ec =
        stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep none Q m₀ r x.sim ec from
      stepSimEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx
        (.inl (.inl (.inl (.inl (Q, m₀, r))))) x.sim ec hidx]
  · change stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep (some idx) Q m₀ m₁ r x ec =
      stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep none Q m₀ m₁ r x ec
    unfold stepSimCEagerChall
    rw [show stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep (some idx) Q m₀ m₁ r x.sim ec =
        stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep none Q m₀ m₁ r x.sim ec from
      stepSimEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx
        (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) x.sim ec hidx]
  · change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep (some idx) Q w x ec =
      stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep none Q w x ec
    unfold stepSimCEagerDeliver
    rw [simRecvUsesCoin_some_eq_none_of_not_div P encT decT idx Q w true x.sim hidx,
      simRecvStep_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx Q w true (ec Q)
        x.sim hidx, hC, evictStopsC_some_of_ne P encT decT idx Q w true x hidx,
      evictStopsC_none]
  · change stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep (some idx) Q w x ec =
      stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep none Q w x ec
    unfold stepSimCEagerInject
    rw [simRecvUsesCoin_some_eq_none_of_not_div P encT decT idx Q w false x.sim hidx,
      simRecvStep_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx Q w false (ec Q)
        x.sim hidx, hC, evictStopsC_some_of_ne P encT decT idx Q w false x hidx,
      evictStopsC_none]
  · change stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep (some idx) Q x ec =
      stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep none Q x ec
    unfold stepSimCEagerCorr
    rw [hC]

theorem evalDist_runWinAtC_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAtC P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont)
        x ec winBefore idx] =
      𝒟[(liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        runWinAtC P ℓ Dh encPt encT decT idOf lam qep (cont y) x ec winBefore idx] := by
  unfold runWinAtC
  cases idx with
  | zero =>
    simp only [runSimCEager_inl_bind, bind_assoc]
  | succ j =>
    dsimp only
    split
    · exact (OracleComp.evalDist_bind_const _ _).symm
    · simp only [runSimCEager_inl_bind, bind_assoc]

theorem runHidC_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    runHidC P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont)
        x ec =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        runHidC P ℓ Dh encPt encT decT idOf lam qep (cont y) x ec := by
  unfold runHidC
  simp only [runSimCEager_inl_bind, bind_assoc]

theorem evalDist_runWinAtC_inr_same_amb_bind {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q ×
      (JointC PQ Pt ℓ × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.base.amb = x.1.base.amb)
    (hstep : ∀ idx, ¬ idx < x.1.base.amb →
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q x ec =
        N >>= fun y => pure (f y))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAtC P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q)) >>= cont)
        x ec winBefore idx] =
      𝒟[N >>= fun y =>
        runWinAtC P ℓ Dh encPt encT decT idOf lam qep (cont (f y).1) (f y).2.1 (f y).2.2
          winBefore idx] := by
  unfold runWinAtC
  cases idx with
  | zero =>
    have hstep_none : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q x ec =
        N >>= fun y => pure (f y) := by
      rw [← stepSimCEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep
            (x.1.base.amb + 1) q x ec (by omega)]
      exact hstep (x.1.base.amb + 1) (by omega)
    rw [runSimCEager_inr_bind, hstep_none]
    simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only
    simp only [hamb]
    split
    · exact (OracleComp.evalDist_bind_const _ _).symm
    · rename_i hnot
      rw [runSimCEager_inr_bind, hstep j hnot]
      simp only [bind_assoc, pure_bind]

/-! ## `CloseByStateC` combinators -/

theorem closeByStateC_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (a : α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hwin_R : s_R.win = false) (hwin_fig8 : s_fig8.win = false) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (pure a) s_R sC s_fig8 fl ec
      winBefore := by
  unfold CloseByStateC
  rw [runRCont_pure, runSimCEager_pure]
  simp only [pure_bind, hwin_R, hwin_fig8]
  exact closeByRefinesH_of_eq (q + 1) rfl

theorem closeByStateC_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (h : ∀ y, CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont y) s_R sC s_fig8 fl
      ec winBefore) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir))
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) h)
  · simp only [runRCont_inl_bind, bind_assoc]
  · simp only [runSimCEager_inl_bind, bind_assoc]
  · intro idx _
    exact evalDist_runWinAtC_inl_bind P ℓ Dh encPt encT decT idOf lam qep u cont (sC, s_fig8, fl)
      ec winBefore idx
  · simp only [runRCont_inl_bind, bind_assoc]
  · rw [runHidC_inl_bind]

/-- Coupling rule for an oracle step that preserves `amb` and matches answers across runs. -/
theorem closeByStateC_inr_same_amb_bind {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ)
    (fR : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (fS : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      (JointC PQ Pt ℓ × (Party → BitVec 256)))
    (hans : ∀ y, (fR y).1 = (fS y).1)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      N >>= fun y => pure (fR y))
    (hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) ec =
      N >>= fun y => pure (fS y))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (sC, s_fig8, fl) ec =
        N >>= fun y => pure (fS y))
    (hamb : ∀ y, (fS y).2.1.1.base.amb = sC.base.amb)
    (hrem : ∀ y, remWin qep (fS y).2.1.1.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ y, CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont (fS y).1) (fR y).2 (fS y).2.1.1 (fS y).2.1.2.1 (fS y).2.1.2.2 (fS y).2.2 winBefore) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir)) N
      (fun y => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem y)) (hcont y)))
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimCEager_inr_bind, hstepSim, bind_assoc, pure_bind]
  · intro idx _
    exact evalDist_runWinAtC_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (sC, s_fig8, fl) ec N fS hamb hstepWin winBefore idx
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runHidC, runSimCEager_inr_bind, hstepSim, bind_assoc, pure_bind]

theorem closeByStateC_inr_same_amb_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl fl' : Bool)
    (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      pure (ans, s_R'))
    (hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) ec =
      pure (ans, ((sC', s_fig8', fl'), ec')))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (sC, s_fig8, fl) ec =
        pure (ans, ((sC', s_fig8', fl'), ec')))
    (hamb : sC'.base.amb = sC.base.amb)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC'
      s_fig8' fl' ec' winBefore) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore :=
  closeByStateC_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep q δ post q_sm cont s_R sC
    s_fig8 fl ec winBefore (pure ()) (fun _ => (ans, s_R')) (fun _ => (ans, ((sC', s_fig8', fl'), ec')))
    (fun _ => rfl) hD0 (by rw [hstepR]; simp) (by rw [hstepSim]; simp)
    (fun idx h => by rw [hstepWin idx h]; simp) (fun _ => hamb) (fun _ => hrem) (fun _ => hcont)

/-! ## Probe flag -/

private def cfl_preserves {α : Type}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    gh.2 = true →
    ∀ r ∈ support ((m.run sC).run gh), r.2.2 = true

private theorem cfl_preserves_pure {α : Type} (a : α) :
    cfl_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (pure a) := by
  intro sC gh hgh r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem cfl_preserves_bind {α β : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : cfl_preserves m) (hk : ∀ a, cfl_preserves (k a)) :
    cfl_preserves (m >>= k) := by
  intro sC gh hgh r hr
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  exact hk r₁.1.1 r₁.1.2 r₁.2 (hm sC gh hgh r₁ hr₁) r hr

private theorem cfl_preserves_get :
    cfl_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) get := by
  intro sC gh hgh r hr
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem cfl_preserves_set (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    cfl_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (set sC') := by
  intro sC gh hgh r hr
  simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem cfl_preserves_modify (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    cfl_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (modify f) := by
  intro sC gh hgh r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem cfl_probeHook_lift_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (y : Fig8Comp Pt ℓ α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift y).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) y).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) := rfl

private theorem cfl_preserves_ite {α : Type} {P_cond : Prop} [Decidable P_cond]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : cfl_preserves t) (he : cfl_preserves e) :
    cfl_preserves (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem cfl_preserves_zoomB {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    cfl_preserves (PQ := PQ) (runOnBaseState (probeHook fig qepF) x) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).lift (x.run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, cfl_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨_, _, rfl⟩
  exact hgh

private theorem cfl_preserves_liftC {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    cfl_preserves (PQ := PQ) (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).lift x >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, cfl_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨_, _, rfl⟩
  exact hgh

private theorem cfl_probeHook_probe_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh =
      pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

private theorem cfl_preserves_probe
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    cfl_preserves (PQ := PQ)
      (StateT.lift ((probeHook fig qepF).probe Q c') :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) Unit) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).probe Q c' >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, cfl_probeHook_probe_run] at hr
  simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  simp [hgh]

private theorem cfl_preserves_guardC {α : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : cfl_preserves m) :
    cfl_preserves (guardC m) := by
  unfold guardC
  refine cfl_preserves_bind cfl_preserves_get fun sC => ?_
  exact cfl_preserves_ite (cfl_preserves_pure none) hm

private theorem cfl_preserves_simSendC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    cfl_preserves (simSendC P qep fig (probeHook fig qepF) Q m₀ chal r) := by
  unfold simSendC
  refine cfl_preserves_bind (cfl_preserves_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact cfl_preserves_pure none
  | some w =>
    refine cfl_preserves_bind cfl_preserves_get fun sC => ?_
    exact cfl_preserves_bind (cfl_preserves_set _) fun _ => cfl_preserves_pure (some w)

private theorem cfl_preserves_fwdAnswerC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    cfl_preserves (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine cfl_preserves_bind (cfl_preserves_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact cfl_preserves_zoomB (PQ := PQ) fig qepF _
  | some r =>
    cases r <;>
      first
      | exact cfl_preserves_zoomB (PQ := PQ) fig qepF _
      | exact cfl_preserves_bind (cfl_preserves_modify _) fun _ =>
          cfl_preserves_zoomB (PQ := PQ) fig qepF _

private theorem cfl_preserves_resyncC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    cfl_preserves (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact cfl_preserves_pure _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine cfl_preserves_bind (cfl_preserves_liftC fig qepF _) fun res => ?_
    cases res with
    | none => exact cfl_preserves_pure _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        exact cfl_preserves_bind (cfl_preserves_modify _) fun _ =>
          cfl_preserves_zoomB (PQ := PQ) fig qepF _
      | _ => exact cfl_preserves_pure _

private theorem cfl_preserves_fwdC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    cfl_preserves (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine cfl_preserves_bind cfl_preserves_get fun sC => ?_
  cases honestC with
  | none => exact cfl_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c'
  | some c =>
    refine cfl_preserves_ite ?_ (cfl_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots fig fs P sC Q w c c' with
    | some r => exact cfl_preserves_resyncC qep fig fs qepF Q w ci? T pq' c r
    | none =>
      exact cfl_preserves_bind (cfl_preserves_probe fig qepF Q c') fun _ =>
        cfl_preserves_pure _

private theorem cfl_preserves_fwdEvictC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    cfl_preserves (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine cfl_preserves_bind cfl_preserves_get fun sC => ?_
  refine cfl_preserves_ite ?_ (cfl_preserves_fwdAnswerC qep fig fs qepF Q w isDel none T pq' c')
  exact cfl_preserves_bind (cfl_preserves_probe fig qepF Q c') fun _ => cfl_preserves_pure _

private theorem cfl_preserves_simRecvC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    cfl_preserves (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine cfl_preserves_bind cfl_preserves_get fun sC => ?_
  dsimp only
  refine cfl_preserves_ite (cfl_preserves_pure _) ?_
  refine cfl_preserves_ite (cfl_preserves_pure _) ?_
  refine cfl_preserves_ite (cfl_preserves_pure _) ?_
  refine cfl_preserves_ite (cfl_preserves_pure _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact cfl_preserves_pure _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine cfl_preserves_ite (cfl_preserves_pure _) ?_
    refine cfl_preserves_ite (cfl_preserves_pure _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact cfl_preserves_pure _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine cfl_preserves_ite (cfl_preserves_pure _) ?_
        exact cfl_preserves_fwdC P qep fig fs qepF Q w isDel (some ci) h.senderRatchetKey pq' _ _
      | none =>
        dsimp only
        refine cfl_preserves_ite (cfl_preserves_pure _) ?_
        refine cfl_preserves_ite (cfl_preserves_pure _) ?_
        refine cfl_preserves_ite
          (cfl_preserves_bind (cfl_preserves_modify _) fun _ => ?_) ?_ <;>
        · refine cfl_preserves_ite (cfl_preserves_pure _) ?_
          cases decT h.senderRatchetKey with
          | none => exact cfl_preserves_pure _
          | some T =>
            exact cfl_preserves_ite
              (cfl_preserves_fwdEvictC qep fig fs qepF Q w isDel h.senderRatchetKey pq' _)
              (cfl_preserves_fwdC P qep fig fs qepF Q w isDel none h.senderRatchetKey pq' _ _)

private theorem cfl_preserves_simCorrC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    cfl_preserves (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC
  refine cfl_preserves_bind cfl_preserves_get fun sC => ?_
  refine cfl_preserves_ite (cfl_preserves_pure _) ?_
  refine cfl_preserves_bind (cfl_preserves_liftC fig qepF _) fun res => ?_
  cases res with
  | none => exact cfl_preserves_pure _
  | some st =>
    exact cfl_preserves_bind (cfl_preserves_set _) fun _ => cfl_preserves_pure _

private theorem cfl_stepSimCNone_preserve_fl (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hfl : x.2.2 = true) :
    ∀ z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x), z.2.2.2 = true := by
  intro z hz
  unfold stepSimCNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨r, hr, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hpres : cfl_preserves
      (simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh (.inr q)) := by
    rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
    · exact cfl_preserves_guardC (cfl_preserves_simSendC P qep _ (qep + 1) Q m₀ none r')
    · exact cfl_preserves_guardC (cfl_preserves_simSendC P qep _ (qep + 1) Q m₀ (some m₁) r')
    · exact cfl_preserves_guardC (cfl_preserves_simRecvC P encT decT qep _ _ (qep + 1) Q w true)
    · exact cfl_preserves_guardC (cfl_preserves_simRecvC P encT decT qep _ _ (qep + 1) Q w false)
    · exact cfl_preserves_guardC (cfl_preserves_simCorrC P encT _ (qep + 1) Dh Q)
  exact hpres x.1 x.2 hfl r hr

private theorem cfl_stepSimC_preserve_fl (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hfl : x.2.2 = true) :
    ∀ z ∈ support (stepSimC P ℓ Dh encPt encT decT idOf lam qep k q x), z.2.2.2 = true := by
  rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact cfl_stepSimCNone_preserve_fl P ℓ Dh encPt encT decT idOf lam qep _ x hfl
  · exact cfl_stepSimCNone_preserve_fl P ℓ Dh encPt encT decT idOf lam qep _ x hfl
  · intro z hz
    simp only [stepSimC] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨r, _, rfl⟩
      exact hfl
    · exact cfl_stepSimCNone_preserve_fl P ℓ Dh encPt encT decT idOf lam qep _ x hfl z hz
  · intro z hz
    simp only [stepSimC] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨r, _, rfl⟩
      exact hfl
    · exact cfl_stepSimCNone_preserve_fl P ℓ Dh encPt encT decT idOf lam qep _ x hfl z hz
  · exact cfl_stepSimCNone_preserve_fl P ℓ Dh encPt encT decT idOf lam qep _ x hfl

/-- Once set, the probe flag remains `true` across `stepSimCEager`. -/
theorem stepSimCEager_preserve_fl (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (hfl : x.2.2 = true) :
    ∀ z ∈ support (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q x ec), z.2.1.2.2 = true := by
  intro z hz
  rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · simp only [stepSimCEager, stepSimCEagerTransmit, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hfl
  · simp only [stepSimCEager, stepSimCEagerChall, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hfl
  · simp only [stepSimCEager, stepSimCEagerDeliver] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨_, _, rfl⟩
      exact hfl
    · split at hz
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨_, _, rfl⟩
        simpa [evictStopStepC] using hfl
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨res, hres, _, _, rfl⟩
        exact cfl_stepSimC_preserve_fl P ℓ Dh encPt encT decT idOf lam qep k _ x hfl res hres
  · simp only [stepSimCEager, stepSimCEagerInject] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨_, _, rfl⟩
      exact hfl
    · split at hz
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨_, _, rfl⟩
        simpa [evictStopStepC] using hfl
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨res, hres, _, _, rfl⟩
        exact cfl_stepSimC_preserve_fl P ℓ Dh encPt encT decT idOf lam qep k _ x hfl res hres
  · simp only [stepSimCEager, stepSimCEagerCorr, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, _, _, rfl⟩
    exact cfl_stepSimC_preserve_fl P ℓ Dh encPt encT decT idOf lam qep k _ x hfl res hres

theorem evalDist_runHidC_of_fl_true {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (hfl : x.2.2 = true) :
    𝒟[runHidC P ℓ Dh encPt encT decT idOf lam qep oa x ec] {true} = 1 := by
  unfold runHidC runSimCEager
  refine Construction.AuthL11.evalDist_bind_eq_one _ _ fun z hz => ?_
  have h := simulateQ_run_preserve (simEagerImplC P ℓ Dh encPt encT decT idOf lam qep none)
    (fun s => s.1.2.2 = true)
    (fun q s hs z hz => stepSimCEager_preserve_fl P ℓ Dh encPt encT decT idOf lam qep none q s.1
      s.2 hs z hz) oa (x, ec) hfl z hz
  simp [h]

/-- A joint state with the probe flag set closes immediately via `cHid`. -/
theorem closeByStateC_of_fl_true {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post oa s_R sC s_fig8 true ec
      winBefore :=
  closeByRefinesH_of_hid_eq_one
    (evalDist_runHidC_of_fl_true P ℓ Dh encPt encT decT idOf lam qep oa _ ec rfl)

theorem closeByStateC_inr_of_fl_step {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hset : ∀ z ∈ support (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm
      (sC, s_fig8, fl) ec), z.2.1.2.2 = true) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  refine closeByRefinesH_of_hid_eq_one ?_
  unfold runHidC
  rw [runSimCEager_inr_bind, bind_assoc]
  refine Construction.AuthL11.evalDist_bind_eq_one _ _ fun z hz => ?_
  have h := evalDist_runHidC_of_fl_true P ℓ Dh encPt encT decT idOf lam qep (cont z.1) z.2.1 z.2.2
    (hset z hz)
  simpa [runHidC] using h

end CryptoGames.LibsignalSM.Proofs.Refinement
