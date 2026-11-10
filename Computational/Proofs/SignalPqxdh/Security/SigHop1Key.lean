/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.SigHop1KeyA
public import Computational.Proofs.SignalPqxdh.Security.SigHop
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhIkCoupling
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-Key `KeyInd` Bad-Signature Hop (`G0_1 -> G1` and `G0 -> G2`)

**Checked by Lean.** Bounds the advantage change from adding the `hasBadSigKeyInd` abort to the
one-key random-oracle handshake game (`keyInd1KeyExpG0_1 → keyInd1KeyExpG1`) by
`S.N_id * GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A)`, and combines it with
the birthday collision bound to obtain `keyInd1Key_hop_G0_G1_le` and `keyInd1Key_hop_G0_G2_le`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp ENNReal MeasureTheory BigOperators
open SignalPqxdh.Security.RoKem
open SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.Sig1Key
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik

/-! ## Support-restricted continuations and preservation bridges -/

private noncomputable def withSupp {α : Type} (m : ProbComp α) (k : α → ProbComp Bool) (x : α) :
    ProbComp Bool :=
  @ite _ (x ∈ support m) (Classical.propDecidable _) (k x) (pure false)

private theorem evalDist_bind_withSupp_eq {α : Type} (m : ProbComp α) (k : α → ProbComp Bool) :
    𝒟[m >>= k] = 𝒟[m >>= withSupp m k] := by
  refine OracleComp.evalDist_bind_congr_of_support m k (withSupp m k) (fun x hx => ?_)
  unfold withSupp
  simp [hx]

private theorem pqxdhKeyIndImpl_initiateOPK_pres_raw (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bnd : PreKeyBundleInput) (st : KeyIndState S) :
    ∀ x ∈ support ((pqxdhKeyIndImpl true S P (.initiateOPK u i bnd)).run st),
      InitPostKeyInd P bnd st x.2 :=
  pqxdhKeyIndImpl_initiateOPK_pres true S P u i bnd st

private theorem pqxdhKeyIndImpl_initiateNoOPK_pres_raw (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bnd : PreKeyBundleInput) (st : KeyIndState S) :
    ∀ x ∈ support ((pqxdhKeyIndImpl true S P (.initiateNoOPK u i bnd)).run st),
      InitPostKeyInd P bnd st x.2 :=
  pqxdhKeyIndImpl_initiateNoOPK_pres true S P u i bnd st

private theorem pqxdhKeyIndImpl_other_pres_raw (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S)
    (h_not_init : ∀ u, q ≠ .initPrin u)
    (h_not_corr : ∀ u, q ≠ .corruptIK u)
    (h_not_spk : ∀ u j, q ≠ .genSPK u j)
    (h_not_iopk : ∀ u i b, q ≠ .initiateOPK u i b)
    (h_not_inoopk : ∀ u i b, q ≠ .initiateNoOPK u i b) :
    ∀ x ∈ support ((pqxdhKeyIndImpl true S P q).run st),
      x.2.principals = st.principals ∧ SpksPreserved S st.spkBundles x.2.spkBundles ∧
      badPeersKeyInd x.2 = badPeersKeyInd st := by
  intro x hx
  have hcomm := pqxdhKeyIndCachedImpl_commutes_cache true S P q st
  unfold CommutesRel at hcomm
  have hmem : (x.1, cacheKeyIndAdvKeys S P x.2) ∈
      support ((pqxdhKeyIndCachedImpl true S P q).run (cacheKeyIndAdvKeys S P st)) := by
    rw [hcomm, support_map]
    exact ⟨x, hx, rfl⟩
  simpa [cacheKeyIndAdvKeys, badPeersKeyInd] using
    pqxdhKeyIndImpl_other_pres true S P q (cacheKeyIndAdvKeys S P st)
      h_not_init h_not_corr h_not_spk h_not_iopk h_not_inoopk _ hmem

/-! ## Pre-sampled one-key `KeyIndFgCutoffState` implementation -/

noncomputable def fg1KeyPreInitPrin (kIdx : ℕ) (optSk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    StateT (KeyIndState S) ProbComp KeyIndResponse := do
  let st ← get
  if st.principals.any (fun (idx, _) => idx == u.val) then
    return .noneResp
  let sk ← liftM (match optSk with
    | some sk0 => if u.val == kIdx then pure sk0 else sampleScalar32
    | none => sampleScalar32)
  let pk := P.x25519Base sk
  let entry : PrincipalEntry := {
    secIKA0    := sk
    ikAPk      := pk
    secIKAsign := sk
    ikSignPk   := pk
    corrupted  := false
  }
  set { st with principals := (u.val, entry) :: st.principals }
  return .initPrinResp pk pk

/-- Pre-sampled one-key `KeyIndFgCutoffState` implementation substituting `optSk` at principal
    `kIdx` during `.initPrin` and delegating all other queries to `pqxdhKeyIndFgImpl`. -/
noncomputable def pqxdhKeyInd1KeyFgPreImpl (kIdx : ℕ) (optSk : Option Bytes)
    (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .initPrin u => liftFgBase (fg1KeyPreInitPrin kIdx optSk S P u)
  | q           => pqxdhKeyIndFgImpl S P q

theorem pqxdhKeyInd1KeyFgPreImpl_non_initPrin_eq_fgPre {S : Setup}
    (kIdx : ℕ) (optSk : Option Bytes) (uSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyInd1KeyFgPreImpl kIdx optSk S P q =
      pqxdhKeyIndFgPreImpl false S.N_send_tot (noSpkIdx S) (some uSk) none S P q := by
  have hfg := (pqxdhKeyIndFgPreImpl_none_none_eq (S := S) false S.N_send_tot (noSpkIdx S) P).symm
  cases q with
  | initPrin u => exact False.elim (hq u rfl)
  | initiateOPK u i bundle =>
    change pqxdhKeyIndFgImpl S P (.initiateOPK u i bundle) = _
    rw [hfg]
    have hlt := initSessionSlotIdx_lt_of_isSendSessionId (.sendOPK u i) trivial
    have hne : (initSessionSlotIdx (.sendOPK u i) == S.N_send_tot) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
    unfold pqxdhKeyIndFgPreImpl fgPreInitiate
    simp [hne]
  | initiateNoOPK u i bundle =>
    change pqxdhKeyIndFgImpl S P (.initiateNoOPK u i bundle) = _
    rw [hfg]
    have hlt := initSessionSlotIdx_lt_of_isSendSessionId (.sendNoOPK u i) trivial
    have hne : (initSessionSlotIdx (.sendNoOPK u i) == S.N_send_tot) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
    unfold pqxdhKeyIndFgPreImpl fgPreInitiate
    simp [hne]
  | genSPK u j =>
    change pqxdhKeyIndFgImpl S P (.genSPK u j) = _
    rw [hfg]
    rfl
  | _ => rfl

theorem pqxdhKeyInd1KeyFgPreImpl_non_initPrin_eq_fgPreIk {S : Setup}
    (kIdx : ℕ) (optSk : Option Bytes) (uSk vSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyInd1KeyFgPreImpl kIdx optSk S P q =
      pqxdhKeyIndFgPreImplIk S.N_send_tot kIdx (some uSk) (some vSk) S P q := by
  rw [pqxdhKeyInd1KeyFgPreImpl_non_initPrin_eq_fgPre kIdx optSk uSk P q hq]
  cases q with
  | initPrin u => exact False.elim (hq u rfl)
  | _ => rfl

theorem mem_support_pqxdhKeyIndFgImpl_base {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgImpl S P q).run hst)) :
    (x.1, x.2.base) ∈ support ((pqxdhKeyIndImpl true S P q).run hst.base) := by
  cases q <;>
  · unfold pqxdhKeyIndFgImpl at hx
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨r, base'⟩, hmem, rfl⟩
    exact hmem

theorem pqxdhKeyInd1KeyFgPreImpl_none_step_base {S : Setup} (kIdx : ℕ) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) :
    Prod.map id KeyIndFgCutoffState.base <$>
      (pqxdhKeyInd1KeyFgPreImpl kIdx none S P q).run hst =
      (pqxdhKeyIndImpl1KeyRo S P q).run hst.base := by
  cases q with
  | initPrin u =>
    unfold pqxdhKeyInd1KeyFgPreImpl fg1KeyPreInitPrin liftFgBase
      pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal
    dsimp only
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases hst.base.principals.any (fun (idx, _) => idx == u.val) with
    | true => simp
    | false =>
      simp [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]
  | roQuery secrets =>
    unfold pqxdhKeyInd1KeyFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl1KeyRo
    simp [map_eq_bind_pure_comp, bind_assoc]
  | _ =>
    unfold pqxdhKeyInd1KeyFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl1KeyRo
    simp [map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyInd1KeyFgPreImpl_none_sim_base {S : Setup} {α : Type}
    (kIdx : ℕ) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S) :
    Prod.map id KeyIndFgCutoffState.base <$>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyInd1KeyFgPreImpl kIdx none S P) oa).run hst =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndState S) ProbComp) +
        pqxdhKeyIndImpl1KeyRo S P) oa).run hst.base := by
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp [StateT.run_pure]
  | query_bind q k ih =>
    cases q with
    | inl uq =>
      simp only [simulateQ_run_query_inl, map_bind]
      congr 1; ext u
      exact ih u hst
    | inr gq =>
      simp only [simulateQ_run_query_inr, map_bind]
      rw [← pqxdhKeyInd1KeyFgPreImpl_none_step_base kIdx P gq hst, bind_map_left]
      congr 1; ext y
      exact ih y.1 y.2

theorem pqxdhKeyInd1KeyFgPreImpl_preserves_hasFiredPrin {S : Setup}
    (kIdx : ℕ) (optSk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyInd1KeyFgPreImpl kIdx optSk S P q).run hst))
    (hFired : hasFiredPrin S kIdx hst) :
    hasFiredPrin S kIdx x.2 := by
  cases q with
  | initPrin u =>
    unfold pqxdhKeyInd1KeyFgPreImpl fg1KeyPreInitPrin at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val) with
    | true =>
      rw [hAny] at hb
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb
      have hB := (Prod.mk.inj hb).2
      unfold hasFiredPrin at hFired ⊢
      rwa [hB]
    | false =>
      rw [hAny] at hb
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb
      rcases hb with ⟨sk, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      unfold hasFiredPrin at hFired ⊢
      rw [hB]
      simp [List.any_cons, hFired]
  | _ =>
    rw [pqxdhKeyInd1KeyFgPreImpl_non_initPrin_eq_fgPre kIdx optSk [] P _
      (fun _ h => by cases h)] at hx
    exact (pqxdhKeyIndFgPreImpl_preserves_hasFired false S.N_send_tot (noSpkIdx S)
      (some []) none P _ hst x hx).2.1 kIdx hFired

theorem evalDist_runKeyInd1KeySim_eq_preSample {S : Setup}
    (kIdx : ℕ) (P : Primitives) (A : KeyIndAdversary S)
    (obs : KeyIndState S → Bool) :
    let fullPre (sk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P
    𝒟[do
        let sk ← sampleScalar32
        let secb ← $ᵗ Bool
        let (_, finalHst) ← (simulateQ (fullPre sk) A.run).run (KeyIndFgCutoffState.empty S secb)
        pure (obs finalHst.base)] =
    𝒟[runKeyInd1KeySim S P A >>= fun (_, _, finalSt) => pure (obs finalSt)] := by
  intro fullPre
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  unfold runKeyInd1KeySim
  simp only [bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hPre :
      𝒟[sampleScalar32 >>= fun sk =>
        (simulateQ (fullPre sk) A.run).run (KeyIndFgCutoffState.empty S secb) >>=
          fun x => pure (obs x.2.base)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (KeyIndFgCutoffState S) ProbComp) +
          pqxdhKeyInd1KeyFgPreImpl kIdx none S P) A.run).run (KeyIndFgCutoffState.empty S secb) >>=
            fun x => pure (obs x.2.base)] := by
    refine evalDist_simulateQ_preSample_slot_eq
      sampleScalar32
      (hasFiredPrin S kIdx)
      (pqxdhKeyInd1KeyFgPreImpl kIdx none S P)
      (fun sk => pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P)
      (fun q s hFired => ⟨?_, fun x hx =>
        pqxdhKeyInd1KeyFgPreImpl_preserves_hasFiredPrin kIdx none P q s x hx hFired⟩)
      (fun q s _ => ?_)
      A.run (KeyIndFgCutoffState.empty S secb) (fun x => pure (obs x.2.base))
    · intro sk
      cases q with
      | initPrin u =>
        unfold pqxdhKeyInd1KeyFgPreImpl fg1KeyPreInitPrin liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        by_cases hSlot : (u.val == kIdx) = true
        · have hany : s.base.principals.any (fun (idx, _) => idx == u.val) = true := by
            unfold hasFiredPrin at hFired
            rw [beq_iff_eq.mp hSlot]; exact hFired
          simp [hany]
        · cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
      | _ => rfl
    · cases q with
      | initPrin u =>
        by_cases hSlot : (u.val == kIdx) = true
        · unfold pqxdhKeyInd1KeyFgPreImpl fg1KeyPreInitPrin liftFgBase
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
          cases s.base.principals.any (fun (idx, _) => idx == u.val) with
          | true => exact Or.inl (fun _ => rfl)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine Or.inr ⟨fun obs' => ?_, fun sk x hx => ?_⟩
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure,
                StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind, bind_assoc]
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure,
                StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind,
                support_pure, Set.mem_singleton_iff] at hx
              have hB := (Prod.mk.inj hx).2
              unfold hasFiredPrin; rw [hB]; simp [hSlot]
        · refine Or.inl (fun sk => ?_)
          unfold pqxdhKeyInd1KeyFgPreImpl fg1KeyPreInitPrin liftFgBase
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
          cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
      | _ => exact Or.inl (fun _ => rfl)
  rw [hPre]
  have hBase := pqxdhKeyInd1KeyFgPreImpl_none_sim_base kIdx P A.run
    (KeyIndFgCutoffState.empty S secb)
  rw [show KeyIndState.empty S secb = (KeyIndFgCutoffState.empty S secb).base from rfl,
    ← hBase, bind_map_left]
  rfl

/-! ## Absorbing forgery and corrupted branches -/

/-- Absorbing win condition for `sigReductionKeyInd1KeyAt`: `st.forgery` holds a valid signature
    under `P.sigPkGen sk` on a message `mStar` not in `msgs`. -/
def Sig1KeyWon {S : Setup} (P : Primitives) (sk : Bytes)
    (st : Sig1KeySimState S) (msgs : List Bytes) : Prop :=
  ∃ mStar sigStar,
    st.forgery = some (mStar, sigStar) ∧
    P.sigVerify (P.sigPkGen sk) mStar sigStar = true ∧
    mStar ∉ msgs

noncomputable def sig1KeyWinBool {S : Setup} {α : Type} (P : Primitives) (sk : Bytes)
    (res : (α × Sig1KeySimState S) × List Bytes) : Bool :=
  let (mStar, sigStar) := res.1.2.forgery.getD ([], [])
  P.sigVerify (P.sigPkGen sk) mStar sigStar && decide (mStar ∉ res.2)

theorem one_le_evalDist_sig1KeyWon {S : Setup} {α : Type}
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (maxLen : ℕ)
    (oa : OracleComp (unifSpec + keyIndSpec S) α)
    (st : Sig1KeySimState S) (msgs : List Bytes)
    (hWon : Sig1KeyWon P sk st msgs) :
    1 ≤ 𝒟[(simulateQ (gapSigEufCmaFullImpl P ddh sk)
            (runWithSigDdhStep (sig1KeyStep S maxLen) oa st)).run msgs >>=
          fun res => pure (sig1KeyWinBool P sk res)] {true} := by
  induction oa using OracleComp.inductionOn generalizing st msgs with
  | pure x =>
    rcases hWon with ⟨mStar, sigStar, hfg, hver, hnotmem⟩
    simp [runWithSigDdhStep_pure, StateT.run_pure, sig1KeyWinBool, hfg, hver, hnotmem]
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [runWithSigDdhStep_query_inl]
      have hq :
          (simulateQ (gapSigEufCmaFullImpl P ddh sk)
            (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl (Sum.inl n))) >>=
              fun u => runWithSigDdhStep (sig1KeyStep S maxLen) (k u) st)).run msgs =
          (liftM (unifSpec.query n) >>= fun u =>
            (simulateQ (gapSigEufCmaFullImpl P ddh sk)
              (runWithSigDdhStep (sig1KeyStep S maxLen) (k u) st)).run msgs) := by
        simp [gapSigEufCmaFullImpl, primBaseImpl, QueryImpl.liftTarget,
          simulateQ_bind, StateT.run_bind, StateT.run_monadLift]
      rw [hq, bind_assoc]
      calc (1 : ℝ≥0∞)
          = 𝒟[liftM (unifSpec.query n) >>= fun _ => pure true] {true} := by
              rw [OracleComp.evalDist_bind_const]; simp
        _ ≤ _ := evalDist_bind_true_mono_of_support _ _ _ (fun u _ => by
              simpa using ih u st msgs hWon)
    | inr gq =>
      rcases hWon with ⟨mStar, sigStar, hfg, hver, hnotmem⟩
      rw [runWithSigDdhStep_query_inr]
      have hStep : sig1KeyStep S maxLen gq st = pure (.noneResp, st) := by
        unfold sig1KeyStep
        simp [hfg]
      rw [hStep, pure_bind]
      exact ih .noneResp st msgs ⟨mStar, sigStar, hfg, hver, hnotmem⟩

theorem fg1KeyPreInitPrin_safe_step (S : Setup) (P : Primitives) (kIdx : ℕ)
    (optSk : Option Bytes) (u : Fin S.N_id) (st : KeyIndState S)
    (hSafe : (keyIndSigLens S).Safe P kIdx st) :
    ∀ x ∈ support ((fg1KeyPreInitPrin kIdx optSk S P u).run st),
      (keyIndSigLens S).Safe P kIdx x.2 := by
  rcases hSafe with ⟨hVP, ⟨ek, hek⟩, hCorr, hClean⟩
  intro x hx
  unfold fg1KeyPreInitPrin at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hAny : st.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    rw [hAny] at hx
    simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hVP, ⟨ek, hek⟩, hCorr, hClean⟩
  | false =>
    rw [hAny] at hx
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨sk0, _, rfl⟩
    let entry : PrincipalEntry := {
      secIKA0 := sk0, ikAPk := P.x25519Base sk0,
      secIKAsign := sk0, ikSignPk := P.x25519Base sk0, corrupted := false }
    have hCons := validPrincipals_cons S u entry st.principals hVP hAny
    have hne : u.val ≠ kIdx := by
      intro rfl
      exact hCons.2 (List.mem_map_of_mem hek)
    refine ⟨hCons.1, ⟨ek, List.mem_cons_of_mem _ hek⟩, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with hEq | hmem
      · injection hEq with h1 _
        exact False.elim (hne h1.symm)
      · exact hCorr e hmem
    · exact cleanPeers_cons_principal S P kIdx u.val entry st.principals
        (badPeersKeyInd st) hClean

theorem pqxdhKeyInd1KeyFgPreImpl_safe_step (S : Setup) (P : Primitives) (kIdx : ℕ)
    (optSk : Option Bytes) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hSafe : (keyIndSigLens S).Safe P kIdx hst.base) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyFgPreImpl kIdx optSk S P q).run hst),
      (keyIndSigLens S).Safe P kIdx x.2.base := by
  intro x hx
  cases q with
  | initPrin u =>
    unfold pqxdhKeyInd1KeyFgPreImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    exact fg1KeyPreInitPrin_safe_step S P kIdx optSk u hst.base hSafe (x.1, x.2.base) hb
  | corruptIK u =>
    have hb := mem_support_pqxdhKeyIndFgImpl_base P (.corruptIK u) hst x hx
    exact (keyIndSigLens S).safe_step_corruptIK P kIdx u hst.base hSafe (x.1, x.2.base) hb
  | genSPK u j =>
    have hb := mem_support_pqxdhKeyIndFgImpl_base P (.genSPK u j) hst x hx
    exact (keyIndSigLens S).safe_step_genSPK P kIdx u j hst.base hSafe (x.1, x.2.base) hb
  | initiateOPK u i bnd =>
    have hb := mem_support_pqxdhKeyIndFgImpl_base P (.initiateOPK u i bnd) hst x hx
    exact (keyIndSigLens S).safe_step_initiate P kIdx bnd _ hst.base
      (pqxdhKeyIndImpl_initiateOPK_pres_raw S P u i bnd hst.base) hSafe (x.1, x.2.base) hb
  | initiateNoOPK u i bnd =>
    have hb := mem_support_pqxdhKeyIndFgImpl_base P (.initiateNoOPK u i bnd) hst x hx
    exact (keyIndSigLens S).safe_step_initiate P kIdx bnd _ hst.base
      (pqxdhKeyIndImpl_initiateNoOPK_pres_raw S P u i bnd hst.base) hSafe (x.1, x.2.base) hb
  | genOPK _ _ _ | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _ | testSession _
  | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
    have hb := mem_support_pqxdhKeyIndFgImpl_base P _ hst x hx
    exact (keyIndSigLens S).safe_step_other P kIdx _ hst.base
      (pqxdhKeyIndImpl_other_pres_raw S P _ hst.base
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
      hSafe (x.1, x.2.base) hb

theorem evalDist_safe_1Key_eq_zero {S : Setup} {α : Type}
    (P : Primitives) (kIdx : ℕ) (optSk : Option Bytes)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (hSafe : (keyIndSigLens S).Safe P kIdx hst.base) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyInd1KeyFgPreImpl kIdx optSk S P) oa).run hst >>=
      fun (_, finalHst) => pure (hasBadSigKeyIndAt S P kIdx finalHst.base)] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure x =>
    have hBadF : hasBadSigKeyIndAt S P kIdx hst.base = false :=
      (keyIndSigLens S).safe_badAt_eq_false P kIdx hst.base hSafe
    simp [StateT.run_pure, hBadF]
  | query_bind q k ih =>
    cases q with
    | inl n =>
      simp only [simulateQ_run_query_inl, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun u _ => ih u hst hSafe)
    | inr gq =>
      simp only [simulateQ_run_query_inr, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun y hy =>
        ih y.1 y.2 (pqxdhKeyInd1KeyFgPreImpl_safe_step S P kIdx optSk gq hst hSafe y hy))

/-! ## Active coupling invariant and per-query step coupling -/

@[simp] private theorem simulateQ_primSigDdhQ_x25519Base_run (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk s : Bytes) (msgs : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (primSigDdhQ (.x25519Base s))).run msgs =
      pure (P.x25519Base s, msgs) :=
  simulateQ_primSigDdhQ_run P ddh sk (.x25519Base s) msgs

@[simp] private theorem simulateQ_primSigDdhQ_kemKeyGen_run (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk seed : Bytes) (msgs : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (primSigDdhQ (.kemKeyGen seed))).run msgs =
      pure (P.kemKeyGen seed, msgs) :=
  simulateQ_primSigDdhQ_run P ddh sk (.kemKeyGen seed) msgs

theorem sessDeadIk_N_send_tot_eq_false {S : Setup} (P : Primitives) (V : Bytes)
    (hst : KeyIndFgCutoffState S) (hValidSess : ValidSessionIds S ((sessPksKeyInd S hst.base).map Prod.fst)) :
    sessDeadIk P S.N_send_tot V hst = false := by
  unfold sessDeadIk
  have hNone : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == S.N_send_tot) = none := by
    rw [List.find?_eq_none]
    intro s hs hBeq
    have hSidMem : s.sid ∈ (sessPksKeyInd S hst.base).map Prod.fst := by
      simp only [sessPksKeyInd, List.mem_map]
      exact ⟨(s.sid, s.hdr.ekAPk), ⟨s, hs, rfl⟩, rfl⟩
    have hSend : IsSendSessionId S s.sid := hValidSess.1 s.sid hSidMem
    have hLt := initSessionSlotIdx_lt_of_isSendSessionId s.sid hSend
    exact absurd (beq_iff_eq.mp hBeq) (Nat.ne_of_lt hLt)
  rw [hNone]

theorem deadDh2_N_send_tot_eq_deadDh1 {S : Setup} (P : Primitives) (kIdx : ℕ) (V : Bytes)
    (hst : KeyIndFgCutoffState S)
    (hTgtV : prinTargetIsV kIdx V hst = true)
    (hValidSess : ValidSessionIds S ((sessPksKeyInd S hst.base).map Prod.fst)) :
    deadDh2 P S.N_send_tot kIdx V hst = deadDh1 kIdx hst := by
  unfold deadDh2
  rw [hTgtV, sessDeadIk_N_send_tot_eq_false P V hst hValidSess, Bool.true_and, Bool.or_false]

theorem safe_of_deadDh1_true {S : Setup} (P : Primitives) (kIdx : ℕ)
    (hst : KeyIndFgCutoffState S)
    (hVP : ValidPrincipals S hst.base.principals)
    (hClean : CleanPeers S P kIdx hst.base.principals (badPeersKeyInd hst.base))
    (hDead1 : deadDh1 kIdx hst = true) :
    (keyIndSigLens S).Safe P kIdx hst.base := by
  unfold deadDh1 at hDead1
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == kIdx) with
  | none => rw [hF] at hDead1; cases hDead1
  | some p =>
    rcases p with ⟨u0, ek⟩
    rw [hF] at hDead1
    dsimp only at hDead1
    have hu0Eq : u0 = kIdx :=
      beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == kIdx) hF)
    subst hu0Eq
    have hekMem : (u0, ek) ∈ hst.base.principals := List.mem_of_find?_eq_some hF
    refine ⟨hVP, ⟨ek, hekMem⟩, ?_, hClean⟩
    intro e heMem
    have hEq := mem_principals_unique hVP.2 heMem hekMem
    subst hEq
    exact hDead1

/-- Active coupling relation between the pre-sampled one-key game state `hst` and the
    `GapSigEufCma` simulator state `(st, msgs)`. -/
def Sig1KeyRel (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (kIdx : ℕ)
    (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : Sig1KeySimState S) (msgs : List Bytes) : Prop :=
  st.forgery = none ∧
  st.targetParty = kIdx ∧
  st.targetPk = P.sigPkGen sk ∧
  (∃ st0 : FgKeyIndSimState S,
    st.fg = clearFgTargetSign kIdx st0 ∧
    FgSimInvDh2 S b P hP S.N_send_tot kIdx uSk sk huSk hvSk rem hst st0) ∧
  deadDh1 kIdx hst = false ∧
  CleanPeers S P kIdx hst.base.principals (badPeersKeyInd hst.base) ∧
  2 * min S.N_spk_tot S.N_recv ≤
    2 * st.signBudget + (bundleSignedMessages kIdx hst.base.spkBundles).length ∧
  (∀ m ∈ msgs, m ∈ bundleSignedMessages kIdx hst.base.spkBundles) ∧
  (∀ kv ∈ hst.base.principals,
    (kv.1 == kIdx) = true → kv.2.secIKAsign = sk ∧ kv.2.ikSignPk = P.sigPkGen sk)

theorem sig1KeyRel_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (kIdx : ℕ)
    (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32) (secb : Bool) :
    Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk b.q_total
      (KeyIndFgCutoffState.empty S secb)
      (Sig1KeySimState.empty S secb kIdx (P.sigPkGen sk)) [] := by
  refine ⟨rfl, rfl, rfl,
    ⟨FgGapDh.FgKeyIndSimState.empty S secb, rfl,
      fgSimInvDh2_empty S b P hP S.N_send_tot kIdx uSk sk huSk hvSk secb⟩,
    rfl, cleanPeers_nil S P kIdx [], Nat.le_refl (2 * min S.N_spk_tot S.N_recv),
    fun _ h => False.elim (List.not_mem_nil h),
    fun _ h => False.elim (List.not_mem_nil h)⟩

theorem sig1KeyRel_weaken_rem {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {kIdx : ℕ}
    {uSk sk : Bytes} {huSk : uSk.length = 32} {hvSk : sk.length = 32}
    {rem : ℕ} {hst : KeyIndFgCutoffState S} {st : Sig1KeySimState S} {msgs : List Bytes}
    (hRel : Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk (rem + 1) hst st msgs) :
    Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst st msgs := by
  rcases hRel with ⟨hFgNone, hParty, hPk, ⟨st0, hClear, hInv⟩, hDead1, hClean, hBud, hMsgs, hSign⟩
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact ⟨hFgNone, hParty, hPk,
    ⟨st0, hClear, ⟨h1, h2, h3, by omega, by omega, h6, h7, h8, h9, h10, h11⟩⟩,
    hDead1, hClean, hBud, hMsgs, hSign⟩

theorem extractBundleForgery_clear_erase (P : Primitives) (kIdx : ℕ) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) :
    extractBundleForgery P kIdx targetPk
      (clearPrincipalsTargetSign kIdx (erasePrincipalsFg kIdx principals)) spkBundles bundle none =
      extractBundleForgery P kIdx targetPk principals spkBundles bundle none := by
  unfold extractBundleForgery
  rw [isHonestUncorruptedPeer_clearPrincipalsTargetSign, isHonestUncorruptedPeer_erasePrincipalsFg]

theorem sig1KeyStep_delegated_run {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (kIdx : ℕ) (uSk sk : Bytes) (maxLen : ℕ)
    (q : KeyIndQuery S) (st : Sig1KeySimState S) (st0 : FgKeyIndSimState S) (msgs : List Bytes)
    (hClear : st.fg = clearFgTargetSign kIdx st0)
    (hPk : st.targetPk = P.x25519Base sk)
    (hNoInit : ∀ u, q ≠ .initPrin u)
    (hNoTargetCorr : ∀ u, q = .corruptIK u → (u.val == kIdx) = false)
    (hNoTargetSpk : ∀ u j, q = .genSPK u j → (u.val == kIdx) = false) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk)
      (do
        let (out, fg') ← embedGdhSigDdh
          (fgKeyIndStep false S.N_send_tot S.N_spk_tot S maxLen [] st.targetPk q st.fg)
        return (out, { st with fg := fg' }))).run msgs =
    (fun p : KeyIndResponse × FgKeyIndSimState S =>
      ((p.1, { st with fg := clearFgTargetSign kIdx p.2 }), msgs)) <$>
      (fgKeyIndSimImplIk P ddh S.N_send_tot kIdx S maxLen
        (P.x25519Base uSk) (P.x25519Base sk) q).run st0 := by
  have hNoSpk : S.N_spk_tot = noSpkIdx S := rfl
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_embedGdhSigDdh_run,
    simulateQ_gapDhFullImpl_fgKeyIndStep, simulateQ_pure, StateT.run_pure,
    map_eq_bind_pure_comp, bind_assoc]
  have hStepIk :
      fgKeyIndStepPureIk P ddh S.N_send_tot kIdx S maxLen
        (P.x25519Base uSk) (P.x25519Base sk) q st0 =
      fgKeyIndStepPure P ddh false S.N_send_tot (noSpkIdx S) S maxLen
        (P.x25519Base uSk) (P.x25519Base sk) q st0 := by
    cases q with
    | initPrin u => exact False.elim (hNoInit u rfl)
    | _ => rfl
  rw [hClear, hPk, hNoSpk,
    fgKeyIndStepPure_false_N_send_tot_U_irrel P ddh (noSpkIdx S) S maxLen [] (P.x25519Base uSk),
    fgKeyIndStepPure_clearFgTargetSign P ddh (noSpkIdx S) kIdx S maxLen
      (P.x25519Base uSk) (P.x25519Base sk) q st0 hNoInit hNoTargetCorr hNoTargetSpk,
    fgKeyIndSimImplIk_run, hStepIk]
  simp [map_eq_bind_pure_comp, bind_assoc]

/-! ### Per-Query Step Coupling Lemmas -/

private theorem sig1Key_step_initPrin (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (kIdx : ℕ)
    (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32)
    (u : Fin S.N_id) (rem : ℕ)
    (hst : KeyIndFgCutoffState S) (st : Sig1KeySimState S) (msgs : List Bytes)
    (hRel : Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk (rem + 1) hst st msgs)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : (KeyIndResponse × Sig1KeySimState S) × List Bytes → ProbComp Bool)
    (hCont : ∀ r hst' st' msgs',
      Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst' st' msgs' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 ((r, st'), msgs')] {true}) :
    𝒟[(pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.initPrin u)).run hst >>= k1] {true} ≤
    𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (sig1KeyStep S b.q_total (.initPrin u) st)).run msgs >>= k2] {true} := by
  rcases st with ⟨fg, targetParty, targetPk, signBudget, forgery⟩
  have hRel0 := hRel
  rcases hRel with ⟨hFgNone, hParty, hPk, ⟨st0, hClear, hInv⟩, hDead1, hClean, hBud, hMsgs, hSign⟩
  dsimp only at hFgNone hParty hPk hClear hBud
  subst forgery targetParty targetPk
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hSigPk : P.sigPkGen sk = P.x25519Base sk :=
    congrFun hP.toWellFormedPrimitivesδ.sigPkGen_eq_x25519Base sk
  have hAnySim :
      fg.base.principals.any (fun (idx, _) => idx == u.val) =
      hst.base.principals.any (fun (idx, _) => idx == u.val) := by
    rw [hClear]; dsimp only [clearFgTargetSign]
    rw [any_idx_clearPrincipalsTargetSign, hBaseEq]
    exact any_idx_erasePrincipalsFg kIdx u.val hst.base.principals
  unfold pqxdhKeyInd1KeyFgPreImpl fg1KeyPreInitPrin liftFgBase sig1KeyStep
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hAnySim,
    StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    simp only [↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
    exact hCont .noneResp hst _ msgs (sig1KeyRel_weaken_rem hRel0)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hTgt : (u.val == kIdx) = true
    · have huEq : u.val = kIdx := beq_iff_eq.mp hTgt
      simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_pure,
        StateT.run_monadLift, monadLift_self, StateT.run_set, bind_assoc, pure_bind,
        simulateQ_bind, simulateQ_unifSigDdh_run, simulateQ_pure, bind_map_left, hSigPk]
      conv_lhs => rw [← evalDist_sampleScalar32_const]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun x _ => ?_)
      rw [simulateQ_primSigDdhQ_x25519Base_run, pure_bind]
      let pk := P.x25519Base sk
      let entry1 : PrincipalEntry := {
        secIKA0 := sk, ikAPk := pk, secIKAsign := sk, ikSignPk := pk, corrupted := false }
      let entry0 : PrincipalEntry := {
        secIKA0 := [], ikAPk := pk, secIKAsign := sk, ikSignPk := pk, corrupted := false }
      let entrySim : PrincipalEntry := {
        secIKA0 := [], ikAPk := pk, secIKAsign := [], ikSignPk := pk, corrupted := false }
      let hst' : KeyIndFgCutoffState S :=
        { hst with base := { hst.base with principals := (u.val, entry1) :: hst.base.principals } }
      let st0' : FgKeyIndSimState S :=
        { st0 with base := { st0.base with principals := (u.val, entry0) :: st0.base.principals } }
      let st' : Sig1KeySimState S :=
        { fg := { fg with base :=
            { fg.base with principals := (u.val, entrySim) :: fg.base.principals } }
          targetParty := kIdx
          targetPk := pk
          signBudget := signBudget
          forgery := none }
      have hDead1' : deadDh1 kIdx hst' = false := by
        unfold deadDh1; simp [hst', huEq, entry1]
      have hTgtV' : prinTargetIsV kIdx pk hst' = true := by
        unfold prinTargetIsV at hTgtV ⊢
        simp [hst', entry1, pk, huEq, hTgtV]
      have hClear' : st'.fg = clearFgTargetSign kIdx st0' := by
        dsimp only [st', st0', clearFgTargetSign, clearPrincipalsTargetSign]
        rw [hClear]; dsimp only [clearFgTargetSign, clearPrincipalsTargetSign]
        simp [huEq, entry0, entrySim]
      apply hCont (.initPrinResp pk pk) hst' st' msgs
      refine ⟨rfl, rfl, hSigPk.symm, ⟨st0', hClear', ?_⟩, hDead1',
        cleanPeers_cons_principal S P kIdx u.val entry1 hst.base.principals
          (badPeersKeyInd hst.base) hClean,
        hBud, hMsgs, ?_⟩
      · refine ⟨?_, hAdvEq, hCache, by dsimp [st0']; omega, by dsimp [hst']; omega,
          ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
            hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩,
          hTgtV', ?_, hSpks, hOpks, hSess⟩
        · dsimp only [st0', hst', eraseStateFgIk]
          rw [hBaseEq]
          simp [eraseStateFgIk, erasePrincipalsFg, erasePrincipalEntryFg, huEq, entry1, entry0]
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hvSk, rfl, fun _ => rfl⟩
          · exact hPrins kv hMem
      · intro kv hkv hk
        rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨rfl, hSigPk.symm⟩
        · exact hSign kv hMem hk
    · have hTgtF : (u.val == kIdx) = false := Bool.eq_false_iff.mpr hTgt
      have hNe : u.val ≠ kIdx := beq_eq_false_iff_ne.mp hTgtF
      simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        simulateQ_bind, simulateQ_unifSigDdh_run, simulateQ_pure, bind_map_left]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKA0 hSec0 => ?_)
      rw [simulateQ_primSigDdhQ_x25519Base_run, pure_bind]
      have hLen0 : secIKA0.length = 32 := length_of_mem_support_sampleScalar32 hSec0
      let pk0 := P.x25519Base secIKA0
      let entry1 : PrincipalEntry := {
        secIKA0 := secIKA0, ikAPk := pk0, secIKAsign := secIKA0, ikSignPk := pk0,
        corrupted := false }
      let hst' : KeyIndFgCutoffState S :=
        { hst with base := { hst.base with principals := (u.val, entry1) :: hst.base.principals } }
      let st0' : FgKeyIndSimState S :=
        { st0 with base := { st0.base with principals := (u.val, entry1) :: st0.base.principals } }
      let st' : Sig1KeySimState S :=
        { fg := { fg with base :=
            { fg.base with principals := (u.val, entry1) :: fg.base.principals } }
          targetParty := kIdx
          targetPk := P.sigPkGen sk
          signBudget := signBudget
          forgery := none }
      have hDead1' : deadDh1 kIdx hst' = false := by
        unfold deadDh1 at hDead1 ⊢
        simp [hst', hNe, hDead1]
      have hTgtV' : prinTargetIsV kIdx (P.x25519Base sk) hst' = true := by
        unfold prinTargetIsV at hTgtV ⊢
        simp [hst', entry1, hNe, hTgtV]
      have hClear' : st'.fg = clearFgTargetSign kIdx st0' := by
        dsimp only [st', st0', clearFgTargetSign, clearPrincipalsTargetSign]
        rw [hClear]; dsimp only [clearFgTargetSign, clearPrincipalsTargetSign]
        simp [hNe]
      apply hCont (.initPrinResp pk0 pk0) hst' st' msgs
      refine ⟨rfl, rfl, rfl, ⟨st0', hClear', ?_⟩, hDead1',
        cleanPeers_cons_principal S P kIdx u.val entry1 hst.base.principals
          (badPeersKeyInd hst.base) hClean,
        hBud, hMsgs, ?_⟩
      · refine ⟨?_, hAdvEq, hCache, by dsimp [st0']; omega, by dsimp [hst']; omega,
          ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
            hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩,
          hTgtV', ?_, hSpks, hOpks, hSess⟩
        · dsimp only [st0', hst', eraseStateFgIk]
          rw [hBaseEq]
          simp [eraseStateFgIk, erasePrincipalsFg, erasePrincipalEntryFg,
            beq_eq_false_iff_ne.mp hTgtF]
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hLen0, rfl, fun h => by rw [hTgtF] at h; cases h⟩
          · exact hPrins kv hMem
      · intro kv hkv hk
        rcases List.mem_cons.mp hkv with rfl | hMem
        · rw [hTgtF] at hk; cases hk
        · exact hSign kv hMem hk

private theorem sig1Key_step_target_genSPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (kIdx : ℕ)
    (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hu : (u.val == kIdx) = true) (rem : ℕ)
    (hst : KeyIndFgCutoffState S) (st : Sig1KeySimState S) (msgs : List Bytes)
    (hRel : Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk (rem + 1) hst st msgs)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : (KeyIndResponse × Sig1KeySimState S) × List Bytes → ProbComp Bool)
    (hCont : ∀ r hst' st' msgs',
      Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst' st' msgs' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 ((r, st'), msgs')] {true}) :
    𝒟[(pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.genSPK u j)).run hst >>= k1] {true} ≤
    𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (sig1KeyStep S b.q_total (.genSPK u j) st)).run msgs >>= k2] {true} := by
  rcases st with ⟨fg, targetParty, targetPk, signBudget, forgery⟩
  have hRel0 := hRel
  rcases hRel with ⟨hFgNone, hParty, hPk, ⟨st0, hClear, hInv⟩, hDead1, hClean, hBud, hMsgs, hSign⟩
  dsimp only at hFgNone hParty hPk hClear hBud
  subst forgery targetParty targetPk
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have huEq : u.val = kIdx := beq_iff_eq.mp hu
  have hSpk0 : st0.base.spkBundles = hst.base.spkBundles := by
    rw [hBaseEq]; rfl
  have hSpkEq : fg.base.spkBundles = hst.base.spkBundles := by
    rw [hClear]; dsimp only [clearFgTargetSign]; exact hSpk0
  have hFindSim :
      fg.base.principals.find? (fun (idx, _) => idx == u.val) =
      ((hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg kIdx idx e))).map
        (fun (idx, e) => if idx == kIdx then (idx, { e with secIKAsign := [] }) else (idx, e)) := by
    rw [hClear]; dsimp only [clearFgTargetSign]
    rw [find?_idx_clearPrincipalsTargetSign, hBaseEq]
    dsimp only [eraseStateFgIk]
    rw [find?_idx_erasePrincipalsFg]
  unfold pqxdhKeyInd1KeyFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl sampleKemKeyGen sig1KeyStep
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hu, hSpkEq,
    StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
  cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) with
  | true =>
    simp only [↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
    exact hCont .noneResp hst _ msgs (sig1KeyRel_weaken_rem hRel0)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      have hFSim : fg.base.principals.find? (fun (idx, _) => idx == u.val) = none := by
        rw [hFindSim, hFP]; rfl
      rw [hFSim]
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      exact hCont .noneResp hst _ msgs (sig1KeyRel_weaken_rem hRel0)
    | some p =>
      rcases p with ⟨u0, uEntry⟩
      have hu0Mem : (u0, uEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
      have hu0U : u0 = u.val :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hFP)
      have hu0K : (u0 == kIdx) = true := by rw [hu0U]; exact hu
      have hu0Eq : u0 = kIdx := beq_iff_eq.mp hu0K
      have hSignEq : uEntry.secIKAsign = sk := (hSign (u0, uEntry) hu0Mem hu0K).1
      have hFSim :
          fg.base.principals.find? (fun (idx, _) => idx == u.val) =
          some (u0, { erasePrincipalEntryFg kIdx u0 uEntry with secIKAsign := [] }) := by
        rw [hFindSim, hFP]
        simp [hu0Eq]
      let dummyB : SpkBundleEntry := {
        spkSk := [], spkPk := [], spkSig := [], pqspkSk := [], pqspkPk := [], pqspkSig := [] }
      have hLenLt :
          (bundleSignedMessages kIdx hst.base.spkBundles).length + 2 ≤
            2 * min S.N_spk_tot S.N_recv := by
        rw [← huEq]
        exact bundleSignedMessages_length_add_two_le S u j dummyB hst.base.spkBundles
          hValidEc.2.1 hAny
      obtain ⟨sb', hSbEq⟩ : ∃ sb', signBudget = sb' + 1 := ⟨signBudget - 1, by omega⟩
      rw [hFSim, hSbEq]
      dsimp only
      simp only [hSignEq, erasePrincipalEntryFg_ikAPk, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_unifSigDdh_run,
        bind_map_left, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun spkSk hSpkSk => ?_)
      have hSpkLen : spkSk.length = 32 := length_of_mem_support_sampleScalar32 hSpkSk
      rw [simulateQ_primSigDdhQ_x25519Base_run, pure_bind]
      simp only [simulateQ_sigChalQ_run, bind_map_left]
      refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
      refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun seedKem _ => ?_)
      rw [simulateQ_primSigDdhQ_kemKeyGen_run, pure_bind]
      dsimp only
      refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
      let spkPk := P.x25519Base spkSk
      let spkSig := P.sigSign sk (encodeEC spkPk) rSpk
      let pqspkPk := (P.kemKeyGen seedKem).1
      let pqspkSk := (P.kemKeyGen seedKem).2
      let pqspkSig := P.sigSign sk (encodeKEM pqspkPk) rPq
      let bEntry : SpkBundleEntry := {
        spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
        pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
      let bundleOut : PreKeyBundleInput := {
        ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig,
        opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
      let hst' : KeyIndFgCutoffState S :=
        { hst with base := { hst.base with
            spkBundles := ((u.val, j.val), bEntry) :: hst.base.spkBundles } }
      let st0' : FgKeyIndSimState S :=
        { st0 with base := { st0.base with
            spkBundles := ((u.val, j.val), bEntry) :: st0.base.spkBundles } }
      let st' : Sig1KeySimState S :=
        { fg := { fg with base := { fg.base with
            spkBundles := ((u.val, j.val), bEntry) :: hst.base.spkBundles } }
          targetParty := kIdx
          targetPk := P.sigPkGen sk
          signBudget := sb'
          forgery := none }
      have hClear' : st'.fg = clearFgTargetSign kIdx st0' := by
        dsimp only [st', st0', clearFgTargetSign]
        rw [hClear]; dsimp only [clearFgTargetSign]
        rw [hSpk0]
      apply hCont (.bundleResp bundleOut) hst' st'
        (encodeKEM pqspkPk :: encodeEC spkPk :: msgs)
      refine ⟨rfl, rfl, rfl, ⟨st0', hClear', ?_⟩, hDead1, hClean, ?_, ?_, hSign⟩
      · refine ⟨?_, hAdvEq, hCache, by dsimp [st0']; omega, by dsimp [hst']; omega,
          ⟨hValidEc.1,
            (validSpkBundles_cons S u j bEntry hst.base.spkBundles hValidEc.2.1 hAny).1,
            hValidEc.2.2.1, hValidEc.2.2.2⟩,
          hTgtV, hPrins, ?_, hOpks, hSess⟩
        · dsimp only [st0', hst', eraseStateFgIk]; rw [hBaseEq]; rfl
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hSpkLen, rfl⟩
          · exact hSpks kv hMem
      · dsimp only [st', hst']
        rw [huEq, bundleSignedMessages_cons_eq, List.length_cons, List.length_cons]
        omega
      · intro m hm
        dsimp only [hst']
        rw [huEq, bundleSignedMessages_cons_eq]
        rcases List.mem_cons.mp hm with rfl | hm1
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_cons.mp hm1 with rfl | hm2
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hMsgs m hm2))

private theorem sig1Key_step_initiate_post {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {kIdx : ℕ}
    {uSk sk : Bytes} {huSk : uSk.length = 32} {hvSk : sk.length = 32}
    {rem : ℕ} {hst hst' : KeyIndFgCutoffState S}
    {st : Sig1KeySimState S} {st0' : FgKeyIndSimState S}
    {msgs : List Bytes} {bundle : PreKeyBundleInput}
    (hFgNone : st.forgery = none) (hParty : st.targetParty = kIdx) (hPk : st.targetPk = P.sigPkGen sk)
    (hVP : ValidPrincipals S hst.base.principals)
    (hDead1 : deadDh1 kIdx hst = false)
    (hClean : CleanPeers S P kIdx hst.base.principals (badPeersKeyInd hst.base))
    (hBud : 2 * min S.N_spk_tot S.N_recv ≤
      2 * st.signBudget + (bundleSignedMessages kIdx hst.base.spkBundles).length)
    (hMsgs : ∀ m ∈ msgs, m ∈ bundleSignedMessages kIdx hst.base.spkBundles)
    (hSign : ∀ kv ∈ hst.base.principals,
      (kv.1 == kIdx) = true → kv.2.secIKAsign = sk ∧ kv.2.ikSignPk = P.sigPkGen sk)
    (hExtNone : extractBundleForgery P kIdx (P.sigPkGen sk)
      hst.base.principals hst.base.spkBundles bundle none = none)
    (hPost : InitPostKeyInd P bundle hst.base hst'.base)
    (hDead2' : deadDh2 P S.N_send_tot kIdx (P.x25519Base sk) hst' = false)
    (hInv' : FgSimInvDh2 S b P hP S.N_send_tot kIdx uSk sk huSk hvSk rem hst' st0') :
    Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst'
      { st with fg := clearFgTargetSign kIdx st0' } msgs := by
  have hDead1' : deadDh1 kIdx hst' = false := by
    rw [← deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst' hInv'.2.2.2.2.2.2.1
      hInv'.2.2.2.2.2.1.2.2.2.1]
    exact hDead2'
  rcases hPost with ⟨hPrinEq, hSpkEq, hBpEq | ⟨opkEntries, hBpCons, hSigEc, hSigKem, hFresh, hBad⟩⟩
  · refine ⟨hFgNone, hParty, hPk, ⟨st0', rfl, hInv'⟩, hDead1', ?_, ?_, ?_, ?_⟩
    · rw [hPrinEq, hBpEq]; exact hClean
    · rw [hSpkEq]; exact hBud
    · rw [hSpkEq]; exact hMsgs
    · rw [hPrinEq]; exact hSign
  · have hClean' : CleanPeers S P kIdx hst'.base.principals (badPeersKeyInd hst'.base) := by
      rw [hPrinEq, hBpCons]
      by_cases hkMem : ∃ e, (kIdx, e) ∈ hst.base.principals
      · rcases hkMem with ⟨ek, hekMem⟩
        have hFindK := find?_idx_eq_some_of_mem hst.base.principals hVP.2 kIdx ek hekMem
        have hekCorr : ek.corrupted = false := by
          unfold deadDh1 at hDead1
          rw [hFindK] at hDead1
          exact hDead1
        have hekSign := hSign (kIdx, ek) hekMem (beq_self_eq_true kIdx)
        exact cleanPeers_cons_of_extractBundleForgery_eq_none S P kIdx sk
          hst.base.principals hst.base.spkBundles opkEntries (badPeersKeyInd hst.base) bundle
          hVP ⟨ek, hekMem, hekSign.1, hekSign.2, hekCorr⟩ hClean hExtNone
          hSigEc hSigKem hFresh hBad
      · refine cleanPeers_cons_of_before S P kIdx hst.base.principals
          (badPeersKeyInd hst.base) bundle.ikB (fun p hp => ⟨hVP.1 p hp, ?_⟩) hClean hFresh
        intro hpEq
        exact hkMem ⟨p.2, hpEq ▸ hp⟩
    refine ⟨hFgNone, hParty, hPk, ⟨st0', rfl, hInv'⟩, hDead1', hClean', ?_, ?_, ?_⟩
    · rw [hSpkEq]; exact hBud
    · rw [hSpkEq]; exact hMsgs
    · rw [hPrinEq]; exact hSign

private theorem sig1Key_step_other (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (kIdx : ℕ)
    (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ)
    (hNoInit : ∀ u, q ≠ .initPrin u)
    (hNoCorr : ∀ u, q ≠ .corruptIK u)
    (hNoSpk : ∀ u j, q ≠ .genSPK u j)
    (hNoIOpk : ∀ u i bnd, q ≠ .initiateOPK u i bnd)
    (hNoINoOpk : ∀ u i bnd, q ≠ .initiateNoOPK u i bnd)
    (hst : KeyIndFgCutoffState S) (st : Sig1KeySimState S) (msgs : List Bytes)
    (hRel : Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk (rem + 1) hst st msgs)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : (KeyIndResponse × Sig1KeySimState S) × List Bytes → ProbComp Bool)
    (hCont : ∀ r hst' st' msgs',
      Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst' st' msgs' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 ((r, st'), msgs')] {true}) :
    𝒟[(pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P q).run hst >>= k1] {true} ≤
    𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (sig1KeyStep S b.q_total q st)).run msgs >>= k2] {true} := by
  rcases hRel with ⟨hFgNone, hParty, hPk, ⟨st0, hClear, hInv⟩, hDead1, hClean, hBud, hMsgs, hSign⟩
  have hSigPk : P.sigPkGen sk = P.x25519Base sk :=
    congrFun hP.toWellFormedPrimitivesδ.sigPkGen_eq_x25519Base sk
  have hDead2 : deadDh2 P S.N_send_tot kIdx (P.x25519Base sk) hst = false := by
    rw [deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst
      hInv.2.2.2.2.2.2.1 hInv.2.2.2.2.2.1.2.2.2.1]
    exact hDead1
  have hStepR :
      sig1KeyStep S b.q_total q st =
        (do
          let (out, fg') ← embedGdhSigDdh
            (fgKeyIndStep false S.N_send_tot S.N_spk_tot S b.q_total [] st.targetPk q st.fg)
          return (out, { st with fg := fg' })) := by
    cases q with
    | initPrin u => exact False.elim (hNoInit u rfl)
    | genSPK u j => exact False.elim (hNoSpk u j rfl)
    | initiateOPK u i bnd => exact False.elim (hNoIOpk u i bnd rfl)
    | initiateNoOPK u i bnd => exact False.elim (hNoINoOpk u i bnd rfl)
    | _ => unfold sig1KeyStep; simp [hFgNone]
  let m1 := (pqxdhKeyIndFgPreImplIk S.N_send_tot kIdx (some uSk) (some sk) S P q).run hst
  have hm1Eq : (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P q).run hst = m1 := by
    rw [pqxdhKeyInd1KeyFgPreImpl_non_initPrin_eq_fgPreIk kIdx (some sk) uSk sk P q hNoInit]
  rw [hm1Eq, evalDist_bind_withSupp_eq m1 k1, hStepR,
    sig1KeyStep_delegated_run P P.isValidDhTriple kIdx uSk sk b.q_total q st st0 msgs
      hClear (hPk.trans hSigPk) hNoInit
      (fun u h => False.elim (hNoCorr u h))
      (fun u j h => False.elim (hNoSpk u j h)),
    bind_map_left]
  refine fgStepCoupling_dh2 S b P hP S.N_send_tot kIdx uSk sk huSk hvSk q rem hst st0
    hDead2 hInv (withSupp m1 k1)
    (fun p => k2 ((p.1, { st with fg := clearFgTargetSign kIdx p.2 }), msgs))
    (fun r hst' st0' hDead2' hInv' => ?_) (fun r hst' hDead2' => ?_)
  · unfold withSupp
    split_ifs with hx
    · have hxFg : (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P q).run hst) := by
        rw [show pqxdhKeyIndFgImpl S P q = pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P q from by
          cases q with
          | initPrin u => exact False.elim (hNoInit u rfl)
          | _ => rfl]
        rwa [hm1Eq]
      have hb := mem_support_pqxdhKeyIndFgImpl_base P q hst (r, hst') hxFg
      have hPres := pqxdhKeyIndImpl_other_pres_raw S P q hst.base
        hNoInit hNoCorr hNoSpk hNoIOpk hNoINoOpk (r, hst'.base) hb
      have hDead1' : deadDh1 kIdx hst' = false := by
        rw [← deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst'
          hInv'.2.2.2.2.2.2.1 hInv'.2.2.2.2.2.1.2.2.2.1]
        exact hDead2'
      apply hCont r hst' { st with fg := clearFgTargetSign kIdx st0' } msgs
      refine ⟨hFgNone, hParty, hPk, ⟨st0', rfl, hInv'⟩, hDead1', ?_, ?_, ?_, ?_⟩
      · rw [hPres.1, hPres.2.2]; exact hClean
      · rw [hPres.2.1.2.2.2 kIdx]; exact hBud
      · intro m hm; rw [hPres.2.1.2.2.2 kIdx]; exact hMsgs m hm
      · rw [hPres.1]; exact hSign
    · simp
  · unfold withSupp
    split_ifs with hx
    · exfalso
      have hxFg : (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P q).run hst) := by
        rw [show pqxdhKeyIndFgImpl S P q = pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P q from by
          cases q with
          | initPrin u => exact False.elim (hNoInit u rfl)
          | _ => rfl]
        rwa [hm1Eq]
      have hb := mem_support_pqxdhKeyIndFgImpl_base P q hst (r, hst') hxFg
      have hPres := pqxdhKeyIndImpl_other_pres_raw S P q hst.base
        hNoInit hNoCorr hNoSpk hNoIOpk hNoINoOpk (r, hst'.base) hb
      have hValidEc' := pqxdhKeyIndImpl_validKeyIndEc_step true S P q hst.base
        ⟨hInv.2.2.2.2.2.1.1, hInv.2.2.2.2.2.1.2.1, hInv.2.2.2.2.2.1.2.2.1,
          hInv.2.2.2.2.2.1.2.2.2.1⟩ (r, hst'.base) hb
      have hTgtV' : prinTargetIsV kIdx (P.x25519Base sk) hst' = true := by
        unfold prinTargetIsV; rw [hPres.1]; exact hInv.2.2.2.2.2.2.1
      rw [deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst' hTgtV'
        hValidEc'.2.2.2, deadDh1_eq_of_principals kIdx hPres.1, hDead1] at hDead2'
      cases hDead2'
    · simp

theorem sig1Key_step_coupling (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (kIdx : ℕ)
    (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ)
    (hst : KeyIndFgCutoffState S) (st : Sig1KeySimState S) (msgs : List Bytes)
    (hRel : Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk (rem + 1) hst st msgs)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : (KeyIndResponse × Sig1KeySimState S) × List Bytes → ProbComp Bool)
    (hSafeCont : ∀ r hst', (keyIndSigLens S).Safe P kIdx hst'.base → 𝒟[k1 (r, hst')] {true} = 0)
    (hWonCont : ∀ r st' msgs', Sig1KeyWon P sk st' msgs' → 1 ≤ 𝒟[k2 ((r, st'), msgs')] {true})
    (hCont : ∀ r hst' st' msgs',
      Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst' st' msgs' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 ((r, st'), msgs')] {true}) :
    𝒟[(pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P q).run hst >>= k1] {true} ≤
    𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (sig1KeyStep S b.q_total q st)).run msgs >>= k2] {true} := by
  cases q with
  | initPrin u =>
    exact sig1Key_step_initPrin S b P hP kIdx uSk sk huSk hvSk u rem hst st msgs hRel k1 k2 hCont
  | genSPK u j =>
    by_cases hu : (u.val == kIdx) = true
    · exact sig1Key_step_target_genSPK S b P hP kIdx uSk sk huSk hvSk u j hu rem hst st msgs
        hRel k1 k2 hCont
    · have huF : (u.val == kIdx) = false := Bool.eq_false_iff.mpr hu
      rcases hRel with ⟨hFgNone, hParty, hPk, ⟨st0, hClear, hInv⟩, hDead1, hClean, hBud, hMsgs, hSign⟩
      have hSigPk : P.sigPkGen sk = P.x25519Base sk :=
        congrFun hP.toWellFormedPrimitivesδ.sigPkGen_eq_x25519Base sk
      have hDead2 : deadDh2 P S.N_send_tot kIdx (P.x25519Base sk) hst = false := by
        rw [deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst
          hInv.2.2.2.2.2.2.1 hInv.2.2.2.2.2.1.2.2.2.1]
        exact hDead1
      have hStepR : sig1KeyStep S b.q_total (.genSPK u j) st =
          (do
            let (out, fg') ← embedGdhSigDdh
              (fgKeyIndStep false S.N_send_tot S.N_spk_tot S b.q_total [] st.targetPk
                (.genSPK u j) st.fg)
            return (out, { st with fg := fg' })) := by
        unfold sig1KeyStep; simp [hFgNone, hParty, huF]
      let m1 := (pqxdhKeyIndFgPreImplIk S.N_send_tot kIdx (some uSk) (some sk) S P (.genSPK u j)).run hst
      have hm1Eq : (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.genSPK u j)).run hst = m1 := by
        rw [pqxdhKeyInd1KeyFgPreImpl_non_initPrin_eq_fgPreIk kIdx (some sk) uSk sk P _
          (fun _ h => by cases h)]
      rw [hm1Eq, evalDist_bind_withSupp_eq m1 k1, hStepR,
        sig1KeyStep_delegated_run P P.isValidDhTriple kIdx uSk sk b.q_total (.genSPK u j) st st0 msgs
          hClear (hPk.trans hSigPk) (fun _ h => by cases h) (fun _ h => by cases h)
          (fun _ _ h => by injection h with h1 _; rw [← h1]; exact huF),
        bind_map_left]
      refine fgStepCoupling_dh2 S b P hP S.N_send_tot kIdx uSk sk huSk hvSk (.genSPK u j) rem
        hst st0 hDead2 hInv (withSupp m1 k1)
        (fun p => k2 ((p.1, { st with fg := clearFgTargetSign kIdx p.2 }), msgs))
        (fun r hst' st0' hDead2' hInv' => ?_) (fun r hst' hDead2' => ?_)
      · unfold withSupp
        split_ifs with hx
        · have hxFg : (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P (.genSPK u j)).run hst) := by
            rwa [← hm1Eq] at hx
          have hb := mem_support_pqxdhKeyIndFgImpl_base P (.genSPK u j) hst (r, hst') hxFg
          have hDead1' : deadDh1 kIdx hst' = false := by
            rw [← deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst'
              hInv'.2.2.2.2.2.2.1 hInv'.2.2.2.2.2.1.2.2.2.1]
            exact hDead2'
          have hSpkCases := (keyIndSigLens S).mem_support_realGenSPK P u j hst.base (r, hst'.base) hb
          rcases hSpkCases with hNone | ⟨_, idx0, uEntry0, bEntry0, bundleOut0, _, hSome⟩
          · have hBaseEq' : hst'.base = hst.base := (Prod.mk.inj hNone).2
            apply hCont r hst' { st with fg := clearFgTargetSign kIdx st0' } msgs
            refine ⟨hFgNone, hParty, hPk, ⟨st0', rfl, hInv'⟩, hDead1', ?_, ?_, ?_, ?_⟩ <;>
              rw [hBaseEq'] <;> assumption
          · have hBaseEq' : hst'.base =
                { hst.base with spkBundles := ((u.val, j.val), bEntry0) :: hst.base.spkBundles } :=
              (Prod.mk.inj hSome).2
            apply hCont r hst' { st with fg := clearFgTargetSign kIdx st0' } msgs
            refine ⟨hFgNone, hParty, hPk, ⟨st0', rfl, hInv'⟩, hDead1', ?_, ?_, ?_, ?_⟩
            · rw [hBaseEq']; exact hClean
            · rw [hBaseEq']; dsimp only
              rw [bundleSignedMessages_cons_of_ne kIdx u.val j.val bEntry0 _ huF]
              exact hBud
            · intro m hm
              rw [hBaseEq']; dsimp only
              rw [bundleSignedMessages_cons_of_ne kIdx u.val j.val bEntry0 _ huF]
              exact hMsgs m hm
            · rw [hBaseEq']; exact hSign
        · simp
      · unfold withSupp
        split_ifs with hx
        · exfalso
          have hxFg : (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P (.genSPK u j)).run hst) := by
            rwa [← hm1Eq] at hx
          have hb := mem_support_pqxdhKeyIndFgImpl_base P (.genSPK u j) hst (r, hst') hxFg
          have hPrinEq : hst'.base.principals = hst.base.principals := by
            rcases (keyIndSigLens S).mem_support_realGenSPK P u j hst.base (r, hst'.base) hb with
              hNone | ⟨_, _, _, _, _, _, hSome⟩
            · exact congrArg KeyIndState.principals (Prod.mk.inj hNone).2
            · dsimp only [keyIndSigLens] at hSome
              rw [(Prod.mk.inj hSome).2]
          have hSessEq : hst'.base.sessions = hst.base.sessions := by
            rcases (keyIndSigLens S).mem_support_realGenSPK P u j hst.base (r, hst'.base) hb with
              hNone | ⟨_, _, _, _, _, _, hSome⟩
            · exact congrArg KeyIndState.sessions (Prod.mk.inj hNone).2
            · dsimp only [keyIndSigLens] at hSome
              rw [(Prod.mk.inj hSome).2]
          rw [deadDh2_eq_of_prin_sess P S.N_send_tot kIdx (P.x25519Base sk)
            hPrinEq (by rw [hSessEq]), hDead2] at hDead2'
          cases hDead2'
        · simp
  | corruptIK u =>
    have hRel0 := hRel
    rcases hRel with ⟨hFgNone, hParty, hPk, ⟨st0, hClear, hInv⟩, hDead1, hClean, hBud, hMsgs, hSign⟩
    by_cases hu : (u.val == kIdx) = true
    · have huEq : u.val = kIdx := beq_iff_eq.mp hu
      cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        have hFindSim : st.fg.base.principals.find? (fun (idx, _) => idx == u.val) = none := by
          rw [hClear]; dsimp only [clearFgTargetSign]
          rw [find?_idx_clearPrincipalsTargetSign, hInv.1]
          dsimp only [eraseStateFgIk]
          rw [find?_idx_erasePrincipalsFg, hFP]
          rfl
        have hL : (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.corruptIK u)).run hst =
            pure (.noneResp, hst) := by
          unfold pqxdhKeyInd1KeyFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl
          simp [StateT.run_bind, StateT.run_get, hFP]
        have hR : (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
            (sig1KeyStep S b.q_total (.corruptIK u) st)).run msgs =
            pure ((.noneResp, st), msgs) := by
          unfold sig1KeyStep
          simp only [hFgNone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            simulateQ_bind, StateT.run_bind, simulateQ_embedGdhSigDdh_run,
            simulateQ_gapDhFullImpl_fgKeyIndStep, fgKeyIndStepPure,
            simulateQ_pure, StateT.run_pure, bind_map_left, hFindSim, pure_bind]
          cases st; simp_all
        rw [hL, hR, pure_bind, pure_bind]
        exact hCont .noneResp hst st msgs (sig1KeyRel_weaken_rem hRel0)
      | some p =>
        rcases p with ⟨u0, uEntry⟩
        have hZero :
            𝒟[(pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.corruptIK u)).run hst >>= k1] {true} = 0 := by
          refine evalDist_bind_true_eq_zero_of_support _ _ (fun ⟨r, hst'⟩ hx => ?_)
          have hb := mem_support_pqxdhKeyIndFgImpl_base P (.corruptIK u) hst (r, hst') hx
          rcases (keyIndSigLens S).mem_support_realCorruptIK u hst.base (r, hst'.base) hb with
            ⟨hNone, _⟩ | ⟨_, _, _, hSome⟩
          · dsimp only [keyIndSigLens] at hNone
            rw [hFP] at hNone; cases hNone
          · dsimp only [keyIndSigLens] at hSome
            let mapPrins := hst.base.principals.map (fun (i, e) =>
              if i == u.val then (i, { e with corrupted := true }) else (i, e))
            have hBaseEq' : hst'.base = { hst.base with principals := mapPrins } :=
              (Prod.mk.inj hSome).2
            have hekMem : (kIdx, uEntry) ∈ hst.base.principals := by
              have hu0U : u0 = u.val :=
                beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hFP)
              rw [← huEq, ← hu0U]
              exact List.mem_of_find?_eq_some hFP
            apply hSafeCont r hst'
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [hBaseEq']
              exact validPrincipals_corrupt S u.val hst.base.principals hInv.2.2.2.2.2.1.1
            · rw [hBaseEq']
              exact ⟨{ uEntry with corrupted := true },
                (mem_corrupt_map u.val kIdx _ hst.base.principals).mpr
                  ⟨uEntry, hekMem, by simp [huEq]⟩⟩
            · intro e he
              rw [hBaseEq'] at he
              dsimp only [mapPrins] at he
              rcases (mem_corrupt_map u.val kIdx e hst.base.principals).mp he with ⟨e0, _, rfl⟩
              simp [huEq]
            · rw [hBaseEq']
              exact cleanPeers_corrupt S P kIdx u.val hst.base.principals
                (badPeersKeyInd hst.base) hClean
        rw [hZero]
        exact zero_le
    · have huF : (u.val == kIdx) = false := Bool.eq_false_iff.mpr hu
      have hSigPk : P.sigPkGen sk = P.x25519Base sk :=
        congrFun hP.toWellFormedPrimitivesδ.sigPkGen_eq_x25519Base sk
      have hDead2 : deadDh2 P S.N_send_tot kIdx (P.x25519Base sk) hst = false := by
        rw [deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst
          hInv.2.2.2.2.2.2.1 hInv.2.2.2.2.2.1.2.2.2.1]
        exact hDead1
      have hStepR : sig1KeyStep S b.q_total (.corruptIK u) st =
          (do
            let (out, fg') ← embedGdhSigDdh
              (fgKeyIndStep false S.N_send_tot S.N_spk_tot S b.q_total [] st.targetPk
                (.corruptIK u) st.fg)
            return (out, { st with fg := fg' })) := by
        unfold sig1KeyStep; simp [hFgNone]
      let m1 := (pqxdhKeyIndFgPreImplIk S.N_send_tot kIdx (some uSk) (some sk) S P (.corruptIK u)).run hst
      have hm1Eq : (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.corruptIK u)).run hst = m1 := by
        rw [pqxdhKeyInd1KeyFgPreImpl_non_initPrin_eq_fgPreIk kIdx (some sk) uSk sk P _
          (fun _ h => by cases h)]
      rw [hm1Eq, evalDist_bind_withSupp_eq m1 k1, hStepR,
        sig1KeyStep_delegated_run P P.isValidDhTriple kIdx uSk sk b.q_total (.corruptIK u) st st0 msgs
          hClear (hPk.trans hSigPk) (fun _ h => by cases h)
          (fun _ h => by injection h with h1; rw [← h1]; exact huF)
          (fun _ _ h => by cases h),
        bind_map_left]
      refine fgStepCoupling_dh2 S b P hP S.N_send_tot kIdx uSk sk huSk hvSk (.corruptIK u) rem
        hst st0 hDead2 hInv (withSupp m1 k1)
        (fun p => k2 ((p.1, { st with fg := clearFgTargetSign kIdx p.2 }), msgs))
        (fun r hst' st0' hDead2' hInv' => ?_) (fun r hst' hDead2' => ?_)
      · unfold withSupp
        split_ifs with hx
        · have hxFg : (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P (.corruptIK u)).run hst) := by
            rwa [← hm1Eq] at hx
          have hb := mem_support_pqxdhKeyIndFgImpl_base P (.corruptIK u) hst (r, hst') hxFg
          have hDead1' : deadDh1 kIdx hst' = false := by
            rw [← deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst'
              hInv'.2.2.2.2.2.2.1 hInv'.2.2.2.2.2.1.2.2.2.1]
            exact hDead2'
          rcases (keyIndSigLens S).mem_support_realCorruptIK u hst.base (r, hst'.base) hb with
            ⟨_, hNone⟩ | ⟨_, _, _, hSome⟩
          · have hBaseEq' : hst'.base = hst.base := (Prod.mk.inj hNone).2
            apply hCont r hst' { st with fg := clearFgTargetSign kIdx st0' } msgs
            refine ⟨hFgNone, hParty, hPk, ⟨st0', rfl, hInv'⟩, hDead1', ?_, ?_, ?_, ?_⟩ <;>
              rw [hBaseEq'] <;> assumption
          · dsimp only [keyIndSigLens] at hSome
            let mapPrins := hst.base.principals.map (fun (i, e) =>
              if i == u.val then (i, { e with corrupted := true }) else (i, e))
            have hBaseEq' : hst'.base = { hst.base with principals := mapPrins } :=
              (Prod.mk.inj hSome).2
            apply hCont r hst' { st with fg := clearFgTargetSign kIdx st0' } msgs
            refine ⟨hFgNone, hParty, hPk, ⟨st0', rfl, hInv'⟩, hDead1', ?_, ?_, ?_, ?_⟩
            · rw [hBaseEq']
              exact cleanPeers_corrupt S P kIdx u.val hst.base.principals
                (badPeersKeyInd hst.base) hClean
            · rw [hBaseEq']; exact hBud
            · rw [hBaseEq']; exact hMsgs
            · intro kv hkv hk
              rw [hBaseEq'] at hkv; dsimp only [mapPrins] at hkv
              rcases List.mem_map.mp hkv with ⟨⟨idx0, e0⟩, hMem0, hEq0⟩
              by_cases hi : (idx0 == u.val) = true
              · simp only [hi, ↓reduceIte] at hEq0
                subst hEq0
                have hku : (idx0 == kIdx) = false := by
                  rw [beq_iff_eq.mp hi]; exact huF
                rw [hku] at hk; cases hk
              · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hEq0
                subst hEq0
                exact hSign (idx0, e0) hMem0 hk
        · simp
      · unfold withSupp
        split_ifs with hx
        · exfalso
          have hxFg : (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P (.corruptIK u)).run hst) := by
            rwa [← hm1Eq] at hx
          have hb := mem_support_pqxdhKeyIndFgImpl_base P (.corruptIK u) hst (r, hst') hxFg
          rcases (keyIndSigLens S).mem_support_realCorruptIK u hst.base (r, hst'.base) hb with
            ⟨_, hNone⟩ | ⟨_, _, _, hSome⟩
          · have hBaseEq' : hst'.base = hst.base := (Prod.mk.inj hNone).2
            have hP' : hst'.base.principals = hst.base.principals :=
              congrArg KeyIndState.principals hBaseEq'
            have hS' : hst'.base.sessions = hst.base.sessions :=
              congrArg KeyIndState.sessions hBaseEq'
            rw [deadDh2_eq_of_prin_sess P S.N_send_tot kIdx (P.x25519Base sk)
              hP' (by rw [hS']), hDead2] at hDead2'
            cases hDead2'
          · dsimp only [keyIndSigLens] at hSome
            let mapPrins := hst.base.principals.map (fun (i, e) =>
              if i == u.val then (i, { e with corrupted := true }) else (i, e))
            have hBaseEq' : hst'.base = { hst.base with principals := mapPrins } :=
              (Prod.mk.inj hSome).2
            have hEqD : deadDh2 P S.N_send_tot kIdx (P.x25519Base sk) hst' =
                deadDh2 P S.N_send_tot kIdx (P.x25519Base sk) hst := by
              rw [deadDh2_eq_of_prin_sess P S.N_send_tot kIdx (P.x25519Base sk)
                (hst1 := { hst with base := hst'.base }) (hst2 := hst') rfl rfl]
              simpa [hBaseEq', mapPrins] using
                deadDh2_map_corrupted_of_ne P S.N_send_tot kIdx u.val (P.x25519Base sk) huF hst
            rw [hEqD, hDead2] at hDead2'
            cases hDead2'
        · simp
  | initiateOPK u i bundle =>
    rcases hRel with ⟨hFgNone, hParty, hPk, ⟨st0, hClear, hInv⟩, hDead1, hClean, hBud, hMsgs, hSign⟩
    have hSigPk : P.sigPkGen sk = P.x25519Base sk :=
      congrFun hP.toWellFormedPrimitivesδ.sigPkGen_eq_x25519Base sk
    have hPrinLen : st.fg.base.principals.length ≤ S.N_dh := by
      rw [hClear]; dsimp only [clearFgTargetSign]
      rw [length_clearPrincipalsTargetSign, hInv.1]
      dsimp only [eraseStateFgIk, erasePrincipalsFg]
      rw [List.length_map]
      exact (validKeyIndEc_lengths_le_fg S P hst.base hInv.2.2.2.2.2.1).1
    have hSpkSimEq : st.fg.base.spkBundles = hst.base.spkBundles := by
      rw [hClear]; dsimp only [clearFgTargetSign]; rw [hInv.1]; rfl
    have hExtEq :
        extractBundleForgery P kIdx (P.sigPkGen sk)
          st.fg.base.principals st.fg.base.spkBundles bundle none =
        extractBundleForgery P kIdx (P.sigPkGen sk)
          hst.base.principals hst.base.spkBundles bundle none := by
      rw [hSpkSimEq, hClear]; dsimp only [clearFgTargetSign]
      rw [hInv.1]; dsimp only [eraseStateFgIk]
      exact extractBundleForgery_clear_erase P kIdx (P.sigPkGen sk)
        hst.base.principals hst.base.spkBundles bundle
    have hStepUnfold :
        (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
          (sig1KeyStep S b.q_total (.initiateOPK u i bundle) st)).run msgs =
        (let forgery' := extractBundleForgery P kIdx (P.sigPkGen sk)
            hst.base.principals hst.base.spkBundles bundle none
         if forgery'.isSome then
           pure ((.noneResp, { st with forgery := forgery' }), msgs)
         else
           (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
             (do
               let (out, fg') ← embedGdhSigDdh
                 (fgKeyIndStep false S.N_send_tot S.N_spk_tot S b.q_total [] st.targetPk
                   (.initiateOPK u i bundle) st.fg)
               return (out, { st with fg := fg' }))).run msgs) := by
      unfold sig1KeyStep
      simp only [hFgNone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hParty, hPk,
        simulateQ_bind, StateT.run_bind, simulateQ_embedPrim_sigDdh_run,
        simulateQ_extractBundleForgeryPrim S P kIdx (P.sigPkGen sk)
          st.fg.base.principals st.fg.base.spkBundles bundle none hPrinLen,
        hExtEq, map_pure, pure_bind]
      cases (extractBundleForgery P kIdx (P.sigPkGen sk)
        hst.base.principals hst.base.spkBundles bundle none).isSome <;> simp
    rw [hStepUnfold]
    cases hExt : extractBundleForgery P kIdx (P.sigPkGen sk)
        hst.base.principals hst.base.spkBundles bundle none with
    | some ms =>
      rcases ms with ⟨mStar, sigStar⟩
      simp only [Option.isSome_some, ↓reduceIte, pure_bind]
      have hValid := extractBundleForgery_valid_euf_cma P kIdx (P.sigPkGen sk)
        hst.base.principals hst.base.spkBundles bundle hExt
      have hNotInMsgs : mStar ∉ msgs := fun hm => hValid.2.2 (hMsgs mStar hm)
      have hWon : Sig1KeyWon P sk { st with forgery := some (mStar, sigStar) } msgs :=
        ⟨mStar, sigStar, rfl, hValid.2.1, hNotInMsgs⟩
      calc 𝒟[(pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.initiateOPK u i bundle)).run hst >>= k1] {true}
          ≤ 1 := prob_le_one
        _ ≤ 𝒟[k2 ((.noneResp, { st with forgery := some (mStar, sigStar) }), msgs)] {true} :=
            hWonCont .noneResp _ msgs hWon
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      have hDead2 : deadDh2 P S.N_send_tot kIdx (P.x25519Base sk) hst = false := by
        rw [deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst
          hInv.2.2.2.2.2.2.1 hInv.2.2.2.2.2.1.2.2.2.1]
        exact hDead1
      let m1 := (pqxdhKeyIndFgPreImplIk S.N_send_tot kIdx (some uSk) (some sk) S P
        (.initiateOPK u i bundle)).run hst
      have hm1Eq :
          (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.initiateOPK u i bundle)).run hst = m1 := by
        rw [pqxdhKeyInd1KeyFgPreImpl_non_initPrin_eq_fgPreIk kIdx (some sk) uSk sk P _
          (fun _ h => by cases h)]
      rw [hm1Eq, evalDist_bind_withSupp_eq m1 k1,
        sig1KeyStep_delegated_run P P.isValidDhTriple kIdx uSk sk b.q_total
          (.initiateOPK u i bundle) st st0 msgs hClear (hPk.trans hSigPk)
          (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h),
        bind_map_left]
      refine fgStepCoupling_dh2 S b P hP S.N_send_tot kIdx uSk sk huSk hvSk
        (.initiateOPK u i bundle) rem hst st0 hDead2 hInv (withSupp m1 k1)
        (fun p => k2 ((p.1, { st with fg := clearFgTargetSign kIdx p.2 }), msgs))
        (fun r hst' st0' hDead2' hInv' => ?_) (fun r hst' hDead2' => ?_)
      · unfold withSupp
        split_ifs with hx
        · have hxFg :
              (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P (.initiateOPK u i bundle)).run hst) := by
            rwa [← hm1Eq] at hx
          have hb := mem_support_pqxdhKeyIndFgImpl_base P (.initiateOPK u i bundle) hst (r, hst') hxFg
          have hPost := pqxdhKeyIndImpl_initiateOPK_pres_raw S P u i bundle hst.base (r, hst'.base) hb
          exact hCont r hst' { st with fg := clearFgTargetSign kIdx st0' } msgs
            (sig1Key_step_initiate_post hFgNone hParty hPk hInv.2.2.2.2.2.1.1 hDead1 hClean
              hBud hMsgs hSign hExt hPost hDead2' hInv')
        · simp
      · unfold withSupp
        split_ifs with hx
        · exfalso
          have hxFg :
              (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P (.initiateOPK u i bundle)).run hst) := by
            rwa [← hm1Eq] at hx
          have hb := mem_support_pqxdhKeyIndFgImpl_base P (.initiateOPK u i bundle) hst (r, hst') hxFg
          have hPost := pqxdhKeyIndImpl_initiateOPK_pres_raw S P u i bundle hst.base (r, hst'.base) hb
          have hValidEc' := pqxdhKeyIndImpl_validKeyIndEc_step true S P (.initiateOPK u i bundle)
            hst.base ⟨hInv.2.2.2.2.2.1.1, hInv.2.2.2.2.2.1.2.1, hInv.2.2.2.2.2.1.2.2.1,
              hInv.2.2.2.2.2.1.2.2.2.1⟩ (r, hst'.base) hb
          have hTgtV' : prinTargetIsV kIdx (P.x25519Base sk) hst' = true := by
            unfold prinTargetIsV; rw [hPost.1]; exact hInv.2.2.2.2.2.2.1
          rw [deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst' hTgtV'
            hValidEc'.2.2.2, deadDh1_eq_of_principals kIdx hPost.1, hDead1] at hDead2'
          cases hDead2'
        · simp
  | initiateNoOPK u i bundle =>
    rcases hRel with ⟨hFgNone, hParty, hPk, ⟨st0, hClear, hInv⟩, hDead1, hClean, hBud, hMsgs, hSign⟩
    have hSigPk : P.sigPkGen sk = P.x25519Base sk :=
      congrFun hP.toWellFormedPrimitivesδ.sigPkGen_eq_x25519Base sk
    have hPrinLen : st.fg.base.principals.length ≤ S.N_dh := by
      rw [hClear]; dsimp only [clearFgTargetSign]
      rw [length_clearPrincipalsTargetSign, hInv.1]
      dsimp only [eraseStateFgIk, erasePrincipalsFg]
      rw [List.length_map]
      exact (validKeyIndEc_lengths_le_fg S P hst.base hInv.2.2.2.2.2.1).1
    have hSpkSimEq : st.fg.base.spkBundles = hst.base.spkBundles := by
      rw [hClear]; dsimp only [clearFgTargetSign]; rw [hInv.1]; rfl
    have hExtEq :
        extractBundleForgery P kIdx (P.sigPkGen sk)
          st.fg.base.principals st.fg.base.spkBundles bundle none =
        extractBundleForgery P kIdx (P.sigPkGen sk)
          hst.base.principals hst.base.spkBundles bundle none := by
      rw [hSpkSimEq, hClear]; dsimp only [clearFgTargetSign]
      rw [hInv.1]; dsimp only [eraseStateFgIk]
      exact extractBundleForgery_clear_erase P kIdx (P.sigPkGen sk)
        hst.base.principals hst.base.spkBundles bundle
    have hStepUnfold :
        (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
          (sig1KeyStep S b.q_total (.initiateNoOPK u i bundle) st)).run msgs =
        (let forgery' := extractBundleForgery P kIdx (P.sigPkGen sk)
            hst.base.principals hst.base.spkBundles bundle none
         if forgery'.isSome then
           pure ((.noneResp, { st with forgery := forgery' }), msgs)
         else
           (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
             (do
               let (out, fg') ← embedGdhSigDdh
                 (fgKeyIndStep false S.N_send_tot S.N_spk_tot S b.q_total [] st.targetPk
                   (.initiateNoOPK u i bundle) st.fg)
               return (out, { st with fg := fg' }))).run msgs) := by
      unfold sig1KeyStep
      simp only [hFgNone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hParty, hPk,
        simulateQ_bind, StateT.run_bind, simulateQ_embedPrim_sigDdh_run,
        simulateQ_extractBundleForgeryPrim S P kIdx (P.sigPkGen sk)
          st.fg.base.principals st.fg.base.spkBundles bundle none hPrinLen,
        hExtEq, map_pure, pure_bind]
      cases (extractBundleForgery P kIdx (P.sigPkGen sk)
        hst.base.principals hst.base.spkBundles bundle none).isSome <;> simp
    rw [hStepUnfold]
    cases hExt : extractBundleForgery P kIdx (P.sigPkGen sk)
        hst.base.principals hst.base.spkBundles bundle none with
    | some ms =>
      rcases ms with ⟨mStar, sigStar⟩
      simp only [Option.isSome_some, ↓reduceIte, pure_bind]
      have hValid := extractBundleForgery_valid_euf_cma P kIdx (P.sigPkGen sk)
        hst.base.principals hst.base.spkBundles bundle hExt
      have hNotInMsgs : mStar ∉ msgs := fun hm => hValid.2.2 (hMsgs mStar hm)
      have hWon : Sig1KeyWon P sk { st with forgery := some (mStar, sigStar) } msgs :=
        ⟨mStar, sigStar, rfl, hValid.2.1, hNotInMsgs⟩
      calc 𝒟[(pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.initiateNoOPK u i bundle)).run hst >>= k1] {true}
          ≤ 1 := prob_le_one
        _ ≤ 𝒟[k2 ((.noneResp, { st with forgery := some (mStar, sigStar) }), msgs)] {true} :=
            hWonCont .noneResp _ msgs hWon
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      have hDead2 : deadDh2 P S.N_send_tot kIdx (P.x25519Base sk) hst = false := by
        rw [deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst
          hInv.2.2.2.2.2.2.1 hInv.2.2.2.2.2.1.2.2.2.1]
        exact hDead1
      let m1 := (pqxdhKeyIndFgPreImplIk S.N_send_tot kIdx (some uSk) (some sk) S P
        (.initiateNoOPK u i bundle)).run hst
      have hm1Eq :
          (pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P (.initiateNoOPK u i bundle)).run hst = m1 := by
        rw [pqxdhKeyInd1KeyFgPreImpl_non_initPrin_eq_fgPreIk kIdx (some sk) uSk sk P _
          (fun _ h => by cases h)]
      rw [hm1Eq, evalDist_bind_withSupp_eq m1 k1,
        sig1KeyStep_delegated_run P P.isValidDhTriple kIdx uSk sk b.q_total
          (.initiateNoOPK u i bundle) st st0 msgs hClear (hPk.trans hSigPk)
          (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h),
        bind_map_left]
      refine fgStepCoupling_dh2 S b P hP S.N_send_tot kIdx uSk sk huSk hvSk
        (.initiateNoOPK u i bundle) rem hst st0 hDead2 hInv (withSupp m1 k1)
        (fun p => k2 ((p.1, { st with fg := clearFgTargetSign kIdx p.2 }), msgs))
        (fun r hst' st0' hDead2' hInv' => ?_) (fun r hst' hDead2' => ?_)
      · unfold withSupp
        split_ifs with hx
        · have hxFg :
              (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P (.initiateNoOPK u i bundle)).run hst) := by
            rwa [← hm1Eq] at hx
          have hb := mem_support_pqxdhKeyIndFgImpl_base P (.initiateNoOPK u i bundle) hst (r, hst') hxFg
          have hPost := pqxdhKeyIndImpl_initiateNoOPK_pres_raw S P u i bundle hst.base (r, hst'.base) hb
          exact hCont r hst' { st with fg := clearFgTargetSign kIdx st0' } msgs
            (sig1Key_step_initiate_post hFgNone hParty hPk hInv.2.2.2.2.2.1.1 hDead1 hClean
              hBud hMsgs hSign hExt hPost hDead2' hInv')
        · simp
      · unfold withSupp
        split_ifs with hx
        · exfalso
          have hxFg :
              (r, hst') ∈ support ((pqxdhKeyIndFgImpl S P (.initiateNoOPK u i bundle)).run hst) := by
            rwa [← hm1Eq] at hx
          have hb := mem_support_pqxdhKeyIndFgImpl_base P (.initiateNoOPK u i bundle) hst (r, hst') hxFg
          have hPost := pqxdhKeyIndImpl_initiateNoOPK_pres_raw S P u i bundle hst.base (r, hst'.base) hb
          have hValidEc' := pqxdhKeyIndImpl_validKeyIndEc_step true S P (.initiateNoOPK u i bundle)
            hst.base ⟨hInv.2.2.2.2.2.1.1, hInv.2.2.2.2.2.1.2.1, hInv.2.2.2.2.2.1.2.2.1,
              hInv.2.2.2.2.2.1.2.2.2.1⟩ (r, hst'.base) hb
          have hTgtV' : prinTargetIsV kIdx (P.x25519Base sk) hst' = true := by
            unfold prinTargetIsV; rw [hPost.1]; exact hInv.2.2.2.2.2.2.1
          rw [deadDh2_N_send_tot_eq_deadDh1 P kIdx (P.x25519Base sk) hst' hTgtV'
            hValidEc'.2.2.2, deadDh1_eq_of_principals kIdx hPost.1, hDead1] at hDead2'
          cases hDead2'
        · simp
  | genOPK u j o =>
    exact sig1Key_step_other S b P hP kIdx uSk sk huSk hvSk (.genOPK u j o) rem
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hst st msgs hRel k1 k2 hCont
  | acceptOPK k j o hdr =>
    exact sig1Key_step_other S b P hP kIdx uSk sk huSk hvSk (.acceptOPK k j o hdr) rem
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hst st msgs hRel k1 k2 hCont
  | acceptNoOPK k j l hdr =>
    exact sig1Key_step_other S b P hP kIdx uSk sk huSk hvSk (.acceptNoOPK k j l hdr) rem
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hst st msgs hRel k1 k2 hCont
  | testSession sid =>
    exact sig1Key_step_other S b P hP kIdx uSk sk huSk hvSk (.testSession sid) rem
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hst st msgs hRel k1 k2 hCont
  | revealSessionKey sid =>
    exact sig1Key_step_other S b P hP kIdx uSk sk huSk hvSk (.revealSessionKey sid) rem
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hst st msgs hRel k1 k2 hCont
  | roQuery secrets =>
    exact sig1Key_step_other S b P hP kIdx uSk sk huSk hvSk (.roQuery secrets) rem
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hst st msgs hRel k1 k2 hCont
  | revealDhSecrets =>
    exact sig1Key_step_other S b P hP kIdx uSk sk huSk hvSk .revealDhSecrets rem
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hst st msgs hRel k1 k2 hCont
  | registerKey skAdv =>
    exact sig1Key_step_other S b P hP kIdx uSk sk huSk hvSk (.registerKey skAdv) rem
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hst st msgs hRel k1 k2 hCont
  | revealSpkSk u j =>
    exact sig1Key_step_other S b P hP kIdx uSk sk huSk hvSk (.revealSpkSk u j) rem
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hst st msgs hRel k1 k2 hCont

/-! ## Full simulation induction and per-principal `GapSigEufCma` bound -/

theorem evalDist_simulateQ_sig1Key_le {S : Setup} {α : Type}
    (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (kIdx : ℕ) (uSk sk : Bytes) (huSk : uSk.length = 32) (hvSk : sk.length = 32)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (rem : ℕ)
    (hQb : IsQueryBoundP oa (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) rem)
    (hst : KeyIndFgCutoffState S) (st : Sig1KeySimState S) (msgs : List Bytes)
    (hRel : Sig1KeyRel S b P hP kIdx uSk sk huSk hvSk rem hst st msgs) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P) oa).run hst >>=
      fun (_, finalHst) => pure (hasBadSigKeyIndAt S P kIdx finalHst.base)] {true} ≤
    𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
        (runWithSigDdhStep (sig1KeyStep S b.q_total) oa st)).run msgs >>=
      fun res => pure (sig1KeyWinBool P sk res)] {true} := by
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndFgCutoffState S) ProbComp) +
    pqxdhKeyInd1KeyFgPreImpl kIdx (some sk) S P
  induction oa using OracleComp.inductionOn generalizing rem hst st msgs with
  | pure x =>
    have hBadF : hasBadSigKeyIndAt S P kIdx hst.base = false :=
      any_peerPartyIdx_eq_false_of_cleanPeers S P kIdx hst.base.principals
        (badPeersKeyInd hst.base) hRel.2.2.2.2.2.1
    simp [StateT.run_pure, hBadF]
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hQb
    cases q with
    | inl n =>
      rcases hQb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      rw [runWithSigDdhStep_query_inl]
      have hqR :
          (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
            (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl (Sum.inl n))) >>=
              fun u => runWithSigDdhStep (sig1KeyStep S b.q_total) (k u) st)).run msgs =
          (liftM (unifSpec.query n) >>= fun u =>
            (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
              (runWithSigDdhStep (sig1KeyStep S b.q_total) (k u) st)).run msgs) := by
        simp [gapSigEufCmaFullImpl, primBaseImpl, QueryImpl.liftTarget,
          simulateQ_bind, StateT.run_bind, StateT.run_monadLift]
      simp only [simulateQ_run_query_inl, hqR, bind_assoc]
      exact evalDist_bind_true_mono_of_support _ _ _ (fun u _ =>
        ih u rem (h_cont u) hst st msgs hRel)
    | inr gq =>
      rcases hQb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases rem with
        | zero => omega
        | succ rem' =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          rw [simulateQ_run_query_inr, runWithSigDdhStep_query_inr]
          simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
          exact sig1Key_step_coupling S b P hP kIdx uSk sk huSk hvSk gq rem' hst st msgs hRel
            (fun y => (simulateQ impl (k y.1)).run y.2 >>=
              fun (_, finalHst) => pure (hasBadSigKeyIndAt S P kIdx finalHst.base))
            (fun z => (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
                (runWithSigDdhStep (sig1KeyStep S b.q_total) (k z.1.1) z.1.2)).run z.2 >>=
              fun res => pure (sig1KeyWinBool P sk res))
            (fun r hst' hSafe => evalDist_safe_1Key_eq_zero P kIdx (some sk) (k r) hst' hSafe)
            (fun r st' msgs' hWon =>
              one_le_evalDist_sig1KeyWon P P.isValidDhTriple sk b.q_total (k r) st' msgs' hWon)
            (fun r hst' st' msgs' hRel' => ih r rem' (h_cont r) hst' st' msgs' hRel')

noncomputable def badSigProbKeyInd1KeyAt (S : Setup) (P : Primitives) (kIdx : ℕ)
    (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyInd1KeySim S P A >>= fun (_, _, finalSt) =>
    pure (hasBadSigKeyIndAt S P kIdx finalSt)] {true}).toReal

/-- Per-principal `GapSigEufCma` bound for one-key `KeyInd`. -/
theorem badSigProbKeyInd1KeyAt_le_gapSigEufCma (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (kIdx : ℕ)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    badSigProbKeyInd1KeyAt S P kIdx A.1 ≤
      GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyAt kIdx S b A) := by
  unfold badSigProbKeyInd1KeyAt GapSigEufCmaReal GapSigEufCma
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyInd1KeySim_eq_preSample kIdx P A.1 (hasBadSigKeyIndAt S P kIdx)]
  rw [gapSigEufCmaExp_eq_fullImpl]
  unfold sigReductionKeyInd1KeyAt sigReductionKeyInd1KeyRunAt
  dsimp only
  let uSk : Bytes := List.replicate 32 0
  have huSk : uSk.length = 32 := by simp [uSk]
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.keyInd_total A.2
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun sk hSk => ?_)
  have hvSk : sk.length = 32 := length_of_mem_support_sampleScalar32 hSk
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_unifSigDdh_run,
    simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_simulateQ_sig1Key_le b P hP kIdx uSk sk huSk hvSk A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (Sig1KeySimState.empty S secb kIdx (P.sigPkGen sk)) []
    (sig1KeyRel_empty S b P hP kIdx uSk sk huSk hvSk secb)

/-! ## Union bound and one-key `G0 → G2` hops -/

noncomputable def badSigNoCollProbKeyInd1Key (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyInd1KeySim S P A >>= fun (_, _, finalSt) =>
    pure (hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals)] {true}).toReal

theorem badSigNoCollProbKeyInd1Key_le_sum (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) :
    badSigNoCollProbKeyInd1Key S P A ≤
      ∑ kIdx ∈ Finset.range S.N_id, badSigProbKeyInd1KeyAt S P kIdx A := by
  unfold badSigNoCollProbKeyInd1Key badSigProbKeyInd1KeyAt
  have hEq :
      (runKeyInd1KeySim S P A >>= fun (_, _, finalSt) =>
        pure (hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals)) =
      (runKeyInd1KeySim S P A >>= fun (_, _, finalSt) =>
        pure ((List.range S.N_id).any (fun kIdx => hasBadSigKeyIndAt S P kIdx finalSt))) := by
    congr 1; ext ⟨_, _, finalSt⟩
    dsimp only
    rw [hasBadSigKeyInd_eq_any_range S P finalSt]
  rw [hEq]
  exact toReal_any_range_le_sum (runKeyInd1KeySim S P A) S.N_id
    (fun kIdx (_, _, finalSt) => hasBadSigKeyIndAt S P kIdx finalSt)

theorem mul_gapSigEufCma_sigReductionKeyInd1Key_eq_sum (S : Setup) (b : QueryBudget)
    (P : Primitives) (A : BoundedAdv (KeyIndAdversary S) b) :
    (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A) =
      ∑ kIdx ∈ Finset.range S.N_id,
        GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyAt kIdx S b A) := by
  have hSwap :
      𝒟[gapSigEufCmaExp P P.isValidDhTriple (sigReductionKeyInd1Key S b A)] =
      𝒟[RoKem.sampleIndexRange S.N_id >>= fun kIdx =>
        gapSigEufCmaExp P P.isValidDhTriple (sigReductionKeyInd1KeyAt kIdx S b A)] := by
    simp only [gapSigEufCmaExp_eq_fullImpl]
    unfold sigReductionKeyInd1Key sigReductionKeyInd1KeyAt
    dsimp only
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_unifSigDdh_run,
      bind_map_left, bind_assoc]
    rw [OracleComp.evalDist_bind_bind_swap]
  unfold GapSigEufCmaReal GapSigEufCma
  rw [hSwap]
  exact _root_.Proofs.SignalPqxdh.Security.mul_toReal_sampleIndexRange_bind_eq_sum S.N_id
    (fun kIdx => gapSigEufCmaExp P P.isValidDhTriple (sigReductionKeyInd1KeyAt kIdx S b A))

theorem badSigNoCollProbKeyInd1Key_le_gapSigEufCma (S : Setup) (b : QueryBudget)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    badSigNoCollProbKeyInd1Key S P A.1 ≤
      (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A) := by
  calc badSigNoCollProbKeyInd1Key S P A.1
      ≤ ∑ kIdx ∈ Finset.range S.N_id, badSigProbKeyInd1KeyAt S P kIdx A.1 :=
        badSigNoCollProbKeyInd1Key_le_sum S P A.1
    _ ≤ ∑ kIdx ∈ Finset.range S.N_id,
          GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyAt kIdx S b A) :=
        Finset.sum_le_sum (fun kIdx _ =>
          badSigProbKeyInd1KeyAt_le_gapSigEufCma S b P hP kIdx A)
    _ = (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A) :=
        (mul_gapSigEufCma_sigReductionKeyInd1Key_eq_sum S b P A).symm

theorem keyInd1Key_hop_G0_1_G1_le_noCollProb (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) :
    |keyInd1KeyAdvG0_1 S P A - keyInd1KeyAdvG1 S P A| ≤
      badSigNoCollProbKeyInd1Key S P A := by
  have h1 : keyInd1KeyExpG0_1 S P A =
      (runKeyInd1KeySim S P A >>= fun (secb, b', finalSt) =>
        if !keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyInd1KeyExpG0_1]
  have h2 : keyInd1KeyExpG1 S P A =
      (runKeyInd1KeySim S P A >>= fun (secb, b', finalSt) =>
        if (!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
           (hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals) then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    have h2_0 : keyInd1KeyExpG1 S P A =
        (runKeyInd1KeySim S P A >>= fun (secb, b', finalSt) =>
          if (!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
             hasBadSigKeyInd finalSt then
            $ᵗ Bool
          else
            pure (b' == secb)) := by
      simp [keyInd1KeyExpG1]
    rw [h2_0]
    congr 1; ext ⟨secb, b', finalSt⟩
    dsimp only
    have hOr :
        ((!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
          hasBadSigKeyInd finalSt) =
        ((!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
          (hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals)) := by
      cases hnp : noPrinPkColl P finalSt.principals
      · have hdup : hasDuplicateBytes (finalSt.principals.map (fun (_, e) => P.pow8 e.ikAPk)) =
            true := by
          unfold noPrinPkColl at hnp; simpa using hnp
        have hcoll : hasDuplicateBytes (allHonestEcPksKeyInd P finalSt) = true := by
          unfold allHonestEcPksKeyInd
          simp only [HasKeyIndState.toKeyIndState, List.append_assoc]
          exact hasDuplicateBytes_append_of_left _ _ hdup
        simp [hasEcPkCollisionKeyInd, hcoll]
      · simp
    rw [hOr]
  unfold keyInd1KeyAdvG0_1 keyInd1KeyAdvG1 badSigNoCollProbKeyInd1Key
  rw [h1, h2]
  exact abs_sub_boolBias_abort_or_le (runKeyInd1KeySim S P A)
    (fun (_, _, finalSt) =>
      !keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt)
    (fun (_, _, finalSt) => hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals)
    (fun (secb, b', _) => pure (b' == secb))

/-- One-key `G0_1 → G1` bound via `sigReductionKeyInd1Key`. -/
theorem keyInd1Key_hop_G0_1_G1_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG0_1 S P A.1 - keyInd1KeyAdvG1 S P A.1| ≤
      (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A) :=
  (keyInd1Key_hop_G0_1_G1_le_noCollProb S P A.1).trans
    (badSigNoCollProbKeyInd1Key_le_gapSigEufCma S b P hP A)

/-- Combined one-key `G0 → G1` bound. -/
theorem keyInd1Key_hop_G0_G1_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG0 S P A.1 - keyInd1KeyAdvG1 S P A.1| ≤
      (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A) +
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  have h0_01 := keyInd1Key_hop_G0_G0_1_le S P hP A.1
  have h01_1 := keyInd1Key_hop_G0_1_G1_le S b P hP A
  have hTri := abs_sub_le (keyInd1KeyAdvG0 S P A.1) (keyInd1KeyAdvG0_1 S P A.1)
    (keyInd1KeyAdvG1 S P A.1)
  linarith

theorem keyInd1Key_hop_G1_G2_le (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyInd1KeyAdvG1 S P A - keyInd1KeyAdvG2 S P A| ≤ 0 := by
  rw [keyInd1KeyAdvG1_eq_G2 S P A, sub_self, abs_zero]

/-- Combined one-key `G0 → G2` bound. -/
theorem keyInd1Key_hop_G0_G2_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG0 S P A.1 - keyInd1KeyAdvG2 S P A.1| ≤
      (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A) +
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  rw [← keyInd1KeyAdvG1_eq_G2 S P A.1]
  exact keyInd1Key_hop_G0_G1_le S b P hP A

end SignalPqxdh.Security

namespace SignalPqxdh

export Security (
  badSigProbKeyInd1KeyAt
  badSigNoCollProbKeyInd1Key
  badSigProbKeyInd1KeyAt_le_gapSigEufCma
  badSigNoCollProbKeyInd1Key_le_gapSigEufCma
  keyInd1Key_hop_G0_1_G1_le
  keyInd1Key_hop_G0_G1_le
  keyInd1Key_hop_G1_G2_le
  keyInd1Key_hop_G0_G2_le
)

end SignalPqxdh
