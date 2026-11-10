/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndSigKem
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Assumptions
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ProbabilityTheory ENNReal
open scoped BigOperators
open SignalPqxdh SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security
/-! ## `buildSecrets` byte-slice extraction -/

@[simp] theorem length_F_X25519 : F_X25519.length = 32 := by
  simp [F_X25519]

theorem drop_take_slice {pfx mid sfx : Bytes} {n m : Nat}
    (hp : pfx.length = n) (hm : mid.length = m) :
    ((pfx ++ mid ++ sfx).drop n).take m = mid := by
  rw [List.append_assoc, ← hp, List.drop_left, ← hm, List.take_left]

def extractDh2 (secrets : Bytes) : Bytes :=
  (secrets.drop 64).take 32

def extractDh4 (secrets : Bytes) : Bytes :=
  (secrets.drop 128).take 32

def extractKemSsNoOPK (secrets : Bytes) : Bytes :=
  (secrets.drop 128).take 32

def extractKemSsOPK (secrets : Bytes) : Bytes :=
  (secrets.drop 160).take 32

theorem extractDh1_buildSecrets
    {dh1 dh2 dh3 : Bytes} {dh4? : Option Bytes} {ss : Bytes}
    (h1 : dh1.length = 32) :
    extractDh1 (buildSecrets dh1 dh2 dh3 dh4? ss) = dh1 := by
  cases dh4? with
  | none =>
    simp only [extractDh1, buildSecrets]
    have h_assoc : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ ss =
        F_X25519 ++ dh1 ++ (dh2 ++ dh3 ++ ss) := by simp [List.append_assoc]
    rw [h_assoc]
    exact drop_take_slice length_F_X25519 h1
  | some dh4 =>
    simp only [extractDh1, buildSecrets]
    have h_assoc : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss =
        F_X25519 ++ dh1 ++ (dh2 ++ dh3 ++ dh4 ++ ss) := by simp [List.append_assoc]
    rw [h_assoc]
    exact drop_take_slice length_F_X25519 h1

theorem extractDh2_buildSecrets
    {dh1 dh2 dh3 : Bytes} {dh4? : Option Bytes} {ss : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) :
    extractDh2 (buildSecrets dh1 dh2 dh3 dh4? ss) = dh2 := by
  have hp : (F_X25519 ++ dh1).length = 64 := by simp [h1]
  cases dh4? with
  | none =>
    simp only [extractDh2, buildSecrets]
    have h_assoc : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ ss =
        (F_X25519 ++ dh1) ++ dh2 ++ (dh3 ++ ss) := by simp [List.append_assoc]
    rw [h_assoc]
    exact drop_take_slice hp h2
  | some dh4 =>
    simp only [extractDh2, buildSecrets]
    have h_assoc : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss =
        (F_X25519 ++ dh1) ++ dh2 ++ (dh3 ++ dh4 ++ ss) := by simp [List.append_assoc]
    rw [h_assoc]
    exact drop_take_slice hp h2

theorem extractDh3_buildSecrets
    {dh1 dh2 dh3 : Bytes} {dh4? : Option Bytes} {ss : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32) :
    extractDh3 (buildSecrets dh1 dh2 dh3 dh4? ss) = dh3 := by
  have hp : (F_X25519 ++ dh1 ++ dh2).length = 96 := by simp [h1, h2]
  cases dh4? with
  | none =>
    simp only [extractDh3, buildSecrets]
    exact drop_take_slice hp h3
  | some dh4 =>
    simp only [extractDh3, buildSecrets]
    have h_assoc : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss =
        (F_X25519 ++ dh1 ++ dh2) ++ dh3 ++ (dh4 ++ ss) := by simp [List.append_assoc]
    rw [h_assoc]
    exact drop_take_slice hp h3

theorem extractDh4_buildSecrets_some
    {dh1 dh2 dh3 dh4 ss : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32)
    (h3 : dh3.length = 32) (h4 : dh4.length = 32) :
    extractDh4 (buildSecrets dh1 dh2 dh3 (some dh4) ss) = dh4 := by
  simp only [extractDh4, buildSecrets]
  have hp : (F_X25519 ++ dh1 ++ dh2 ++ dh3).length = 128 := by simp [h1, h2, h3]
  exact drop_take_slice hp h4

theorem extractKemSsNoOPK_buildSecrets
    {dh1 dh2 dh3 ss : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32)
    (h3 : dh3.length = 32) (hss : ss.length = 32) :
    extractKemSsNoOPK (buildSecrets dh1 dh2 dh3 none ss) = ss := by
  simp only [extractKemSsNoOPK, buildSecrets]
  have hp : (F_X25519 ++ dh1 ++ dh2 ++ dh3).length = 128 := by simp [h1, h2, h3]
  have h_nil : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ ss =
      (F_X25519 ++ dh1 ++ dh2 ++ dh3) ++ ss ++ [] := by simp
  rw [h_nil]
  exact drop_take_slice hp hss

theorem extractKemSsOPK_buildSecrets
    {dh1 dh2 dh3 dh4 ss : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32)
    (h3 : dh3.length = 32) (h4 : dh4.length = 32) (hss : ss.length = 32) :
    extractKemSsOPK (buildSecrets dh1 dh2 dh3 (some dh4) ss) = ss := by
  simp only [extractKemSsOPK, buildSecrets]
  have hp : (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4).length = 160 := by simp [h1, h2, h3, h4]
  have h_nil : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss =
      (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4) ++ ss ++ [] := by simp
  rw [h_nil]
  exact drop_take_slice hp hss

theorem gapDh_nonneg (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pow8 : Bytes → Bytes) (B : GapDhAdv) :
    0 ≤ GapDH P isValidDhTriple pow8 B :=
  ENNReal.toReal_nonneg

/-! ## Generic `KemShCr` simulation -/

/-- State projection for `simulateQ`: if a stateful query handler `implσ` projects onto
`implτ` under `proj : σ → τ` at every query step, then `simulateQ implσ oa` projects onto
`simulateQ implτ oa` for any computation `oa`. -/
theorem map_proj_simulateQ {ι : Type} {O : OracleSpec.{0, 0} ι}
    {σ τ : Type} (proj : σ → τ)
    (implσ : QueryImpl O (StateT σ ProbComp))
    (implτ : QueryImpl O (StateT τ ProbComp))
    (hstep : ∀ (q : ι) (s : σ),
      (Prod.map id proj <$> (implσ q).run s) = (implτ q).run (proj s))
    {α : Type} (oa : OracleComp O α) (s : σ) :
    (Prod.map id proj <$> (simulateQ implσ oa).run s) =
      (simulateQ implτ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp [StateT.run_pure]
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← hstep q s, bind_map_left]
    refine bind_congr fun x => ?_
    exact ih x.1 x.2

abbrev InitKemRecord (S : Setup) := SignalPqxdh.Security.RoKem.InitKemRecord S
abbrev RecvKemRecord := SignalPqxdh.Security.RoKem.RecvKemRecord
abbrev ShCrState.base {S : Setup} {Base : Type} (s : ShCrState S Base) : Base :=
    RoKem.ShCrState.base s
export SignalPqxdh.Security.RoKem (sampleIndexRange)

def isKemShCrPair {S : Setup} (P : Primitives) (i : InitKemRecord S) (r : RecvKemRecord) : Bool :=
  decide (P.kemDecaps r.pqspkSk r.kemCt = some i.kemSs) &&
  decide (r.kemCt ≠ i.kemCt ∨ i.pqspkPk ≠ r.pqspkPk)

def hasBadKemShCrRecordsAt (S : Setup) (P : Primitives) (idx : Nat)
    (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord) : Bool :=
  let bIdx := idx / S.N_send_tot
  let sIdx := idx % S.N_send_tot
  initRecs.any (fun i =>
    (i.sendIdx == sIdx) &&
    recvRecs.any (fun r => (r.bIdx == bIdx) && isKemShCrPair P i r))

def hasBadKemShCrRecords (S : Setup) (P : Primitives)
    (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord) : Bool :=
  (List.range (S.N_spk_tot * S.N_send_tot)).any (fun idx =>
    hasBadKemShCrRecordsAt S P idx initRecs recvRecs)

def isWinningKemShCrCt (P : Primitives) (pk sk chosenPk ct ss candCt : Bytes) : Bool :=
  decide (P.kemDecaps sk candCt = some ss) && decide (candCt ≠ ct ∨ chosenPk ≠ pk)

def extractCollidingKemCt (P : Primitives)
    (pk sk chosenPk ct ss : Bytes) (recvRecs : List RecvKemRecord) : Bytes :=
  match recvRecs.find? (fun r => isWinningKemShCrCt P pk sk chosenPk ct ss r.kemCt) with
  | some r => r.kemCt
  | none   => ct

theorem extractCollidingKemCt_wins_of_find_some (P : Primitives)
    (pk sk chosenPk ct ss : Bytes) (recvRecs : List RecvKemRecord) (r : RecvKemRecord)
    (hfind : recvRecs.find? (fun r => isWinningKemShCrCt P pk sk chosenPk ct ss r.kemCt) = some r) :
    (decide (P.kemDecaps sk (extractCollidingKemCt P pk sk chosenPk ct ss recvRecs) = some ss) &&
     decide (extractCollidingKemCt P pk sk chosenPk ct ss recvRecs ≠ ct ∨ chosenPk ≠ pk)) = true :=
     by
  unfold extractCollidingKemCt
  rw [hfind]
  have hprop := List.find?_some hfind
  simpa [isWinningKemShCrCt] using hprop

theorem extractCollidingKemCt_wins_of_mem_recvRecs {S : Setup} (P : Primitives)
    (pk sk chosenPk ct ss : Bytes) (recvRecs : List RecvKemRecord)
    (i : InitKemRecord S) (r : RecvKemRecord)
    (hr_mem : r ∈ recvRecs)
    (hr_sk : r.pqspkSk = sk) (hr_pk : r.pqspkPk = pk)
    (hi_pk : i.pqspkPk = chosenPk) (hi_ct : i.kemCt = ct) (hi_ss : i.kemSs = ss)
    (hpair : isKemShCrPair P i r = true) :
    (decide (P.kemDecaps sk (extractCollidingKemCt P pk sk chosenPk ct ss recvRecs) = some ss) &&
     decide (extractCollidingKemCt P pk sk chosenPk ct ss recvRecs ≠ ct ∨ chosenPk ≠ pk)) = true :=
     by
  have hwin_r : isWinningKemShCrCt P pk sk chosenPk ct ss r.kemCt = true := by
    unfold isWinningKemShCrCt
    unfold isKemShCrPair at hpair
    rwa [← hr_sk, ← hr_pk, ← hi_pk, ← hi_ct, ← hi_ss]
  have h_some : (recvRecs.find? (fun x => isWinningKemShCrCt P pk sk chosenPk ct ss x.kemCt)).isSome
    :=
    List.find?_isSome.mpr ⟨r, hr_mem, hwin_r⟩
  rcases Option.isSome_iff_exists.mp h_some with ⟨r', hr'⟩
  exact extractCollidingKemCt_wins_of_find_some P pk sk chosenPk ct ss recvRecs r' hr'

theorem spkBundleFlatIdx_inj (S : Setup) (u1 u2 : Fin S.N_id) (j1 j2 : Fin S.N_recv)
    (heq : spkBundleFlatIdx S u1 j1 = spkBundleFlatIdx S u2 j2) :
    u1 = u2 ∧ j1 = j2 := by
  unfold spkBundleFlatIdx at heq
  have hj1 : j1.val < S.N_recv := j1.isLt
  have hj2 : j2.val < S.N_recv := j2.isLt
  have hpos : 0 < S.N_recv := by omega
  have hu : u1.val = u2.val := by
    have h1 : (u1.val * S.N_recv + j1.val) / S.N_recv = u1.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj1, Nat.add_zero]
    have h2 : (u2.val * S.N_recv + j2.val) / S.N_recv = u2.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj2, Nat.add_zero]
    calc u1.val
        = (u1.val * S.N_recv + j1.val) / S.N_recv := h1.symm
      _ = (u2.val * S.N_recv + j2.val) / S.N_recv := by rw [heq]
      _ = u2.val := h2
  have hj : j1.val = j2.val := by
    rw [hu] at heq
    exact Nat.add_left_cancel heq
  exact ⟨Fin.ext hu, Fin.ext hj⟩

def clearShCrTarget {S : Setup} {Base : Type} (hst : ShCrState S Base) : ShCrState S Base :=
  { hst with targetBIdx? := none, targetPk := [], targetSk := [] }

def setShCrTarget {S : Setup} {Base : Type} (hst : ShCrState S Base)
    (bIdx : Nat) (pk sk : Bytes) : ShCrState S Base :=
  { hst with targetBIdx? := some bIdx, targetPk := pk, targetSk := sk }

@[simp] theorem clearShCrTarget_idem {S : Setup} {Base : Type}
    (hst : ShCrState S Base) :
    clearShCrTarget (clearShCrTarget hst) = clearShCrTarget hst := rfl

@[simp] theorem clearShCrTarget_setShCrTarget {S : Setup} {Base : Type}
    (hst : ShCrState S Base) (bIdx : Nat) (pk sk : Bytes) :
    clearShCrTarget (setShCrTarget hst bIdx pk sk) = clearShCrTarget hst := rfl

def hasGeneratedTargetBundle (S : Setup) (bIdx : Nat)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) : Prop :=
  ∃ (u₀ : Fin S.N_id) (j₀ : Fin S.N_recv),
    spkBundleFlatIdx S u₀ j₀ = bIdx ∧
    spkBundles.any (fun (k, _) => k == (u₀.val, j₀.val)) = true

theorem spkBundles_any_eq_true_of_hasGeneratedTargetBundle (S : Setup) (bIdx : Nat)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hgen : hasGeneratedTargetBundle S bIdx spkBundles)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (hb : (spkBundleFlatIdx S u j == bIdx) = true) :
    spkBundles.any (fun (k, _) => k == (u.val, j.val)) = true := by
  rcases hgen with ⟨u₀, j₀, hidx₀, hany₀⟩
  have heq : spkBundleFlatIdx S u j = spkBundleFlatIdx S u₀ j₀ :=
    (beq_iff_eq.mp hb).trans hidx₀.symm
  rcases spkBundleFlatIdx_inj S u u₀ j j₀ heq with ⟨rfl, rfl⟩
  exact hany₀

theorem hasGeneratedTargetBundle_cons (S : Setup) (bIdx : Nat)
    (entry : (Nat × Nat) × SpkBundleEntry)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hgen : hasGeneratedTargetBundle S bIdx spkBundles) :
    hasGeneratedTargetBundle S bIdx (entry :: spkBundles) := by
  rcases hgen with ⟨u₀, j₀, hidx₀, hany₀⟩
  refine ⟨u₀, j₀, hidx₀, ?_⟩
  simp [List.any_cons, hany₀]

theorem bind_congr_of_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (mx : OracleComp spec α) (f g : α → OracleComp spec β)
    (h : ∀ a ∈ support mx, f a = g a) :
    (mx >>= f) = (mx >>= g) := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    congr 1; ext u
    exact ih u (fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩))

theorem simulateQ_run_query_inl {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl QSpec (StateT St ProbComp)) (uq : unifSpec.Domain)
    (oa : (unifSpec + QSpec).Range (Sum.inl uq) → OracleComp (unifSpec + QSpec) α) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM (OracleSpec.query (Sum.inl uq)) >>= oa)).run st =
    (liftM (unifSpec.query uq) >>= fun u =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
        (oa u)).run st) := by
  simp [simulateQ_bind, QueryImpl.liftTarget, StateT.run_bind, StateT.run_monadLift]

theorem simulateQ_run_query_inr {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl QSpec (StateT St ProbComp)) (gq : ι)
    (oa : (unifSpec + QSpec).Range (Sum.inr gq) → OracleComp (unifSpec + QSpec) α) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM (OracleSpec.query (Sum.inr gq)) >>= oa)).run st =
    ((impl gq).run st >>= fun y =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
        (oa y.1)).run y.2) := by
  simp [simulateQ_bind, StateT.run_bind]

theorem simulateQ_shCr_true_eq_false_of_hasGenerated {S : Setup} {Base ι α : Type}
    {QSpec : OracleSpec.{0, 0} ι}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implFalse implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (bIdx : Nat)
    (hClearFalse : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      ∀ x ∈ support ((implFalse q).run hst), clearShCrTarget x.2 = x.2)
    (hAfterGen : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      hasGeneratedTargetBundle S bIdx (getBundles hst.base) →
      (∀ pk sk, (implTrue q).run (setShCrTarget hst bIdx pk sk) =
        Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$> (implFalse q).run hst) ∧
      (∀ x ∈ support ((implFalse q).run hst), hasGeneratedTargetBundle S bIdx
      (getBundles x.2.base)))
    (oa : OracleComp (unifSpec + QSpec) α) (hst : ShCrState S Base)
    (hClear : clearShCrTarget hst = hst)
    (hGen : hasGeneratedTargetBundle S bIdx (getBundles hst.base))
    (pk sk : Bytes) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implTrue
    let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implFalse
    (Prod.map id clearShCrTarget <$> (simulateQ fullTrue oa).run (setShCrTarget hst bIdx pk sk)) =
      (simulateQ fullFalse oa).run hst := by
  intro fullTrue fullFalse
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp [StateT.run_pure, Prod.map, hClear]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullTrue, fullFalse]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, map_bind]
      congr 1; ext u
      exact ih u hst hClear hGen
    | inr gq =>
      dsimp only [fullTrue, fullFalse]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr, map_bind]
      rw [(hAfterGen gq hst hClear hGen).1 pk sk, bind_map_left]
      refine bind_congr_of_support ((implFalse gq).run hst) _ _ (fun x hx => ?_)
      exact ih x.1 x.2 (hClearFalse gq hst hClear x hx) ((hAfterGen gq hst hClear hGen).2 x hx)

theorem evalDist_simulateQ_embedTarget_eq {S : Setup} {Base ι α : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implFalse implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (bIdx : Nat)
    (hClearFalse : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      ∀ x ∈ support ((implFalse q).run hst), clearShCrTarget x.2 = x.2)
    (hAfterGen : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      hasGeneratedTargetBundle S bIdx (getBundles hst.base) →
      (∀ pk sk, (implTrue q).run (setShCrTarget hst bIdx pk sk) =
        Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$> (implFalse q).run hst) ∧
      (∀ x ∈ support ((implFalse q).run hst), hasGeneratedTargetBundle S bIdx
      (getBundles x.2.base)))
    (hBeforeGen : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      ¬ hasGeneratedTargetBundle S bIdx (getBundles hst.base) →
      (∀ pk sk, (implTrue q).run (setShCrTarget hst bIdx pk sk) =
        Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$> (implFalse q).run hst) ∨
      ((∀ obs : QSpec.Range q × ShCrState S Base → ProbComp Bool,
        𝒟[sampleKemKeyGen P >>= fun pair =>
          (implTrue q).run (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x =>
          obs (x.1, clearShCrTarget x.2)] =
        𝒟[(implFalse q).run hst >>= obs]) ∧
       (∀ pk sk, ∀ x ∈ support ((implTrue q).run (setShCrTarget hst bIdx pk sk)),
        x.2 = setShCrTarget (clearShCrTarget x.2) bIdx pk sk ∧
        hasGeneratedTargetBundle S bIdx (getBundles (clearShCrTarget x.2).base))))
    (oa : OracleComp (unifSpec + QSpec) α) (hst : ShCrState S Base)
    (hClear : clearShCrTarget hst = hst)
    (obs : α × ShCrState S Base → ProbComp Bool) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implTrue
    let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implFalse
    𝒟[sampleKemKeyGen P >>= fun pair =>
      (simulateQ fullTrue oa).run (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x =>
      obs (x.1, clearShCrTarget x.2)] =
    𝒟[(simulateQ fullFalse oa).run hst >>= obs] := by
  intro fullTrue fullFalse
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    calc 𝒟[sampleKemKeyGen P >>= fun pair =>
          (simulateQ fullTrue (pure a)).run (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x =>
          obs (x.1, clearShCrTarget x.2)]
        = 𝒟[sampleKemKeyGen P >>= fun _ => obs (a, hst)] := by
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun pair _ => ?_)
          simp [StateT.run_pure, hClear]
      _ = 𝒟[(simulateQ fullFalse (pure a)).run hst >>= obs] := by
          rw [OracleComp.evalDist_bind_const]
          simp [StateT.run_pure]
  | query_bind q oa ih =>
    by_cases hGen : hasGeneratedTargetBundle S bIdx (getBundles hst.base)
    · calc 𝒟[sampleKemKeyGen P >>= fun pair =>
            (simulateQ fullTrue (liftM (OracleSpec.query q) >>= oa)).run
              (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x =>
            obs (x.1, clearShCrTarget x.2)]
          = 𝒟[sampleKemKeyGen P >>= fun _ =>
              (simulateQ fullFalse (liftM (OracleSpec.query q) >>= oa)).run hst >>= obs] := by
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨pk, sk⟩ _ => ?_)
            have hsim := simulateQ_shCr_true_eq_false_of_hasGenerated getBundles implFalse implTrue
              bIdx
              hClearFalse hAfterGen (liftM (OracleSpec.query q) >>= oa) hst hClear hGen pk sk
            dsimp only at hsim
            rw [← hsim, bind_map_left]
            rfl
        _ = 𝒟[(simulateQ fullFalse (liftM (OracleSpec.query q) >>= oa)).run hst >>= obs] :=
            OracleComp.evalDist_bind_const _ _
    · cases q with
      | inl uq =>
        dsimp only [fullTrue, fullFalse]
        simp_rw [simulateQ_run_query_inl, bind_assoc]
        rw [OracleComp.evalDist_bind_bind_swap]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ?_)
        exact ih u hst hClear
      | inr gq =>
        dsimp only [fullTrue, fullFalse]
        simp_rw [simulateQ_run_query_inr, bind_assoc]
        rcases hBeforeGen gq hst hClear hGen with hLeft | ⟨hDist, hSupp⟩
        · calc 𝒟[sampleKemKeyGen P >>= fun pair =>
                (implTrue gq).run (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x =>
                (simulateQ fullTrue (oa x.1)).run x.2 >>= fun y =>
                obs (y.1, clearShCrTarget y.2)]
              = 𝒟[sampleKemKeyGen P >>= fun pair =>
                  (implFalse gq).run hst >>= fun x =>
                  (simulateQ fullTrue (oa x.1)).run (setShCrTarget x.2 bIdx pair.1 pair.2) >>=
                  fun y =>
                  obs (y.1, clearShCrTarget y.2)] := by
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨pk, sk⟩ _ => ?_)
                rw [hLeft pk sk, bind_map_left]
                rfl
            _ = 𝒟[(implFalse gq).run hst >>= fun x =>
                  (simulateQ fullFalse (oa x.1)).run x.2 >>= obs] := by
                rw [OracleComp.evalDist_bind_bind_swap]
                refine OracleComp.evalDist_bind_congr_of_support ((implFalse gq).run hst) _ _
                  (fun x hx => ?_)
                exact ih x.1 x.2 (hClearFalse gq hst hClear x hx)
        · calc 𝒟[sampleKemKeyGen P >>= fun pair =>
                (implTrue gq).run (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x =>
                (simulateQ fullTrue (oa x.1)).run x.2 >>= fun y =>
                obs (y.1, clearShCrTarget y.2)]
              = 𝒟[sampleKemKeyGen P >>= fun pair =>
                  (implTrue gq).run (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x =>
                  (simulateQ fullFalse (oa x.1)).run (clearShCrTarget x.2) >>= obs] := by
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨pk, sk⟩ _ => ?_)
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
                rcases hSupp pk sk x hx with ⟨hx_set, hx_gen⟩
                have hsim := simulateQ_shCr_true_eq_false_of_hasGenerated getBundles implFalse
                  implTrue bIdx
                  hClearFalse hAfterGen (oa x.1) (clearShCrTarget x.2)
                  (clearShCrTarget_idem x.2) hx_gen pk sk
                dsimp only at hsim
                rw [← hx_set] at hsim
                rw [← hsim, bind_map_left]
                rfl
            _ = 𝒟[(implFalse gq).run hst >>= fun x =>
                  (simulateQ fullFalse (oa x.1)).run x.2 >>= obs] :=
                hDist (fun x => (simulateQ fullFalse (oa x.1)).run x.2 >>= obs)

def spkBundleFlatIdxVal (S : Setup) (k : Nat × Nat) : Nat :=
  k.1 * S.N_recv + k.2

def ValidTargetRecv {S : Setup} {Base : Type}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (bIdx : Nat) (pk sk : Bytes) (hst : ShCrState S Base) : Prop :=
  hst.targetBIdx? = some bIdx ∧ hst.targetPk = pk ∧ hst.targetSk = sk ∧
  (∀ p ∈ getBundles hst.base, (spkBundleFlatIdxVal S p.1 == bIdx) = true →
    p.2.pqspkPk = pk ∧ p.2.pqspkSk = sk) ∧
  (∀ r ∈ hst.recvKemRecs, (r.bIdx == bIdx) = true →
    r.pqspkPk = pk ∧ r.pqspkSk = sk)

theorem simulateQ_post_sIdx_invariant {S : Setup} {Base ι α : Type}
    {QSpec : OracleSpec.{0, 0} ι}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (bIdx sIdx : Nat) (pk sk : Bytes)
    (hValidStep : ∀ (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles bIdx pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles bIdx pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (P_rec : InitKemRecord S → Prop)
    (oa : OracleComp (unifSpec + QSpec) α) (hst : ShCrState S Base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst)
    (hLt : sIdx < hst.sendCount)
    (hRec : ∀ i ∈ hst.initKemRecs, i.sendIdx = sIdx → P_rec i) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implTrue
    ∀ x ∈ support ((simulateQ fullTrue oa).run hst),
      ValidTargetRecv getBundles bIdx pk sk x.2 ∧
      sIdx < x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i.sendIdx = sIdx → P_rec i) := by
  intro fullTrue
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    intro x hx
    change x ∈ support (pure (a, hst)) at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hV, hLt, hRec⟩
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      intro x hx
      dsimp only [fullTrue] at hx
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨u, _, hx⟩
      exact ih u hst hV hLt hRec x hx
    | inr gq =>
      intro x hx
      dsimp only [fullTrue] at hx
      rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨y, hy, hx⟩
      have hVy := hValidStep gq hst hV y hy
      rcases hSendStep gq hst y hy with ⟨hLe, hInit⟩
      have hLty : sIdx < y.2.sendCount := Nat.lt_of_lt_of_le hLt hLe
      have hRecy : ∀ i ∈ y.2.initKemRecs, i.sendIdx = sIdx → P_rec i := by
        intro i hi his
        rcases hInit i hi with hi_old | ⟨hi_eq, _⟩
        · exact hRec i hi_old his
        · omega
      exact ih y.1 y.2 hVy hLty hRecy x hx

theorem hasBadKemShCrRecordsAt_eq_false_of_forall_ne (S : Setup) (P : Primitives) (idx : Nat)
    (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord)
    (hne : ∀ i ∈ initRecs, i.sendIdx ≠ idx % S.N_send_tot) :
    hasBadKemShCrRecordsAt S P idx initRecs recvRecs = false := by
  unfold hasBadKemShCrRecordsAt
  rw [List.any_eq_false]
  intro i hi htrue
  simp only [Bool.and_eq_true, beq_iff_eq] at htrue
  exact hne i hi htrue.1

theorem evalDist_simulateQ_badKem_eq_zero_of_gt {S : Setup} {Base ι α : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (idx : Nat) (pk sk : Bytes)
    (hValidStep : ∀ (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles
      (idx / S.N_send_tot) pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (oa : OracleComp (unifSpec + QSpec) α) (hst : ShCrState S Base)
    (hV : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst)
    (hLt : idx % S.N_send_tot < hst.sendCount)
    (hNe : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ idx % S.N_send_tot) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implTrue
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)] {true} = 0 := by
  intro fullTrue
  have hPost := simulateQ_post_sIdx_invariant getBundles implTrue
    (idx / S.N_send_tot) (idx % S.N_send_tot) pk sk hValidStep hSendStep
    (fun _ => False) oa hst hV hLt (fun i hi heq => hNe i hi heq)
  have h_congr :
      𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
        pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)] =
      𝒟[(simulateQ fullTrue oa).run hst >>= fun _ => (pure false : ProbComp Bool)] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
    rw [hasBadKemShCrRecordsAt_eq_false_of_forall_ne S P idx x.2.initKemRecs x.2.recvKemRecs
      (fun i hi heq => (hPost x hx).2.2 i hi heq)]
  rw [h_congr, OracleComp.evalDist_bind_const]
  simp [evalDist_pure]

theorem evalDist_simulateQ_badKem_le_win_of_gt {S : Setup} {Base ι α : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (idx : Nat) (pk sk chosenPk ct ss : Bytes)
    (hValidStep : ∀ (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles
      (idx / S.N_send_tot) pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (oa : OracleComp (unifSpec + QSpec) α) (hst : ShCrState S Base)
    (hV : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst)
    (hLt : idx % S.N_send_tot < hst.sendCount)
    (hRec : ∀ i ∈ hst.initKemRecs, i.sendIdx = idx % S.N_send_tot →
      i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implTrue
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)] {true} ≤
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      let ct' := extractCollidingKemCt P pk sk chosenPk ct ss x.2.recvKemRecs
      pure (decide (P.kemDecaps sk ct' = some ss) && decide (ct' ≠ ct ∨ chosenPk ≠ pk))] {true} :=
      by
  intro fullTrue
  have hPost := simulateQ_post_sIdx_invariant getBundles implTrue
    (idx / S.N_send_tot) (idx % S.N_send_tot) pk sk hValidStep hSendStep
    (fun i => i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss) oa hst hV hLt hRec
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun x hx => ?_)
  rcases hPost x hx with ⟨hVx, _, hRecx⟩
  cases hbad : hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs
  · simp [evalDist_pure]
  · unfold hasBadKemShCrRecordsAt at hbad
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hbad
    rcases hbad with ⟨i, hi_mem, hi_idx, r, hr_mem, hr_bidx, hpair⟩
    rcases hRecx i hi_mem hi_idx with ⟨hi_pk, hi_ct, hi_ss⟩
    have hr_keys := hVx.2.2.2.2 r hr_mem (beq_iff_eq.mpr hr_bidx)
    have hwin := extractCollidingKemCt_wins_of_mem_recvRecs P pk sk chosenPk ct ss
      x.2.recvKemRecs i r hr_mem hr_keys.2 hr_keys.1 hi_pk hi_ct hi_ss hpair
    simp only [hwin, le_rfl]

structure PausedShCrKem (S : Setup) (Base : Type) where
  bundle : PreKeyBundleInput
  resume : Bytes → Bytes → ProbComp (Bool × ShCrState S Base)

noncomputable def stepUntilShCr {S : Setup} {Base ι : Type} {QSpec : OracleSpec.{0, 0} ι}
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (tryPause : (q : ι) → (QSpec.Range q → OracleComp (unifSpec + QSpec) Bool) →
      ShCrState S Base → Option (PausedShCrKem S Base))
    (oa : OracleComp (unifSpec + QSpec) Bool) :
    ShCrState S Base → ProbComp (Sum (Bool × ShCrState S Base) (PausedShCrKem S Base)) :=
  OracleComp.construct
    (fun b' hst => return Sum.inl (b', hst))
    (fun q cont rec hst =>
      match q with
      | Sum.inl unifQ => do
        let x ← liftM (unifSpec.query unifQ)
        rec x hst
      | Sum.inr gq =>
        match tryPause gq cont hst with
        | some paused => return Sum.inr paused
        | none => do
          let (out, hst') ← (implTrue gq).run hst
          rec out hst')
    oa

theorem stepUntilShCr_query_inl {S : Setup} {Base ι : Type} {QSpec : OracleSpec.{0, 0} ι}
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (tryPause : (q : ι) → (QSpec.Range q → OracleComp (unifSpec + QSpec) Bool) →
      ShCrState S Base → Option (PausedShCrKem S Base))
    (uq : unifSpec.Domain)
    (cont : (unifSpec + QSpec).Range (Sum.inl uq) → OracleComp (unifSpec + QSpec) Bool)
    (hst : ShCrState S Base) :
    stepUntilShCr implTrue tryPause (liftM (OracleSpec.query (Sum.inl uq)) >>= cont) hst =
      (liftM (unifSpec.query uq) >>= fun x => stepUntilShCr implTrue tryPause (cont x) hst) := rfl

theorem stepUntilShCr_query_inr {S : Setup} {Base ι : Type} {QSpec : OracleSpec.{0, 0} ι}
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (tryPause : (q : ι) → (QSpec.Range q → OracleComp (unifSpec + QSpec) Bool) →
      ShCrState S Base → Option (PausedShCrKem S Base))
    (gq : ι)
    (cont : (unifSpec + QSpec).Range (Sum.inr gq) → OracleComp (unifSpec + QSpec) Bool)
    (hst : ShCrState S Base) :
    stepUntilShCr implTrue tryPause (liftM (OracleSpec.query (Sum.inr gq)) >>= cont) hst =
      match tryPause gq cont hst with
      | some paused => pure (Sum.inr paused)
      | none => (implTrue gq).run hst >>= fun x => stepUntilShCr implTrue tryPause (cont x.1) x.2 :=
        rfl

theorem evalDist_stepUntilShCr_le {S : Setup} {Base ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (tryPause : Nat → (q : ι) → (QSpec.Range q → OracleComp (unifSpec + QSpec) Bool) →
      ShCrState S Base → Option (PausedShCrKem S Base))
    (idx : Nat) (pk sk : Bytes)
    (hValidStep : ∀ (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles
      (idx / S.N_send_tot) pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (hPauseNone : ∀ (gq : ι) (cont : QSpec.Range gq → OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base),
      hst.sendCount ≤ idx % S.N_send_tot →
      tryPause (idx % S.N_send_tot) gq cont hst = none →
      ∀ x ∈ support ((implTrue gq).run hst), x.2.sendCount ≤ idx % S.N_send_tot)
    (hPauseSome : ∀ (gq : ι) (cont : QSpec.Range gq → OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base) (paused : PausedShCrKem S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      tryPause (idx % S.N_send_tot) gq cont hst = some paused →
      ∃ (noneOut : QSpec.Range gq)
        (postKem : Bytes → Bytes → ProbComp (QSpec.Range gq × ShCrState S Base)),
        (∀ ss ct, paused.resume ss ct =
          (postKem ss ct >>= fun y =>
            (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT (ShCrState S Base) ProbComp) + implTrue) (cont y.1)).run y.2)) ∧
        (∀ obs : QSpec.Range gq × ShCrState S Base → ProbComp Bool,
          𝒟[(implTrue gq).run hst >>= obs] =
          𝒟[sampleCoins32 >>= fun r =>
            match P.kemEncaps paused.bundle.pqspkB r with
            | none => obs (noneOut, { hst with sendCount := idx % S.N_send_tot + 1 })
            | some (ss, ct) => postKem ss ct >>= obs]) ∧
        (∀ ss ct, ∀ y ∈ support (postKem ss ct),
          ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk y.2 ∧
          idx % S.N_send_tot < y.2.sendCount ∧
          (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
            (i.sendIdx = idx % S.N_send_tot ∧
             i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))))
    (oa : OracleComp (unifSpec + QSpec) Bool) (hst : ShCrState S Base)
    (hV : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst)
    (hLe : hst.sendCount ≤ idx % S.N_send_tot)
    (hInitLt : ∀ i ∈ hst.initKemRecs, i.sendIdx < hst.sendCount) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implTrue
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)] {true} ≤
    𝒟[stepUntilShCr implTrue (tryPause (idx % S.N_send_tot)) oa hst >>= fun res =>
      let chosenPk := match res with
        | Sum.inl _      => pk
        | Sum.inr paused => paused.bundle.pqspkB
      sampleCoins32 >>= fun r =>
      match P.kemEncaps chosenPk r with
      | none => pure false
      | some (ss, ct) =>
        (match res with
         | Sum.inl done   => pure done
         | Sum.inr paused => paused.resume ss ct) >>= fun x =>
        let ct' := extractCollidingKemCt P pk sk chosenPk ct ss x.2.recvKemRecs
        pure (decide (P.kemDecaps sk ct' = some ss) && decide (ct' ≠ ct ∨ chosenPk ≠ pk))] {true} :=
        by
  intro fullTrue
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure b' =>
    have hne : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ idx % S.N_send_tot := by
      intro i hi
      have := hInitLt i hi
      omega
    have h_lhs :
        ((simulateQ fullTrue (pure b')).run hst >>= fun x =>
          pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)) =
        pure false := by
      simp [StateT.run_pure,
        hasBadKemShCrRecordsAt_eq_false_of_forall_ne S P idx hst.initKemRecs hst.recvKemRecs hne]
    rw [h_lhs]
    simp [evalDist_pure]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullTrue]
      rw [simulateQ_run_query_inl, stepUntilShCr_query_inl, bind_assoc, bind_assoc]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
        (fun u _ => ?_)
      exact ih u hst hV hLe hInitLt
    | inr gq =>
      dsimp only [fullTrue]
      rw [simulateQ_run_query_inr, stepUntilShCr_query_inr, bind_assoc]
      cases hPause : tryPause (idx % S.N_send_tot) gq oa hst with
      | none =>
        dsimp only
        rw [bind_assoc]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
          (fun x hx => ?_)
        have hVx := hValidStep gq hst hV x hx
        have hLex := hPauseNone gq oa hst hLe hPause x hx
        rcases hSendStep gq hst x hx with ⟨hSendLe, hInit⟩
        have hInitLtx : ∀ i ∈ x.2.initKemRecs, i.sendIdx < x.2.sendCount := by
          intro i hi
          rcases hInit i hi with hi_old | ⟨hi_eq, hi_lt⟩
          · exact Nat.lt_of_lt_of_le (hInitLt i hi_old) hSendLe
          · omega
        exact ih x.1 x.2 hVx hLex hInitLtx
      | some paused =>
        rcases hPauseSome gq oa hst paused hV hPause with
          ⟨noneOut, postKem, hResume, hDist, hPostSupp⟩
        dsimp only
        rw [pure_bind, hDist (fun x => (simulateQ fullTrue (oa x.1)).run x.2 >>= fun y =>
          pure (hasBadKemShCrRecordsAt S P idx y.2.initKemRecs y.2.recvKemRecs))]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
          (fun r _ => ?_)
        cases P.kemEncaps paused.bundle.pqspkB r with
        | none =>
          have hV_next : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk
              { hst with sendCount := idx % S.N_send_tot + 1 } := hV
          have hNe : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ idx % S.N_send_tot := by
            intro i hi; have := hInitLt i hi; omega
          have hZero := evalDist_simulateQ_badKem_eq_zero_of_gt P getBundles implTrue idx pk sk
            hValidStep hSendStep (oa noneOut) { hst with sendCount := idx % S.N_send_tot + 1 }
            hV_next (Nat.lt_succ_self _) hNe
          dsimp only at hZero
          rw [hZero]
          simp [evalDist_pure]
        | some kemPair =>
          rcases kemPair with ⟨ss, ct⟩
          dsimp only
          rw [hResume ss ct, bind_assoc]
          refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
            (fun y hy => ?_)
          rcases hPostSupp ss ct y hy with ⟨hVy, hLty, hInity⟩
          have hRecy : ∀ i ∈ y.2.initKemRecs, i.sendIdx = idx % S.N_send_tot →
              i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss := by
            intro i hi his
            rcases hInity i hi with hi_old | ⟨_, hpk, hct, hss⟩
            · have := hInitLt i hi_old; omega
            · exact ⟨hpk, hct, hss⟩
          exact evalDist_simulateQ_badKem_le_win_of_gt P getBundles implTrue idx pk sk
            paused.bundle.pqspkB ct ss hValidStep hSendStep (oa y.1) y.2 hVy hLty hRecy

noncomputable def shcrChoosePkGenericAt {S : Setup} {Base ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (initBaseComp : ProbComp Base)
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (tryPause : Nat → (q : ι) → (QSpec.Range q → OracleComp (unifSpec + QSpec) Bool) →
      ShCrState S Base → Option (PausedShCrKem S Base))
    (bIdx sIdx : Nat) (oa : OracleComp (unifSpec + QSpec) Bool)
    (pk sk : Bytes) : ProbComp (Bytes × (Bytes → Bytes → ProbComp Bytes)) := do
  let b0 ← initBaseComp
  let initSt : ShCrState S Base := {
    base        := b0
    targetBIdx? := some bIdx
    targetPk    := pk
    targetSk    := sk
  }
  let res ← stepUntilShCr implTrue (tryPause sIdx) oa initSt
  let chosenPk := match res with
    | Sum.inl _      => pk
    | Sum.inr paused => paused.bundle.pqspkB
  let finishComp : Bytes → Bytes → ProbComp Bytes := fun ss ct => do
    let (_, finalHst) ← match res with
      | Sum.inl done   => pure done
      | Sum.inr paused => paused.resume ss ct
    return extractCollidingKemCt P pk sk chosenPk ct ss finalHst.recvKemRecs
  return (chosenPk, finishComp)

noncomputable def kemShCrExpProb (P : Primitives)
    (choosePk : Bytes → Bytes → ProbComp (Bytes × (Bytes → Bytes → ProbComp Bytes))) :
    ProbComp Bool := do
  let (pk, sk) ← sampleKemKeyGen P
  let (pk', finishComp) ← choosePk pk sk
  let r ← sampleCoins32
  let some (ss, ct) := P.kemEncaps pk' r | return false
  let ct' ← finishComp ss ct
  return (decide (P.kemDecaps sk ct' = some ss) && decide (ct' ≠ ct ∨ pk' ≠ pk))

theorem kemShCrWin_pure_eq_of_cwf (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {pk sk pk' r ss ct ct' : Bytes}
    {d1 : Decidable (P.kemDecaps sk ct' = some ss)}
    {d2 : Decidable (ct' ≠ ct ∨ pk' ≠ pk)}
    {d3 : Decidable (ct'.length = kyberCtLen ∧ pk'.length = kyberPkLen)}
    {d1' : Decidable (P.kemDecaps sk ct' = some ss)}
    {d2' : Decidable (ct' ≠ ct ∨ pk' ≠ pk)}
    (hEnc : P.kemEncaps pk' r = some (ss, ct)) :
    (pure (@decide _ d1 && @decide _ d2 && @decide _ d3) : ProbComp Bool) =
    pure (@decide _ d1' && @decide _ d2') := by
  have hd1 : @decide _ d1 = @decide _ d1' := by congr
  have hd2 : @decide _ d2 = @decide _ d2' := by congr
  rw [hd1, hd2]
  have hpk : pk'.length = kyberPkLen := by
    by_contra hne
    rw [hP.kemEncaps_len_reject pk' r hne] at hEnc
    cases hEnc
  by_cases hdec : P.kemDecaps sk ct' = some ss
  · have hct : ct'.length = kyberCtLen := by
      by_contra hne
      rw [hP.kemDecaps_len_reject sk ct' hne] at hdec
      cases hdec
    have hd3 : @decide _ d3 = true := @decide_eq_true _ d3 ⟨hct, hpk⟩
    simp [hd3]
  · have hd1f : @decide _ d1' = false := @decide_eq_false _ d1' hdec
    simp [hd1f]

theorem badKemShCrProbGenericAt_le_kemShCr {S : Setup} {Base ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (initBaseComp : ProbComp Base)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implFalse implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (tryPause : Nat → (q : ι) → (QSpec.Range q → OracleComp (unifSpec + QSpec) Bool) →
      ShCrState S Base → Option (PausedShCrKem S Base))
    (idx : Nat)
    (hInitBundles : ∀ b0 ∈ support initBaseComp, getBundles b0 = [])
    (hClearFalse : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      ∀ x ∈ support ((implFalse q).run hst), clearShCrTarget x.2 = x.2)
    (hAfterGen : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles hst.base) →
      (∀ pk sk, (implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pk sk) =
        Prod.map id (fun s' => setShCrTarget s' (idx / S.N_send_tot) pk sk) <$>
        (implFalse q).run hst) ∧
      (∀ x ∈ support ((implFalse q).run hst),
        hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles x.2.base)))
    (hBeforeGen : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      ¬ hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles hst.base) →
      (∀ pk sk, (implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pk sk) =
        Prod.map id (fun s' => setShCrTarget s' (idx / S.N_send_tot) pk sk) <$>
        (implFalse q).run hst) ∨
      ((∀ obs : QSpec.Range q × ShCrState S Base → ProbComp Bool,
        𝒟[sampleKemKeyGen P >>= fun pair =>
          (implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pair.1 pair.2) >>= fun x =>
          obs (x.1, clearShCrTarget x.2)] =
        𝒟[(implFalse q).run hst >>= obs]) ∧
       (∀ pk sk, ∀ x ∈ support ((implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pk sk)),
        x.2 = setShCrTarget (clearShCrTarget x.2) (idx / S.N_send_tot) pk sk ∧
        hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles (clearShCrTarget x.2).base))))
    (hValidStep : ∀ (pk sk : Bytes) (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles
      (idx / S.N_send_tot) pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (hPauseNone : ∀ (gq : ι) (cont : QSpec.Range gq → OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base),
      hst.sendCount ≤ idx % S.N_send_tot →
      tryPause (idx % S.N_send_tot) gq cont hst = none →
      ∀ x ∈ support ((implTrue gq).run hst), x.2.sendCount ≤ idx % S.N_send_tot)
    (hPauseSome : ∀ (pk sk : Bytes) (gq : ι) (cont : QSpec.Range gq →
      OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base) (paused : PausedShCrKem S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      tryPause (idx % S.N_send_tot) gq cont hst = some paused →
      ∃ (noneOut : QSpec.Range gq)
        (postKem : Bytes → Bytes → ProbComp (QSpec.Range gq × ShCrState S Base)),
        (∀ ss ct, paused.resume ss ct =
          (postKem ss ct >>= fun y =>
            (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT (ShCrState S Base) ProbComp) + implTrue) (cont y.1)).run y.2)) ∧
        (∀ obs : QSpec.Range gq × ShCrState S Base → ProbComp Bool,
          𝒟[(implTrue gq).run hst >>= obs] =
          𝒟[sampleCoins32 >>= fun r =>
            match P.kemEncaps paused.bundle.pqspkB r with
            | none => obs (noneOut, { hst with sendCount := idx % S.N_send_tot + 1 })
            | some (ss, ct) => postKem ss ct >>= obs]) ∧
        (∀ ss ct, ∀ y ∈ support (postKem ss ct),
          ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk y.2 ∧
          idx % S.N_send_tot < y.2.sendCount ∧
          (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
            (i.sendIdx = idx % S.N_send_tot ∧
             i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))))
    (oa : OracleComp (unifSpec + QSpec) Bool) :
    let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implFalse
    𝒟[initBaseComp >>= fun b0 =>
      (simulateQ fullFalse oa).run { base := b0 } >>= fun x =>
      pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)] {true} ≤
    𝒟[kemShCrExpProb P (shcrChoosePkGenericAt P initBaseComp implTrue tryPause
      (idx / S.N_send_tot) (idx % S.N_send_tot) oa)] {true} := by
  intro fullFalse
  let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (ShCrState S Base) ProbComp) + implTrue
  have h_embed :
      𝒟[initBaseComp >>= fun b0 =>
        (simulateQ fullFalse oa).run { base := b0 } >>= fun x =>
        pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)] =
      𝒟[initBaseComp >>= fun b0 =>
        sampleKemKeyGen P >>= fun pair =>
        (simulateQ fullTrue oa).run (setShCrTarget { base := b0 }
        (idx / S.N_send_tot) pair.1 pair.2) >>= fun x =>
        pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun b0 _ => ?_)
    exact (evalDist_simulateQ_embedTarget_eq P getBundles implFalse implTrue
      (idx / S.N_send_tot) hClearFalse hAfterGen hBeforeGen oa { base := b0 } rfl
      (fun x => pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs))).symm
  rw [h_embed, OracleComp.evalDist_bind_bind_swap]
  unfold kemShCrExpProb shcrChoosePkGenericAt
  simp only [bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun pksk _ => ?_)
  rcases pksk with ⟨pk, sk⟩
  dsimp only
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun b0 hb0 => ?_)
  have hV0 : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk
      (setShCrTarget ({ base := b0 } : ShCrState S Base) (idx / S.N_send_tot) pk sk) := by
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro p hp
      simp [setShCrTarget, hInitBundles b0 hb0] at hp
    · intro r hr
      simp [setShCrTarget] at hr
  have hLe0 : (setShCrTarget ({ base := b0 } : ShCrState S Base)
      (idx / S.N_send_tot) pk sk).sendCount ≤
      idx % S.N_send_tot := Nat.zero_le _
  have hInit0 : ∀ i ∈ (setShCrTarget ({ base := b0 } : ShCrState S Base)
      (idx / S.N_send_tot) pk sk).initKemRecs,
      i.sendIdx < (setShCrTarget ({ base := b0 } : ShCrState S Base)
      (idx / S.N_send_tot) pk sk).sendCount := by
    intro i hi
    simp [setShCrTarget] at hi
  have hStep := evalDist_stepUntilShCr_le P getBundles implTrue tryPause idx pk sk
    (hValidStep pk sk) hSendStep hPauseNone (hPauseSome pk sk) oa
    (setShCrTarget ({ base := b0 } : ShCrState S Base) (idx / S.N_send_tot) pk sk)
    hV0 hLe0 hInit0
  dsimp only at hStep
  refine le_trans hStep ?_
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun res _ => ?_)
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun r _ => ?_)
  cases res with
  | inl done =>
    dsimp only
    cases P.kemEncaps pk r with
    | none => exact le_rfl
    | some kemPair =>
      rcases kemPair with ⟨ss, ct⟩
      dsimp only
      rw [pure_bind, pure_bind]
  | inr paused =>
    dsimp only
    cases P.kemEncaps paused.bundle.pqspkB r with
    | none => exact le_rfl
    | some kemPair =>
      rcases kemPair with ⟨ss, ct⟩
      dsimp only
      rw [bind_assoc]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
        (fun x _ => ?_)
      rw [pure_bind]

/-! ### Generic query-category lemmas -/

theorem clearShCrTarget_eq_iff {S : Setup} {Base : Type} (hst : ShCrState S Base) :
    clearShCrTarget hst = hst ↔
    hst.targetBIdx? = none ∧ hst.targetPk = [] ∧ hst.targetSk = [] := by
  cases hst
  simp [clearShCrTarget, eq_comm]

def liftShCrBase {S : Setup} {Base α : Type}
    (m : StateT Base ProbComp α) : StateT (ShCrState S Base) ProbComp α := fun hst => do
  let (a, base') ← m.run hst.base
  return (a, { hst with base := base' })

theorem liftShCrBase_clearFalse {S : Setup} {Base α : Type}
    (m : StateT Base ProbComp α) (hst : ShCrState S Base)
    (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((liftShCrBase m).run hst), clearShCrTarget x.2 = x.2 := by
  intro x hx
  simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨b, _, hx⟩
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  rw [clearShCrTarget_eq_iff] at hClear ⊢
  exact hClear

theorem liftShCrBase_setShCrTarget {S : Setup} {Base α : Type}
    (m : StateT Base ProbComp α) (hst : ShCrState S Base) (bIdx : Nat) (pk sk : Bytes) :
    (liftShCrBase m).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$> (liftShCrBase m).run hst := by
  simp [liftShCrBase, StateT.run, setShCrTarget, Prod.map]

theorem liftShCrBase_preserves_bundles {S : Setup} {Base α : Type}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (m : StateT Base ProbComp α) (hst : ShCrState S Base)
    (hm : ∀ y ∈ support (m.run hst.base), getBundles y.2 = getBundles hst.base) :
    ∀ x ∈ support ((liftShCrBase m).run hst), getBundles x.2.base = getBundles hst.base := by
  intro x hx
  simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨y, hy, hx⟩
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact hm y hy

theorem liftShCrBase_validStep {S : Setup} {Base α : Type}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (m : StateT Base ProbComp α) (bIdx : Nat) (pk sk : Bytes) (hst : ShCrState S Base)
    (hm : ∀ y ∈ support (m.run hst.base), getBundles y.2 = getBundles hst.base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst) :
    ∀ x ∈ support ((liftShCrBase m).run hst), ValidTargetRecv getBundles bIdx pk sk x.2 := by
  intro x hx
  have hBundles := liftShCrBase_preserves_bundles getBundles m hst hm x hx
  simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨y, _, hx⟩
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨hV.1, hV.2.1, hV.2.2.1, ?_, hV.2.2.2.2⟩
  intro p hp
  rw [hBundles] at hp
  exact hV.2.2.2.1 p hp

theorem liftShCrBase_sendStep {S : Setup} {Base α : Type}
    (m : StateT Base ProbComp α) (hst : ShCrState S Base) :
    ∀ x ∈ support ((liftShCrBase m).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  intro x hx
  simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨y, _, hx⟩
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨le_rfl, fun i hi => Or.inl hi⟩

theorem liftShCrBase_pauseNone {S : Setup} {Base α : Type}
    (m : StateT Base ProbComp α) (sIdx : Nat) (hst : ShCrState S Base)
    (hLe : hst.sendCount ≤ sIdx) :
    ∀ x ∈ support ((liftShCrBase m).run hst), x.2.sendCount ≤ sIdx := by
  intro x hx
  simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨y, _, hx⟩
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact hLe

def recordAcceptKemGeneric {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) : StateT (ShCrState S Base) ProbComp Resp := fun hst =>
  if isNoneResp out then pure (out, hst)
  else
    match (getBundles hst.base).find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => pure (out, hst)
    | some (_, bEntry) =>
      match P.kemDecaps bEntry.pqspkSk hdr.kemCt with
      | none => pure (out, hst)
      | some ss =>
        let r : RecvKemRecord := {
          bIdx    := spkBundleFlatIdx S k j
          k       := k.val
          j       := j.val
          pqspkPk := bEntry.pqspkPk
          pqspkSk := bEntry.pqspkSk
          kemCt   := hdr.kemCt
          kemSs   := ss
        }
        pure (out, { hst with recvKemRecs := r :: hst.recvKemRecs })

theorem recordAcceptKemGeneric_setShCrTarget {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) (hst : ShCrState S Base) (bIdx : Nat) (pk sk : Bytes) :
    (recordAcceptKemGeneric P getBundles isNoneResp k j hdr out).run
      (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (recordAcceptKemGeneric P getBundles isNoneResp k j hdr out).run hst := by
  unfold recordAcceptKemGeneric StateT.run
  dsimp only [setShCrTarget]
  cases isNoneResp out
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases (getBundles hst.base).find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => simp [Prod.map]
    | some pair =>
      rcases pair with ⟨_, bEntry⟩
      dsimp only
      cases P.kemDecaps bEntry.pqspkSk hdr.kemCt <;> simp [Prod.map]
  · simp [Prod.map]

theorem mem_support_recordAcceptKemGeneric {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) (hst : ShCrState S Base) (x : Resp × ShCrState S Base)
    (hx : x ∈ support ((recordAcceptKemGeneric P getBundles isNoneResp k j hdr out).run hst)) :
    x = (out, hst) ∨
    ∃ idxPair bEntry ss,
      (getBundles hst.base).find? (fun (idx, _) => idx == (k.val, j.val)) = some (idxPair, bEntry) ∧
      P.kemDecaps bEntry.pqspkSk hdr.kemCt = some ss ∧
      x = (out, { hst with recvKemRecs := {
        bIdx    := spkBundleFlatIdx S k j
        k       := k.val
        j       := j.val
        pqspkPk := bEntry.pqspkPk
        pqspkSk := bEntry.pqspkSk
        kemCt   := hdr.kemCt
        kemSs   := ss } :: hst.recvKemRecs }) := by
  unfold recordAcceptKemGeneric StateT.run at hx
  dsimp only at hx
  cases hnone : isNoneResp out
  · rw [hnone] at hx
    simp only [Bool.false_eq_true, ↓reduceIte] at hx
    revert hx
    cases hfind : (getBundles hst.base).find? (fun (idx, _) => idx == (k.val, j.val))
    · intro hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      exact Or.inl hx
    · rename_i pair
      rcases pair with ⟨idxPair, bEntry⟩
      dsimp only
      cases hdec : P.kemDecaps bEntry.pqspkSk hdr.kemCt
      · intro hx
        simp only [support_pure, Set.mem_singleton_iff] at hx
        exact Or.inl hx
      · rename_i ss
        intro hx
        simp only [support_pure, Set.mem_singleton_iff] at hx
        exact Or.inr ⟨idxPair, bEntry, ss, rfl, hdec, hx⟩
  · rw [hnone] at hx
    simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hx
    exact Or.inl hx

theorem recordAcceptKemGeneric_clearFalse {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) (hst : ShCrState S Base)
    (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((recordAcceptKemGeneric P getBundles isNoneResp k j hdr out).run hst),
      clearShCrTarget x.2 = x.2 := by
  intro x hx
  rcases mem_support_recordAcceptKemGeneric P getBundles isNoneResp k j hdr out hst x hx with
    rfl | ⟨_, _, _, _, _, rfl⟩
  · exact hClear
  · rw [clearShCrTarget_eq_iff] at hClear ⊢
    exact hClear

theorem recordAcceptKemGeneric_preserves_base_and_send {S : Setup} {Base Resp : Type}
    (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) (hst : ShCrState S Base) :
    ∀ x ∈ support ((recordAcceptKemGeneric P getBundles isNoneResp k j hdr out).run hst),
      x.2.base = hst.base ∧ x.2.sendCount = hst.sendCount ∧ x.2.initKemRecs = hst.initKemRecs := by
  intro x hx
  rcases mem_support_recordAcceptKemGeneric P getBundles isNoneResp k j hdr out hst x hx with
    rfl | ⟨_, _, _, _, _, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

theorem recordAcceptKemGeneric_validStep {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) (bIdx : Nat) (pk sk : Bytes) (hst : ShCrState S Base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst) :
    ∀ x ∈ support ((recordAcceptKemGeneric P getBundles isNoneResp k j hdr out).run hst),
      ValidTargetRecv getBundles bIdx pk sk x.2 := by
  intro x hx
  rcases mem_support_recordAcceptKemGeneric P getBundles isNoneResp k j hdr out hst x hx with
    rfl | ⟨idxPair, bEntry, ss, hfind, _, rfl⟩
  · exact hV
  · refine ⟨hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, ?_⟩
    intro r hr hrb
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr_old
    · have hmem := List.mem_of_find?_eq_some hfind
      have hpred := List.find?_some hfind
      simp only [beq_iff_eq] at hpred
      have hb_eq : (spkBundleFlatIdxVal S idxPair == bIdx) = true := by
        rw [hpred]
        exact hrb
      exact hV.2.2.2.1 (idxPair, bEntry) hmem hb_eq
    · exact hV.2.2.2.2 r hr_old hrb

def mkSpkBundlePair (P : Primitives) (j : Nat) (uEntry : PrincipalEntry)
    (spkSk rSpk pqspkPk pqspkSk rPq : Bytes) : SpkBundleEntry × PreKeyBundleInput :=
  let spkPk := P.x25519Base spkSk
  let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
  let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
  let bEntry : SpkBundleEntry := {
    spkSk    := spkSk
    spkPk    := spkPk
    spkSig   := spkSig
    pqspkSk  := pqspkSk
    pqspkPk  := pqspkPk
    pqspkSig := pqspkSig
  }
  let bundleOut : PreKeyBundleInput := {
    ikB      := uEntry.ikAPk
    spkId    := UInt32.ofNat j
    spkB     := spkPk
    spkSig   := spkSig
    opkB?    := none
    pqspkId  := UInt32.ofNat j
    pqspkB   := pqspkPk
    pqspkSig := pqspkSig
  }
  (bEntry, bundleOut)

def genSpkBaseGeneric {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) : StateT Base ProbComp Resp := do
  let st ← get
  if (getBundles st).any (fun (k, _) => k == (u.val, j.val)) then
    return noneResp
  let some (_, uEntry) := (getPrincipals st).find? (fun (idx, _) => idx == u.val)
    | return noneResp
  let spkSk ← liftM sampleScalar32
  let rSpk ← liftM sampleRandom64
  let (pqspkPk, pqspkSk) ← liftM (sampleKemKeyGen P)
  let rPq ← liftM sampleRandom64
  let (bEntry, bundleOut) := mkSpkBundlePair P j.val uEntry spkSk rSpk pqspkPk pqspkSk rPq
  set (setBundles st (((u.val, j.val), bEntry) :: getBundles st))
  return bundleResp bundleOut

def genSpkTargetGeneric {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (ShCrState S Base) ProbComp Resp := fun hst => do
  let st := hst.base
  if (getBundles st).any (fun (k, _) => k == (u.val, j.val)) then
    return (noneResp, hst)
  let some (_, uEntry) := (getPrincipals st).find? (fun (idx, _) => idx == u.val)
    | return (noneResp, hst)
  let spkSk ← sampleScalar32
  let rSpk ← sampleRandom64
  let rPq ← sampleRandom64
  let (bEntry, bundleOut) := mkSpkBundlePair P j.val uEntry spkSk rSpk hst.targetPk hst.targetSk rPq
  return (bundleResp bundleOut,
    { hst with base := setBundles st (((u.val, j.val), bEntry) :: getBundles st) })

def runShCrGenSPKGeneric {S : Setup} {Base Resp : Type} (embedTarget : Bool) (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (ShCrState S Base) ProbComp Resp := fun hst =>
  if !embedTarget then
    (liftShCrBase (genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp u
    j)).run hst
  else
    match hst.targetBIdx? with
    | none =>
      (liftShCrBase (genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp u
      j)).run hst
    | some bIdx =>
      if spkBundleFlatIdx S u j == bIdx then
        (genSpkTargetGeneric P getPrincipals getBundles setBundles noneResp bundleResp u j).run hst
      else
        (liftShCrBase (genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp u
        j)).run hst

theorem runShCrGenSPKGeneric_false_run {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : ShCrState S Base) :
    (runShCrGenSPKGeneric false P getPrincipals getBundles setBundles noneResp bundleResp u j).run
      hst =
      (liftShCrBase (genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp u
      j)).run hst := rfl

theorem runShCrGenSPKGeneric_true_run_setShCrTarget {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : ShCrState S Base) (bIdx : Nat) (pk sk : Bytes) :
    (runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp bundleResp u j).run
      (setShCrTarget hst bIdx pk sk) =
    if spkBundleFlatIdx S u j == bIdx then
      (genSpkTargetGeneric P getPrincipals getBundles setBundles noneResp bundleResp u j).run
        (setShCrTarget hst bIdx pk sk)
    else
      (liftShCrBase (genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp u
        j)).run
        (setShCrTarget hst bIdx pk sk) := rfl

theorem runShCrGenSPKGeneric_true_run {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : ShCrState S Base) :
    (runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp bundleResp u j).run
    hst =
    match hst.targetBIdx? with
    | none =>
      (liftShCrBase (genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp u
      j)).run hst
    | some bIdx =>
      if spkBundleFlatIdx S u j == bIdx then
        (genSpkTargetGeneric P getPrincipals getBundles setBundles noneResp bundleResp u j).run hst
      else
        (liftShCrBase (genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp u
        j)).run hst := rfl

theorem mem_support_genSpkBaseGeneric {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : Base) (y : Resp × Base)
    (hy : y ∈ support ((genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp
    u j).run st)) :
    y = (noneResp, st) ∨
    ∃ uEntry spkSk rSpk pqspkPk pqspkSk rPq,
      (getBundles st).any (fun (k, _) => k == (u.val, j.val)) = false ∧
      y = (bundleResp (mkSpkBundlePair P j.val uEntry spkSk rSpk pqspkPk pqspkSk rPq).2,
           setBundles st (((u.val, j.val), (mkSpkBundlePair P j.val uEntry spkSk rSpk pqspkPk
           pqspkSk rPq).1) :: getBundles st)) := by
  unfold genSpkBaseGeneric at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  revert hy
  cases hany : (getBundles st).any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hfind : (getPrincipals st).find? (fun (idx, _) => idx == u.val)
    · intro hy
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      exact Or.inl hy
    · rename_i pair
      rcases pair with ⟨_, uEntry⟩
      dsimp only
      intro hy
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, hy⟩
      exact Or.inr ⟨uEntry, spkSk, rSpk, pqspkPk, pqspkSk, rPq, trivial, hy⟩
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    intro hy
    exact Or.inl hy

theorem mem_support_genSpkTargetGeneric {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : ShCrState S Base) (x : Resp × ShCrState S Base)
    (hx : x ∈ support ((genSpkTargetGeneric P getPrincipals getBundles setBundles noneResp
    bundleResp u j).run hst)) :
    x = (noneResp, hst) ∨
    ∃ uEntry spkSk rSpk rPq,
      (getBundles hst.base).any (fun (k, _) => k == (u.val, j.val)) = false ∧
      x = (bundleResp (mkSpkBundlePair P j.val uEntry spkSk rSpk hst.targetPk hst.targetSk rPq).2,
           { hst with base := setBundles hst.base (((u.val, j.val),
             (mkSpkBundlePair P j.val uEntry spkSk rSpk hst.targetPk hst.targetSk rPq).1) ::
             getBundles hst.base) }) := by
  unfold genSpkTargetGeneric StateT.run at hx
  dsimp only at hx
  revert hx
  cases hany : (getBundles hst.base).any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hfind : (getPrincipals hst.base).find? (fun (idx, _) => idx == u.val)
    · intro hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      exact Or.inl hx
    · rename_i pair
      rcases pair with ⟨_, uEntry⟩
      dsimp only
      intro hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨spkSk, _, rSpk, _, rPq, _, hx⟩
      exact Or.inr ⟨uEntry, spkSk, rSpk, rPq, trivial, hx⟩
  · simp only [↓reduceIte, support_pure, Set.mem_singleton_iff]
    intro hx
    exact Or.inl hx

theorem runShCrGenSPKGeneric_clearFalse {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : ShCrState S Base)
    (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((runShCrGenSPKGeneric false P getPrincipals getBundles setBundles noneResp
      bundleResp u j).run hst),
      clearShCrTarget x.2 = x.2 :=
  liftShCrBase_clearFalse _ hst hClear

theorem runShCrGenSPKGeneric_afterGen {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (hGetSet : ∀ (b : Base) bs, getBundles (setBundles b bs) = bs)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (bIdx : Nat) (hst : ShCrState S Base)
    (_hClear : clearShCrTarget hst = hst)
    (hGen : hasGeneratedTargetBundle S bIdx (getBundles hst.base)) :
    (∀ pk sk, (runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp bundleResp u
      j).run
      (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (runShCrGenSPKGeneric false P getPrincipals getBundles setBundles noneResp bundleResp u
        j).run hst) ∧
    (∀ x ∈ support ((runShCrGenSPKGeneric false P getPrincipals getBundles setBundles noneResp
      bundleResp u j).run hst),
      hasGeneratedTargetBundle S bIdx (getBundles x.2.base)) := by
  constructor
  · intro pk sk
    rw [runShCrGenSPKGeneric_true_run_setShCrTarget, runShCrGenSPKGeneric_false_run]
    cases hidx : (spkBundleFlatIdx S u j == bIdx)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact liftShCrBase_setShCrTarget _ hst bIdx pk sk
    · simp only [↓reduceIte]
      have hany := spkBundles_any_eq_true_of_hasGeneratedTargetBundle S bIdx
        (getBundles hst.base) hGen u j
        hidx
      unfold genSpkTargetGeneric liftShCrBase genSpkBaseGeneric StateT.run
      dsimp only [setShCrTarget]
      simp [StateT.run_bind, StateT.run_get, StateT.run_pure, hany, Prod.map]
  · intro x hx
    rw [runShCrGenSPKGeneric_false_run] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨y, hy, hx⟩
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    rcases mem_support_genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp u
      j hst.base y hy with
      rfl | ⟨uEntry, spkSk, rSpk, pqspkPk, pqspkSk, rPq, _, rfl⟩
    · exact hGen
    · dsimp only
      rw [hGetSet]
      exact hasGeneratedTargetBundle_cons S bIdx _ _ hGen

theorem runShCrGenSPKGeneric_beforeGen {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (hGetSet : ∀ (b : Base) bs, getBundles (setBundles b bs) = bs)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (bIdx : Nat) (hst : ShCrState S Base)
    (hClear : clearShCrTarget hst = hst)
    (_hNotGen : ¬ hasGeneratedTargetBundle S bIdx (getBundles hst.base)) :
    (∀ pk sk, (runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp bundleResp u
      j).run
      (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (runShCrGenSPKGeneric false P getPrincipals getBundles setBundles noneResp bundleResp u
        j).run hst) ∨
    ((∀ obs : Resp × ShCrState S Base → ProbComp Bool,
      𝒟[sampleKemKeyGen P >>= fun pair =>
        (runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp bundleResp u
          j).run
          (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x =>
        obs (x.1, clearShCrTarget x.2)] =
      𝒟[(runShCrGenSPKGeneric false P getPrincipals getBundles setBundles noneResp bundleResp u
      j).run hst >>= obs]) ∧
     (∀ pk sk, ∀ x ∈ support ((runShCrGenSPKGeneric true P getPrincipals getBundles setBundles
        noneResp bundleResp u j).run
        (setShCrTarget hst bIdx pk sk)),
      x.2 = setShCrTarget (clearShCrTarget x.2) bIdx pk sk ∧
      hasGeneratedTargetBundle S bIdx (getBundles (clearShCrTarget x.2).base))) := by
  cases hidx : (spkBundleFlatIdx S u j == bIdx)
  · left
    intro pk sk
    rw [runShCrGenSPKGeneric_true_run_setShCrTarget, runShCrGenSPKGeneric_false_run, hidx]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact liftShCrBase_setShCrTarget _ hst bIdx pk sk
  · cases hany : (getBundles hst.base).any (fun (k, _) => k == (u.val, j.val))
    · cases hfind : (getPrincipals hst.base).find? (fun (idx, _) => idx == u.val)
      · left
        intro pk sk
        rw [runShCrGenSPKGeneric_true_run_setShCrTarget, runShCrGenSPKGeneric_false_run, hidx]
        simp only [↓reduceIte]
        unfold genSpkTargetGeneric liftShCrBase genSpkBaseGeneric StateT.run
        dsimp only [setShCrTarget]
        simp [StateT.run_bind, StateT.run_get, StateT.run_pure, hany, hfind, Prod.map]
      · rename_i pair
        rcases pair with ⟨_, uEntry⟩
        right
        have hClearSet : ∀ (b' : Base) (pk sk : Bytes),
            clearShCrTarget ({ setShCrTarget hst bIdx pk sk with base := b' } : ShCrState S Base) =
            { hst with base := b' } := by
          intro b' pk sk
          rw [clearShCrTarget_eq_iff] at hClear
          cases hst
          dsimp only at hClear
          rcases hClear with ⟨rfl, rfl, rfl⟩
          rfl
        constructor
        · intro obs
          have hTarget : ∀ pair : Bytes × Bytes,
              (runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp bundleResp u
                j).run
                (setShCrTarget hst bIdx pair.1 pair.2) =
              (sampleScalar32 >>= fun spkSk =>
               sampleRandom64 >>= fun rSpk =>
               sampleRandom64 >>= fun rPq =>
               let (bEntry, bundleOut) := mkSpkBundlePair P j.val uEntry spkSk rSpk pair.1 pair.2
                 rPq
               pure (bundleResp bundleOut,
                 { setShCrTarget hst bIdx pair.1 pair.2 with
                   base := setBundles hst.base (((u.val, j.val), bEntry) :: getBundles hst.base) }))
                   := by
            intro pair
            rw [runShCrGenSPKGeneric_true_run_setShCrTarget, hidx]
            simp only [↓reduceIte]
            unfold genSpkTargetGeneric StateT.run
            dsimp only [setShCrTarget]
            rw [hany, hfind]
            rfl
          have hBase :
              (runShCrGenSPKGeneric false P getPrincipals getBundles setBundles noneResp bundleResp
              u j).run hst =
              (sampleScalar32 >>= fun spkSk =>
               sampleRandom64 >>= fun rSpk =>
               sampleKemKeyGen P >>= fun pair =>
               sampleRandom64 >>= fun rPq =>
               let (bEntry, bundleOut) := mkSpkBundlePair P j.val uEntry spkSk rSpk pair.1 pair.2
                 rPq
               pure (bundleResp bundleOut,
                 { hst with
                   base := setBundles hst.base (((u.val, j.val), bEntry) :: getBundles hst.base) }))
                   := by
            rw [runShCrGenSPKGeneric_false_run]
            unfold liftShCrBase genSpkBaseGeneric StateT.run
            dsimp only
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hany, Bool.false_eq_true,
              ↓reduceIte, hfind, StateT.run_monadLift, monadLift_self, StateT.run_set,
              StateT.run_pure, bind_assoc]
          simp only [hTarget, hBase, bind_assoc, pure_bind]
          rw [OracleComp.evalDist_bind_bind_swap (sampleKemKeyGen P) sampleScalar32]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spkSk _ => ?_)
          rw [OracleComp.evalDist_bind_bind_swap (sampleKemKeyGen P) sampleRandom64]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rSpk _ => ?_)
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemPair _ => ?_)
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rPq _ => ?_)
          rw [hClearSet]
        · intro pk sk x hx
          rw [runShCrGenSPKGeneric_true_run_setShCrTarget, hidx] at hx
          simp only [↓reduceIte] at hx
          unfold genSpkTargetGeneric StateT.run at hx
          dsimp only [setShCrTarget] at hx
          rw [hany, hfind] at hx
          simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
            support_pure, Set.mem_singleton_iff] at hx
          rcases hx with ⟨spkSk, _, rSpk, _, rPq, _, hx⟩
          subst hx
          constructor
          · rfl
          · dsimp only [clearShCrTarget]
            rw [hGetSet]
            refine ⟨u, j, beq_iff_eq.mp hidx, ?_⟩
            simp [List.any_cons]
    · left
      intro pk sk
      rw [runShCrGenSPKGeneric_true_run_setShCrTarget, runShCrGenSPKGeneric_false_run, hidx]
      simp only [↓reduceIte]
      unfold genSpkTargetGeneric liftShCrBase genSpkBaseGeneric StateT.run
      dsimp only [setShCrTarget]
      simp [StateT.run_bind, StateT.run_get, StateT.run_pure, hany, Prod.map]

theorem runShCrGenSPKGeneric_validStep {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (hGetSet : ∀ (b : Base) bs, getBundles (setBundles b bs) = bs)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (bIdx : Nat) (pk sk : Bytes) (hst : ShCrState S Base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst) :
    ∀ x ∈ support ((runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp
      bundleResp u j).run hst),
      ValidTargetRecv getBundles bIdx pk sk x.2 := by
  intro x hx
  rw [runShCrGenSPKGeneric_true_run, hV.1] at hx
  dsimp only at hx
  revert hx
  cases hidx : (spkBundleFlatIdx S u j == bIdx)
  · simp only [Bool.false_eq_true, ↓reduceIte, liftShCrBase, StateT.run,
      MonadAttach.mem_support_bind]
    intro hx
    rcases hx with ⟨y, hy, hx⟩
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    rcases mem_support_genSpkBaseGeneric P getPrincipals getBundles setBundles noneResp bundleResp u
      j hst.base y hy with
      rfl | ⟨uEntry, spkSk, rSpk, pqspkPk, pqspkSk, rPq, _, rfl⟩
    · exact hV
    · refine ⟨hV.1, hV.2.1, hV.2.2.1, ?_, hV.2.2.2.2⟩
      intro p hp hpb
      dsimp only at hp
      rw [hGetSet] at hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp_old
      · exfalso
        have h1 : spkBundleFlatIdxVal S (u.val, j.val) = spkBundleFlatIdx S u j := rfl
        rw [h1, hidx] at hpb
        exact Bool.noConfusion hpb
      · exact hV.2.2.2.1 p hp_old hpb
  · simp only [↓reduceIte]
    intro hx
    rcases mem_support_genSpkTargetGeneric P getPrincipals getBundles setBundles noneResp bundleResp
      u j hst x hx with
      rfl | ⟨uEntry, spkSk, rSpk, rPq, _, rfl⟩
    · exact hV
    · refine ⟨hV.1, hV.2.1, hV.2.2.1, ?_, hV.2.2.2.2⟩
      intro p hp hpb
      dsimp only at hp
      rw [hGetSet] at hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp_old
      · exact ⟨hV.2.1, hV.2.2.1⟩
      · exact hV.2.2.2.1 p hp_old hpb

theorem runShCrGenSPKGeneric_sendStep {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : ShCrState S Base) :
    ∀ x ∈ support ((runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp
      bundleResp u j).run hst),
      x.2.sendCount = hst.sendCount ∧ x.2.initKemRecs = hst.initKemRecs := by
  intro x hx
  rw [runShCrGenSPKGeneric_true_run] at hx
  revert hx
  cases hst.targetBIdx?
  · simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind]
    intro hx
    rcases hx with ⟨_, _, hx⟩
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨rfl, rfl⟩
  · rename_i bIdx
    dsimp only
    cases hidx : (spkBundleFlatIdx S u j == bIdx)
    · simp only [Bool.false_eq_true, ↓reduceIte, liftShCrBase, StateT.run,
        MonadAttach.mem_support_bind]
      intro hx
      rcases hx with ⟨_, _, hx⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨rfl, rfl⟩
    · simp only [↓reduceIte]
      intro hx
      rcases mem_support_genSpkTargetGeneric P getPrincipals getBundles setBundles noneResp
        bundleResp u j hst x hx with
        rfl | ⟨_, _, _, _, _, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-! ### Generic Receiver & Initiator Combinators -/

def runShCrAcceptGeneric {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) :
    StateT (ShCrState S Base) ProbComp Resp := do
  let out ← liftShCrBase baseAccept
  recordAcceptKemGeneric P getBundles isNoneResp k j hdr out

end Proofs.SignalPqxdh.Security
