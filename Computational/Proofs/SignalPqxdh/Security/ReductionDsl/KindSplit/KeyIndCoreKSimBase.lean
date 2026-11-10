/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCore -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKem -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyShcr -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK -- proof-setup: allow-public-import

/-!
# Shared Base for `KeyIndCore` and `KemShCr` Forgetful Step Simulation

Shared query-budget predicates, sentinel forget maps, online list-length and AVL random-oracle
shadow invariants, and clamped fuel-identity lemmas for kind-split `KeyInd` step simulations.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase

open OracleSpec OracleComp
open _root_.SignalPqxdh (
  Setup QueryBudget KeyIndQuery KeyIndAdversary keyIndSpec
  isKeyIndOnlineQuery isKeyIndRoQuery isGameQuery BoundedAdv HasQueryBound
)
open _root_.SignalPqxdh.Security (keyIndQueryKind)
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface
  pqAtomicSig pqAtomicOps pqPrimIface pqKeyIndCodec
  B PB U32 drKeyT bundleT hdrT sidT
  sidV bundleV hdrV
)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  AtomicIface TagLift embedTy embedVal projVal embedEnv
  mapExpr mapComp mapSamp exprRename compRename
  exprRename_eval compRename_eval mapComp_eval mapExpr_eval mapSamp_eval
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  Ext PT keyIndStateTy shcrStTy pauseTy RS initQTy accQTy
  letV bindV caseOptV eLet eLet2 eFind eAny eMap findMV anyMV
  stPrin stSpks stOpks stSess stResps stUsedO stUsedN stKyb stRo stAdv
  scBase scTB onBase eqB sDrKey96
  emptyStE freshE kyberCheckE
  findHonestC isAdvRegC isGameSpkC isGameOpkC
  koskBundleOkC koskSenderOkC resolveSigPkC honestPeerC
  checkProvC partnerC recordRespC hkdfOrRoC
  preCheckC checkSigsC
  initPrin1KeyB initPrinB corruptB genSpkB shcrGenSpkB genOpkB
  testB revealB revealDhB registerB revealSpkB
  sIndex keyIndLoopBound
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  dfltDrKeyE avlSearchB192C avlInsertAtPathC samplePbytes32C sampleDrKey96AtomicC
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec (
  avlInsertAtPathC_eval_congr
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine (
  RoCacheRel RoCacheRelB192
)
open _root_.Computational.Proofs.ReductionDsl.StepSim (
  bumpPred isGamePred isQueryBoundP_min ForgetSim
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  KeyIndCoreFuels keyIndCoreFuels keyIndSentinel keyIndSentinel_le lt_keyIndSentinel
  roAvlTy roListAtomicTy roListLegacyTy keyIndBaseAtomicTy keyIndStateKTy
  forgetCore shcrKindStTy forgetShcrKind emptyRoAvlE
  roShadowQueryC shcrActiveGenSpkLeg dispatchKeyIndQ
  runAt2 runAt3 runAt4 runAt5 runAt6
)

/-- Three-predicate query-budget family classifying `KeyInd` queries into online (`0`),
    random-oracle (`1`), and all queries (`2`). -/
@[expose] def keyIndSimPred (S : Setup) : Fin 3 → KeyIndQuery S → Prop
  | ⟨0, _⟩ => fun q => isKeyIndOnlineQuery (.inr q)
  | ⟨1, _⟩ => fun q => isKeyIndRoQuery (.inr q)
  | ⟨2, _⟩ => fun _ => True

instance instDecidablePredKeyIndSimPred (S : Setup) (j : Fin 3) :
    DecidablePred (keyIndSimPred S j) := by
  match j with
  | ⟨0, _⟩ => intro q; exact inferInstanceAs (Decidable (isKeyIndOnlineQuery (.inr q)))
  | ⟨1, _⟩ => intro q; exact inferInstanceAs (Decidable (isKeyIndRoQuery (.inr q)))
  | ⟨2, _⟩ => intro _; exact instDecidableTrue

/-- Clamped online, random-oracle, and total query bounds for `keyIndSimPred`. -/
@[expose] def keyIndSimBounds (b : QueryBudget) : Fin 3 → ℕ
  | ⟨0, _⟩ => min b.q_on b.q_total
  | ⟨1, _⟩ => min b.q_ro b.q_total
  | ⟨2, _⟩ => b.q_total

theorem isKeyIndOnlineQuery_xor_isRoQuery {S : Setup} (t : KeyIndQuery S) :
    (isKeyIndOnlineQuery (.inr t) ∧ ¬ isKeyIndRoQuery (.inr t)) ∨
    (¬ isKeyIndOnlineQuery (.inr t) ∧ isKeyIndRoQuery (.inr t)) := by
  cases t <;> simp [isKeyIndOnlineQuery, isKeyIndRoQuery]

@[simp] theorem keyIndSimPred_zero_iff_kind {S : Setup} (t : KeyIndQuery S) :
    keyIndSimPred S 0 t ↔ keyIndQueryKind t = 0 := by
  cases t <;> simp [keyIndSimPred, isKeyIndOnlineQuery, keyIndQueryKind]

@[simp] theorem keyIndSimPred_one_iff_kind {S : Setup} (t : KeyIndQuery S) :
    keyIndSimPred S 1 t ↔ keyIndQueryKind t = 1 := by
  cases t <;> simp [keyIndSimPred, isKeyIndRoQuery, keyIndQueryKind]

theorem bumpPred_keyIndSimPred_sum {S : Setup} {c : Fin 3 → ℕ} (t : KeyIndQuery S)
    (hSum : c 0 + c 1 = c 2) :
    let c' := bumpPred (keyIndSimPred S) c t
    c' 0 + c' 1 = c' 2 := by
  dsimp only
  rcases isKeyIndOnlineQuery_xor_isRoQuery t with ⟨hOn, hNoRo⟩ | ⟨hNoOn, hRo⟩
  · simp [bumpPred, keyIndSimPred, hOn, hNoRo]
    omega
  · simp [bumpPred, keyIndSimPred, hNoOn, hRo]
    omega

private theorem isQueryBoundP_of_imp {ι₀ : Type} {spec : OracleSpec ι₀} {α : Type}
    {oa : OracleComp spec α} {p q : ι₀ → Prop} [DecidablePred p] [DecidablePred q]
    (himp : ∀ t, p t → q t) {m : ℕ} (h : oa.IsQueryBoundP q m) :
    oa.IsQueryBoundP p m := by
  induction oa using OracleComp.inductionOn generalizing m with
  | pure x => exact isQueryBoundP_pure p x m
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨?_, fun u => (ih u (h.2 u)).mono ?_⟩
    · by_cases hp : p t
      · exact Or.inr (h.1.resolve_left (not_not.mpr (himp t hp)))
      · exact Or.inl hp
    · by_cases hp : p t
      · simp only [hp, himp t hp, ite_true]; omega
      · simp only [hp, ite_false]; split <;> omega

/-- Bridges `BoundedAdv` to the three-predicate `IsQueryBoundP` family for `StepSim`. -/
theorem boundedAdv_imp_keyIndSimPred {S : Setup} {b : QueryBudget}
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ (j : Fin 3),
      A.1.run.IsQueryBoundP (isGamePred (G := keyIndSpec S) (keyIndSimPred S j))
        (keyIndSimBounds b j) := by
  rcases A with ⟨adv, hRo, _, _, hTot, hOn⟩
  intro j
  fin_cases j
  · have hEq : isGamePred (G := keyIndSpec S) (keyIndSimPred S 0) = isKeyIndOnlineQuery := by
      funext q; cases q <;> simp [isGamePred, keyIndSimPred, isKeyIndOnlineQuery]
    have hTotOn : adv.run.IsQueryBoundP isKeyIndOnlineQuery b.q_total :=
      isQueryBoundP_of_imp (fun q hq => by cases q <;> simp_all [isKeyIndOnlineQuery, isGameQuery]) hTot
    simpa only [Fin.zero_eta, keyIndSimBounds, hEq] using isQueryBoundP_min hOn hTotOn
  · have hEq : isGamePred (G := keyIndSpec S) (keyIndSimPred S 1) = isKeyIndRoQuery := by
      funext q; cases q <;> simp [isGamePred, keyIndSimPred, isKeyIndRoQuery]
    have hTotRo : adv.run.IsQueryBoundP isKeyIndRoQuery b.q_total :=
      isQueryBoundP_of_imp (fun q hq => by cases q <;> simp_all [isKeyIndRoQuery, isGameQuery]) hTot
    simpa only [Fin.mk_one, keyIndSimBounds, hEq] using isQueryBoundP_min hRo hTotRo
  · have hEq : isGamePred (G := keyIndSpec S) (keyIndSimPred S 2) =
        (fun q => isGameQuery q = true) := by
      funext q; cases q <;> simp [isGamePred, keyIndSimPred, isGameQuery]
    simpa only [Fin.reduceFinMk, keyIndSimBounds, hEq] using hTot

theorem boundedAdv_unit_imp_keyIndSimPred {S : Setup} {b : QueryBudget}
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ (a : Unit) (j : Fin 3),
      ((fun _ : Unit => A.1.run) a).IsQueryBoundP
        (isGamePred (G := keyIndSpec S) (keyIndSimPred S j))
        (keyIndSimBounds b j) :=
  fun _ j => boundedAdv_imp_keyIndSimPred A j

/-- Maps `keyIndSentinel S b` back to the legacy sentinel `b.q_total + 1`, fixing smaller ordinals. -/
@[expose] def fixSent (S : Setup) (b : QueryBudget) (n : ℕ) : ℕ :=
  if n = keyIndSentinel S b then b.q_total + 1 else n

@[simp] theorem fixSent_keyIndSentinel (S : Setup) (b : QueryBudget) :
    fixSent S b (keyIndSentinel S b) = b.q_total + 1 := by
  simp [fixSent]

theorem fixSent_of_lt_N_dh {S : Setup} {b : QueryBudget} {k : ℕ} (hk : k < S.N_dh) :
    fixSent S b k = k := by
  unfold fixSent keyIndSentinel
  split_ifs with h
  · omega
  · rfl

theorem beq_fixSent_of_le_mOn {S : Setup} {b : QueryBudget} {len n : ℕ}
    (hLen : len ≤ min b.q_on b.q_total) :
    (len == n) = (len == fixSent S b n) := by
  have hLtSent : min b.q_on b.q_total < keyIndSentinel S b := lt_keyIndSentinel S b
  have hSentLe : keyIndSentinel S b ≤ b.q_total + 1 := keyIndSentinel_le S b
  unfold fixSent
  split_ifs with hEq
  · subst hEq
    have hNe1 : len ≠ keyIndSentinel S b := by omega
    have hNe2 : len ≠ b.q_total + 1 := by omega
    simp [beq_eq_false_iff_ne.mpr hNe1, beq_eq_false_iff_ne.mpr hNe2]
  · rfl

theorem mem_support_sIndex_lt {Γ : List PT} (n : ℕ) (hPos : 0 < n) (env : Env Γ) {k : ℕ}
    (hk : k ∈ support ((sIndex n : Comp pqxdhOps _ Γ .nat).eval env)) :
    k < n := by
  simp only [sIndex, Comp.eval, ReductionDsl.Iface.liftP,
    _root_.SignalPqxdh.LegacyCosted.pqPrimIface, _root_.SignalPqxdh.LegacyCosted.pqSamplers,
    _root_.SignalPqxdh.LegacyCosted.PSamp.run, _root_.SignalPqxdh.LegacyCosted.sampleIndex,
    hPos, ↓reduceDIte, simulateQ_bind, simulateQ_pure,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hk
  rcases hk with ⟨i, _, rfl⟩
  exact i.isLt

@[expose] def fixShcrStSent (S : Setup) (b : QueryBudget)
    (s : (embedTy shcrStTy).denote) : (embedTy shcrStTy).denote :=
  let (base, (tb, (tpk, (tsk, (cnt, (ir, (rr, (sIdx, chosen)))))))) := s
  (base, (tb, (tpk, (tsk, (cnt, (ir, (rr, (fixSent S b sIdx, chosen))))))))

/-- Forgetful state projection for one-key active `KemShCr`, dropping `roAvl` and remapping `scSIdx`. -/
@[expose] def forgetShcrKindActive (S : Setup) (b : QueryBudget)
    (sK : shcrKindStTy.denote) : (embedTy shcrStTy).denote :=
  fixShcrStSent S b (forgetShcrKind sK)

@[expose] def stPrinList  (bSt : keyIndStateTy.denote) := bSt.2.1
@[expose] def stSpksList  (bSt : keyIndStateTy.denote) := bSt.2.2.1
@[expose] def stOpksList  (bSt : keyIndStateTy.denote) := bSt.2.2.2.1
@[expose] def stSessList  (bSt : keyIndStateTy.denote) := bSt.2.2.2.2.1
@[expose] def stRespsList (bSt : keyIndStateTy.denote) := bSt.2.2.2.2.2.1
@[expose] def stUsedOList (bSt : keyIndStateTy.denote) := bSt.2.2.2.2.2.2.1
@[expose] def stUsedNList (bSt : keyIndStateTy.denote) := bSt.2.2.2.2.2.2.2.1
@[expose] def stKybList   (bSt : keyIndStateTy.denote) := bSt.2.2.2.2.2.2.2.2.1
@[expose] def stRoList    (bSt : keyIndStateTy.denote) := bSt.2.2.2.2.2.2.2.2.2.1
@[expose] def stAdvList   (bSt : keyIndStateTy.denote) := bSt.2.2.2.2.2.2.2.2.2.2

/-- Invariant bounding all online `keyIndStateTy` list lengths by `c 0` and tracking `c 0 + c 1 = c 2`. -/
structure BaseOnlineLenInv (c : Fin 3 → ℕ) (bSt : keyIndStateTy.denote) : Prop where
  prin_le   : (stPrinList bSt).length  ≤ c 0
  spks_le   : (stSpksList bSt).length  ≤ c 0
  opks_le   : (stOpksList bSt).length  ≤ c 0
  sess_le   : (stSessList bSt).length  ≤ c 0
  resps_le  : (stRespsList bSt).length ≤ c 0
  usedO_le  : (stUsedOList bSt).length ≤ c 0
  usedN_le  : (stUsedNList bSt).length ≤ c 0
  kyb_le    : (stKybList bSt).length   ≤ c 0
  adv_le    : (stAdvList bSt).length   ≤ c 0
  counts_eq : c 0 + c 1 = c 2

theorem BaseOnlineLenInv.empty (secb : Bool) :
    BaseOnlineLenInv 0 ((emptyStE (.bool secb) : Expr pqxdhOps [] keyIndStateTy).eval .nil) :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
   Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩

theorem take_min_eq_of_length_le {α : Type} (l : List α) {K₁ K₂ N : ℕ}
    (hLen : l.length ≤ K₁) (hLe : K₁ ≤ K₂) :
    l.take (min K₁ N) = l.take (min K₂ N) := by
  by_cases hN : N ≤ K₁
  · have h1 : min K₁ N = N := Nat.min_eq_right hN
    have h2 : min K₂ N = N := Nat.min_eq_right (Nat.le_trans hN hLe)
    rw [h1, h2]
  · have h1 : l.length ≤ min K₁ N := Nat.le_min.mpr ⟨hLen, by omega⟩
    have h2 : l.length ≤ min K₂ N := Nat.le_min.mpr ⟨Nat.le_trans hLen hLe, by omega⟩
    rw [List.take_of_length_le h1, List.take_of_length_le h2]

/-- Exact-key AVL shadow invariant relating the random-oracle list `roList` and `roAvl`. -/
abbrev RoCacheAvlInv (listCap roCap : ℕ)
    (roList : roListAtomicTy.denote) (roAvl : roAvlTy.denote) : Prop :=
  RoCacheRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) listCap roCap roList roAvl

theorem RoCacheAvlInv.empty (listCap roCap : ℕ) :
    RoCacheAvlInv listCap roCap [] ((emptyRoAvlE (Γ := [])).eval .nil) :=
  RoCacheRelB192.empty (drKeyT (ℓ := 0) (Pt := Empty)) listCap roCap dfltDrKeyE .nil

private theorem embedVal_drKey (x : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote) :
    embedVal _root_.SignalPqxdh.LegacyCosted.drKeyT x = x := by
  rcases x with ⟨_, _, _⟩; rfl

private theorem embedVal_roList (l : roListLegacyTy.denote) :
    embedVal roListLegacyTy l = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨_, _, _, _⟩; exact congrArg _ ih

private theorem embedVal_roPair
    (p : (Ty.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy).denote) :
    embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) p = p := by
  rcases p with ⟨dk, l⟩
  exact Prod.ext (embedVal_drKey dk) (embedVal_roList l)

private theorem sampleDrKey96AtomicC_eval_eq {ι : Type} {T : OracleSpec ι}
    (A : AtomicIface T) {Γ : List (Ty pqAtomicSig)} (ρ : Env Γ) :
    (sampleDrKey96AtomicC (I := A.toIface) rfl).eval ρ = (mapSamp A .drKey96).eval ρ := by
  simp only [sampleDrKey96AtomicC, samplePbytes32C, mapSamp, Comp.eval, Expr.eval, Env.get,
    Expr.v0, Expr.v1, Expr.v2, _root_.Computational.Proofs.SignalPqxdh.AtomicLift.aop,
    _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.aop,
    bind_assoc, pure_bind]
  rfl

/-- Forgetful simulation and `RoCacheAvlInv` preservation for `roShadowQueryC` against legacy
    `hkdfOrRoC K true` lifted via `mapComp tl`. -/
theorem roShadowQueryC_eval_sim
    {A : AtomicIface _root_.SignalPqxdh.PrimBaseSpec}
    (tl : TagLift _root_.SignalPqxdh.LegacyCosted.pqPrimIface A)
    {Γ : List (Ty pqAtomicSig)} (env : Env Γ)
    (K roCap : ℕ)
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192))
    (stLegacy : keyIndStateTy.denote)
    (hUnsupported :
      (hkdfOrRoC K true
        (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        .zero (.var (.succ .zero))).queries tl.unsupportedW (fun _ => 0) = 0)
    (hRoEq : roListE.eval env = embedVal roListLegacyTy (stRoList stLegacy))
    (hInv : RoCacheAvlInv K roCap (roListE.eval env) (tblE.eval env))
    (hLtK : (roListE.eval env).length < K)
    (hRoom : (roListE.eval env).length + 1 ≤ roCap) :
    Prod.map id Prod.fst <$>
        (roShadowQueryC tl roCap roListE tblE secE).eval env =
      (mapComp tl (hkdfOrRoC K true
        (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        .zero (.var (.succ .zero)))).eval
        (.cons (embedVal keyIndStateTy stLegacy) (.cons (secE.eval env) .nil)) ∧
    ∀ out ∈ support ((roShadowQueryC tl roCap roListE tblE secE).eval env),
      RoCacheAvlInv K roCap out.2.1 out.2.2 ∧
      out.2.1.length ≤ (roListE.eval env).length + 1 := by
  set roList := roListE.eval env
  set tbl := tblE.eval env
  set sec := secE.eval env
  have hRoLegacy : stRoList stLegacy = roList := by
    rw [hRoEq, embedVal_roList]
  have hTake : (stRoList stLegacy).take K = roList := by
    rw [hRoLegacy]
    exact List.take_of_length_le (Nat.le_of_lt hLtK)
  let ρ₁ : Env (.prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ) :=
    .cons (roList, (tbl, (sec, CryptoVerification.E2E.ofU8 sec))) env
  obtain ⟨path, hSearch, hIns⟩ :=
    RoCacheRelB192.search_and_insert_spec (I := A.toIface)
      (.fst (.snd .v0)) (.snd (.snd (.snd .v0))) ρ₁ sec rfl hInv
  have hRhs :
      (mapComp tl (hkdfOrRoC K true
        (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        .zero (.var (.succ .zero)))).eval
        (.cons (embedVal keyIndStateTy stLegacy) (.cons sec .nil)) =
      (hkdfOrRoC K true
        (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
        .zero (.var (.succ .zero))).eval (.cons stLegacy (.cons sec .nil)) := by
    have hMC := mapComp_eval tl (hkdfOrRoC K true
      (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
      (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
      .zero (.var (.succ .zero))) hUnsupported (.cons stLegacy (.cons sec .nil))
    have hId : embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) = id :=
      funext embedVal_roPair
    let ρLeg : Env [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192] :=
      .cons stLegacy (.cons sec .nil)
    change (mapComp tl _).eval (embedEnv ρLeg) = _
    rw [hMC, hId, id_map]
  let hitNone : (Ty.prod (.opt (drKeyT (ℓ := 0) (Pt := Empty)))
      (.list _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlPathItemTy)).denote :=
    (none, path)
  have hLhsEval :
      (roShadowQueryC tl roCap roListE tblE secE).eval env =
      match (roList.find? (fun p => p.1 == sec)).map Prod.snd with
      | none =>
        (sampleDrKey96AtomicC (I := A.toIface) rfl (Γ := _)).eval
          (.cons hitNone ρ₁) >>= fun dk =>
          (avlInsertAtPathC (I := A.toIface) roCap
            (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0).eval
            (.cons dk (.cons hitNone ρ₁)) >>= fun tbl' =>
            pure (dk, ((sec, dk) :: roList, tbl'))
      | some dk => pure (dk, (roList, tbl)) := by
    simp only [roShadowQueryC,
      _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.aop,
      Comp.eval, Expr.eval, pure_bind]
    change (avlSearchB192C (I := A.toIface) roCap
      (.fst (.snd .v0)) (.snd (.snd (.snd .v0)))).eval ρ₁ >>= _ = _
    rw [hSearch, pure_bind]
    cases (roList.find? (fun p => p.1 == sec)).map Prod.snd <;> rfl
  refine ⟨?_, ?_⟩
  · rw [hLhsEval, hRhs]
    simp only [hkdfOrRoC, letV, caseOptV, bindV, ↓reduceIte, Comp.eval, pure_bind]
    let ρLeg : Env [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192] :=
      .cons stLegacy (.cons sec .nil)
    have hFindEq :
        (eFind K (stRo (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v
            (.zero : Var [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192] keyIndStateTy)))
          fun e => eqB (.fst (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v e))
            (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v
              (.zero : Var (_root_.SignalPqxdh.LegacyCosted.B 192 ::
                [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
                (_root_.SignalPqxdh.LegacyCosted.B 192)))).eval
          (.cons ((Expr.var (.succ .zero) :
              Expr pqxdhOps [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192]
                (_root_.SignalPqxdh.LegacyCosted.B 192)).eval ρLeg) ρLeg) =
        roList.find? (fun p => p.1 == sec) := by
      simp only [eFind, stRo, eqB, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v,
        Expr.eval, Env.get, ρLeg]
      change List.find? (fun x => x.1 == sec) ((stRoList stLegacy).take K) = _
      rw [hTake]
    dsimp only [ρLeg] at hFindEq
    rw [hFindEq]
    cases hF : roList.find? (fun p => p.1 == sec) with
    | some p =>
      rcases p with ⟨k, dk⟩
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v, Option.map_some,
        map_pure, Expr.eval, Env.get]
      rw [← hRoLegacy]
      rfl
    | none =>
      simp only [Option.map_none, map_bind]
      rw [sampleDrKey96AtomicC_eval_eq, mapSamp_eval tl.hfwd .drKey96]
      have hDrId : embedVal (_root_.SignalPqxdh.LegacyCosted.PSamp.drKey96.ty) = id :=
        funext embedVal_drKey
      rw [hDrId, id_map]
      simp only [sDrKey96, Comp.eval]
      congr 1; funext dk
      obtain ⟨tbl', hInsEval, _⟩ := hIns (by simp [hF]) hLtK hRoom dk
      have hIns' : (avlInsertAtPathC (I := A.toIface) roCap
          (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0).eval
          (.cons dk (.cons hitNone ρ₁)) = pure tbl' := by
        rw [avlInsertAtPathC_eval_congr (I := A.toIface) roCap
          (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0
          (.cons dk (.cons hitNone ρ₁))]
        simpa only [Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v2, ρ₁, hitNone] using hInsEval
      rw [hIns', pure_bind, map_pure]
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v, Expr.eval, Env.get]
      rw [← hRoLegacy]
      rfl
  · intro out hOut
    rw [hLhsEval] at hOut
    cases hF : roList.find? (fun p => p.1 == sec) with
    | some p =>
      rcases p with ⟨k, dk⟩
      simp only [hF, Option.map_some, support_pure, Set.mem_singleton_iff] at hOut
      subst hOut
      exact ⟨hInv, Nat.le_succ _⟩
    | none =>
      simp only [hF, Option.map_none, MonadAttach.mem_support_bind] at hOut
      rcases hOut with ⟨dk, _, tbl', hTblMem, hOutMem⟩
      obtain ⟨tbl'', hInsEval, hRel'⟩ := hIns (by simp [hF]) hLtK hRoom dk
      have hIns' : (avlInsertAtPathC (I := A.toIface) roCap
          (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0).eval
          (.cons dk (.cons hitNone ρ₁)) = pure tbl'' := by
        rw [avlInsertAtPathC_eval_congr (I := A.toIface) roCap
          (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0
          (.cons dk (.cons hitNone ρ₁))]
        simpa only [Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v2, ρ₁, hitNone] using hInsEval
      rw [hIns', support_pure, Set.mem_singleton_iff] at hTblMem
      subst hTblMem
      simp only [support_pure, Set.mem_singleton_iff] at hOutMem
      subst hOutMem
      exact ⟨hRel', Nat.le_refl _⟩

/-- Shared `KeyIndCore` state invariant combining `BaseOnlineLenInv`, `stRo` length bound, and `RoCacheAvlInv`. -/
structure CoreInv (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (sK : keyIndStateKTy.denote) : Prop where
  online_len : BaseOnlineLenInv c (projVal keyIndStateTy sK.1)
  ro_len     : (stRoList (projVal keyIndStateTy sK.1)).length ≤ c 2
  ro_avl     : RoCacheAvlInv (keyIndLoopBound b) (keyIndCoreFuels S b).roCap
                 (embedVal roListLegacyTy (stRoList (projVal keyIndStateTy sK.1))) sK.2

/-- Between-query state invariant for two-stage `KemShCr` step simulation. -/
structure ShcrSimInv (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (sK : shcrKindStTy.denote) : Prop where
  core_inv : CoreInv S b c (sK.1.1, sK.2)
  cnt_le   : (projVal shcrStTy sK.1).2.2.2.2.1 ≤ c 0
  ir_le    : (projVal shcrStTy sK.1).2.2.2.2.2.1.length ≤ c 0
  rr_le    : (projVal shcrStTy sK.1).2.2.2.2.2.2.1.length ≤ c 0

/-- Pause-point invariant for two-stage `KemShCr`, reserving `+ 1` headroom on `stSess`, `stRo`,
    `scCnt`, and `scIR` after `bumpPred` increments `c 0` and `c 2`. -/
structure ShcrPauseInv (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (_pK : (embedTy pauseTy).denote) (sK : shcrKindStTy.denote) : Prop where
  online_len : BaseOnlineLenInv c (projVal keyIndStateTy sK.1.1)
  sess_room  : (stSessList (projVal keyIndStateTy sK.1.1)).length + 1 ≤ c 0
  ro_room    : (stRoList (projVal keyIndStateTy sK.1.1)).length + 1 ≤ c 2
  ro_avl     : RoCacheAvlInv (keyIndLoopBound b) (keyIndCoreFuels S b).roCap
                 (embedVal roListLegacyTy (stRoList (projVal keyIndStateTy sK.1.1))) sK.2
  cnt_room   : (projVal shcrStTy sK.1).2.2.2.2.1 + 1 ≤ c 0
  ir_room    : (projVal shcrStTy sK.1).2.2.2.2.2.1.length + 1 ≤ c 0
  rr_le      : (projVal shcrStTy sK.1).2.2.2.2.2.2.1.length ≤ c 0

private theorem compRename_wkRen1_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ' : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig}
    (c : Comp pqAtomicOps I (A :: Γ') R) (x : A.denote) (y : B.denote) (ρ : Env Γ') :
    (compRename _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK.wkRen1 c).eval
        (.cons x (.cons y ρ)) =
      c.eval (.cons x ρ) := by
  refine compRename_eval c _ (.cons x ρ) (.cons x (.cons y ρ)) ?_
  intro a v
  cases v <;> rfl

/-- Evaluates 14-way `dispatchKeyIndQ` on an encoded query `(pqKeyIndCodec S).qenc t`. -/
theorem dispatchKeyIndQ_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {σ R : Ty pqAtomicSig} (S : Setup)
    (armInitPrin : Comp pqAtomicOps I [.base (.fin S.N_id), σ, (pqKeyIndCodec S).Q] R)
    (armCorruptIK : Comp pqAtomicOps I [.base (.fin S.N_id), σ, (pqKeyIndCodec S).Q] R)
    (armGenSPK :
      Comp pqAtomicOps I
        [.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)), σ, (pqKeyIndCodec S).Q] R)
    (armGenOPK :
      Comp pqAtomicOps I
        [.prod (.base (.fin S.N_id)) (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))),
         σ, (pqKeyIndCodec S).Q] R)
    (armInitOPK :
      Comp pqAtomicOps I
        [.prod (.base (.fin S.N_id))
           (.prod (.base (.fin S.N_send_opk)) (bundleT (ℓ := 0) (Pt := Empty))),
         σ, (pqKeyIndCodec S).Q] R)
    (armInitNoOPK :
      Comp pqAtomicOps I
        [.prod (.base (.fin S.N_id))
           (.prod (.base (.fin S.N_send_no_opk)) (bundleT (ℓ := 0) (Pt := Empty))),
         σ, (pqKeyIndCodec S).Q] R)
    (armAccOPK :
      Comp pqAtomicOps I
        [.prod (.base (.fin S.N_id))
           (.prod (.base (.fin S.N_recv))
             (.prod (.base (.fin S.N_opk)) (hdrT (ℓ := 0) (Pt := Empty)))),
         σ, (pqKeyIndCodec S).Q] R)
    (armAccNoOPK :
      Comp pqAtomicOps I
        [.prod (.base (.fin S.N_id))
           (.prod (.base (.fin S.N_recv))
             (.prod (.base (.fin S.N_no_opk)) (hdrT (ℓ := 0) (Pt := Empty)))),
         σ, (pqKeyIndCodec S).Q] R)
    (armTest : Comp pqAtomicOps I [sidT (ℓ := 0) (Pt := Empty) S, σ, (pqKeyIndCodec S).Q] R)
    (armRo : Comp pqAtomicOps I [PB 192, σ, (pqKeyIndCodec S).Q] R)
    (armRevDh : Comp pqAtomicOps I [.unit, σ, (pqKeyIndCodec S).Q] R)
    (armRevSess : Comp pqAtomicOps I [sidT (ℓ := 0) (Pt := Empty) S, σ, (pqKeyIndCodec S).Q] R)
    (armRegKey : Comp pqAtomicOps I [PB 32, σ, (pqKeyIndCodec S).Q] R)
    (armRevSpk :
      Comp pqAtomicOps I
        [.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)), σ, (pqKeyIndCodec S).Q] R)
    (s : σ.denote) (t : KeyIndQuery S) :
    (dispatchKeyIndQ S .v1
      armInitPrin armCorruptIK armGenSPK armGenOPK
      armInitOPK armInitNoOPK armAccOPK armAccNoOPK
      armTest armRo armRevDh armRevSess armRegKey armRevSpk).eval
      (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
    match t with
    | .initPrin u =>
        armInitPrin.eval (.cons u (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .corruptIK u =>
        armCorruptIK.eval (.cons u (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .genSPK u j =>
        armGenSPK.eval (.cons (u, j) (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .genOPK u j o =>
        armGenOPK.eval (.cons (u, (j, o)) (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .initiateOPK u i bu =>
        armInitOPK.eval
          (.cons (u, (i, bundleV bu)) (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .initiateNoOPK u i bu =>
        armInitNoOPK.eval
          (.cons (u, (i, bundleV bu)) (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .acceptOPK k j o hdr =>
        armAccOPK.eval
          (.cons (k, (j, (o, hdrV hdr))) (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .acceptNoOPK k j l hdr =>
        armAccNoOPK.eval
          (.cons (k, (j, (l, hdrV hdr))) (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .testSession sid =>
        armTest.eval (.cons (sidV sid) (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .roQuery sec =>
        armRo.eval (.cons sec (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .revealDhSecrets =>
        armRevDh.eval (.cons () (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .revealSessionKey sid =>
        armRevSess.eval (.cons (sidV sid) (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .registerKey sk =>
        armRegKey.eval (.cons sk (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)))
    | .revealSpkSk u j =>
        armRevSpk.eval (.cons (u, j) (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil))) := by
  cases t <;>
    simp [dispatchKeyIndQ, pqKeyIndCodec, ReductionDsl.keyIndCodec, ReductionDsl.keyIndQenc,
      Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, compRename_wkRen1_eval]

@[simp] theorem runAt2_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (c : Comp pqAtomicOps I [A, B] R) (env : Env Γ) :
    (runAt2 aE bE c).eval env = c.eval (.cons (aE.eval env) (.cons (bE.eval env) .nil)) := by
  simp only [runAt2, Comp.eval, pure_bind]
  have ha := exprRename_eval aE (fun {a} => Var.succ) env (.cons (bE.eval env) env) (fun _ => rfl)
  rw [ha]
  refine compRename_eval c _ _ _ fun v => ?_
  match v with
  | .zero => rfl
  | .succ .zero => rfl

@[simp] theorem runAt3_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (m : Comp pqAtomicOps I [A, B, C] R) (env : Env Γ) :
    (runAt3 aE bE cE m).eval env =
      m.eval (.cons (aE.eval env) (.cons (bE.eval env) (.cons (cE.eval env) .nil))) := by
  simp only [runAt3, Comp.eval, pure_bind]
  have hb := exprRename_eval bE (fun {a} => Var.succ) env (.cons (cE.eval env) env) (fun _ => rfl)
  rw [hb]
  have ha := exprRename_eval aE (fun {a} v => v.succ.succ) env
    (.cons (bE.eval env) (.cons (cE.eval env) env)) (fun _ => rfl)
  rw [ha]
  refine compRename_eval m _ _ _ fun v => ?_
  match v with
  | .zero | .succ .zero | .succ (.succ .zero) => rfl

@[simp] theorem runAt4_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (cE : Expr pqAtomicOps Γ C) (dE : Expr pqAtomicOps Γ D)
    (m : Comp pqAtomicOps I [A, B, C, D] R) (env : Env Γ) :
    (runAt4 aE bE cE dE m).eval env =
      m.eval (.cons (aE.eval env) (.cons (bE.eval env)
        (.cons (cE.eval env) (.cons (dE.eval env) .nil)))) := by
  simp only [runAt4, Comp.eval, pure_bind]
  have hc := exprRename_eval cE (fun {a} => Var.succ) env (.cons (dE.eval env) env) (fun _ => rfl)
  rw [hc]
  have hb := exprRename_eval bE (fun {a} v => v.succ.succ) env
    (.cons (cE.eval env) (.cons (dE.eval env) env)) (fun _ => rfl)
  rw [hb]
  have ha := exprRename_eval aE (fun {a} v => v.succ.succ.succ) env
    (.cons (bE.eval env) (.cons (cE.eval env) (.cons (dE.eval env) env))) (fun _ => rfl)
  rw [ha]
  refine compRename_eval m _ _ _ fun v => ?_
  match v with
  | .zero | .succ .zero | .succ (.succ .zero) | .succ (.succ (.succ .zero)) => rfl

@[simp] theorem runAt5_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D E R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (cE : Expr pqAtomicOps Γ C) (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E)
    (m : Comp pqAtomicOps I [A, B, C, D, E] R) (env : Env Γ) :
    (runAt5 aE bE cE dE eE m).eval env =
      m.eval (.cons (aE.eval env) (.cons (bE.eval env) (.cons (cE.eval env)
        (.cons (dE.eval env) (.cons (eE.eval env) .nil))))) := by
  simp only [runAt5, Comp.eval, pure_bind]
  have hd := exprRename_eval dE (fun {a} => Var.succ) env (.cons (eE.eval env) env) (fun _ => rfl)
  rw [hd]
  have hc := exprRename_eval cE (fun {a} v => v.succ.succ) env
    (.cons (dE.eval env) (.cons (eE.eval env) env)) (fun _ => rfl)
  rw [hc]
  have hb := exprRename_eval bE (fun {a} v => v.succ.succ.succ) env
    (.cons (cE.eval env) (.cons (dE.eval env) (.cons (eE.eval env) env))) (fun _ => rfl)
  rw [hb]
  have ha := exprRename_eval aE (fun {a} v => v.succ.succ.succ.succ) env
    (.cons (bE.eval env) (.cons (cE.eval env) (.cons (dE.eval env) (.cons (eE.eval env) env))))
    (fun _ => rfl)
  rw [ha]
  refine compRename_eval m _ _ _ fun v => ?_
  match v with
  | .zero | .succ .zero | .succ (.succ .zero)
  | .succ (.succ (.succ .zero)) | .succ (.succ (.succ (.succ .zero))) => rfl

@[simp] theorem runAt6_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D E F R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E) (fE : Expr pqAtomicOps Γ F)
    (m : Comp pqAtomicOps I [A, B, C, D, E, F] R) (env : Env Γ) :
    (runAt6 aE bE cE dE eE fE m).eval env =
      m.eval (.cons (aE.eval env) (.cons (bE.eval env) (.cons (cE.eval env)
        (.cons (dE.eval env) (.cons (eE.eval env) (.cons (fE.eval env) .nil)))))) := by
  simp only [runAt6, Comp.eval, pure_bind]
  have he := exprRename_eval eE (fun {a} => Var.succ) env (.cons (fE.eval env) env) (fun _ => rfl)
  rw [he]
  have hd := exprRename_eval dE (fun {a} v => v.succ.succ) env
    (.cons (eE.eval env) (.cons (fE.eval env) env)) (fun _ => rfl)
  rw [hd]
  have hc := exprRename_eval cE (fun {a} v => v.succ.succ.succ) env
    (.cons (dE.eval env) (.cons (eE.eval env) (.cons (fE.eval env) env))) (fun _ => rfl)
  rw [hc]
  have hb := exprRename_eval bE (fun {a} v => v.succ.succ.succ.succ) env
    (.cons (cE.eval env) (.cons (dE.eval env) (.cons (eE.eval env) (.cons (fE.eval env) env))))
    (fun _ => rfl)
  rw [hb]
  have ha := exprRename_eval aE (fun {a} v => v.succ.succ.succ.succ.succ) env
    (.cons (bE.eval env) (.cons (cE.eval env) (.cons (dE.eval env)
      (.cons (eE.eval env) (.cons (fE.eval env) env))))) (fun _ => rfl)
  rw [ha]
  refine compRename_eval m _ _ _ fun v => ?_
  match v with
  | .zero | .succ .zero | .succ (.succ .zero) | .succ (.succ (.succ .zero))
  | .succ (.succ (.succ (.succ .zero))) | .succ (.succ (.succ (.succ (.succ .zero)))) => rfl

section FuelIdentity

@[simp] private theorem v_eval_cons {Γ Δ : List PT} {σ τ : PT} [Ext Γ Δ]
    (x : Var Γ τ) (a : σ.denote) (env : Env Δ) :
    (@_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v Γ (σ :: Δ) τ Ext.step x).eval
        (.cons a env) =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v x).eval env := rfl

@[simp] private theorem v_zero_eval {Γ : List PT} {τ : PT} (a : τ.denote) (env : Env Γ) :
    (@_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v (τ :: Γ) (τ :: Γ) τ Ext.refl .zero).eval
        (.cons a env) = a := rfl

private theorem eFind_eq_of_le {Γ : List PT} {τ : PT} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eFind K₁ xs p).eval env = (eFind K₂ xs p).eval env := by
  simp only [eFind, Expr.eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

private theorem eAny_eq_of_le {Γ : List PT} {τ : PT} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eAny K₁ xs p).eval env = (eAny K₂ xs p).eval env := by
  simp only [eAny, Expr.eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

private theorem eMap_eq_of_le {Γ : List PT} {τ₁ τ₂ : PT} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eMap K₁ xs f).eval env = (eMap K₂ xs f).eval env := by
  simp only [eMap, Expr.eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

private theorem findMV_min_eq_of_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ : PT} {K₁ K₂ N : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (findMV (min K₁ N) xs p).eval env = (findMV (min K₂ N) xs p).eval env := by
  simp only [findMV, Comp.eval, take_min_eq_of_length_le (xs.eval env) hLen hLe]

private theorem anyMV_min_eq_of_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ : PT} {K₁ K₂ N : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (anyMV (min K₁ N) xs p).eval env = (anyMV (min K₂ N) xs p).eval env := by
  simp only [anyMV, Comp.eval, take_min_eq_of_length_le (xs.eval env) hLen hLe]

variable (S : Setup) {K₁ K₂ : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

theorem findHonestC_min_eq (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) (env : Env Δ)
    (hLen : (stPrinList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (findHonestC S K₁ st ik).eval env = (findHonestC S K₂ st ik).eval env := by
  simp only [findHonestC, letV, Comp.eval, pure_bind]
  exact findMV_min_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, Expr.eval] using hLen) hLe

theorem isAdvRegC_min_eq (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (pk : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) (env : Env Δ)
    (hLen : (stAdvList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (isAdvRegC K₁ st pk).eval env = (isAdvRegC K₂ st pk).eval env := by
  simp only [isAdvRegC, bindV, Comp.eval]
  congr 1; funext p
  congr 1
  exact eAny_eq_of_le _ _ _ (by simpa [stAdv, stAdvList, Expr.eval] using hLen) hLe

theorem isGameSpkC_min_eq (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (pk : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) (env : Env Δ)
    (hLen : (stSpksList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (isGameSpkC S K₁ st pk).eval env = (isGameSpkC S K₂ st pk).eval env := by
  simp only [isGameSpkC, letV, Comp.eval, pure_bind]
  exact anyMV_min_eq_of_le _ _ _ (by simpa [stSpks, stSpksList, Expr.eval] using hLen) hLe

theorem isGameOpkC_min_eq (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (pk : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) (env : Env Δ)
    (hLen : (stOpksList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (isGameOpkC S K₁ st pk).eval env = (isGameOpkC S K₂ st pk).eval env := by
  simp only [isGameOpkC, letV, Comp.eval, pure_bind]
  exact anyMV_min_eq_of_le _ _ _ (by simpa [stOpks, stOpksList, Expr.eval] using hLen) hLe

theorem koskBundleOkC_min_eq (st : Var Γ₁ keyIndStateTy)
    (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env))
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (koskBundleOkC S K₁ st bu).eval env = (koskBundleOkC S K₂ st bu).eval env := by
  have hPrin := Nat.le_trans hInv.prin_le hc
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hOpks := Nat.le_trans hInv.opks_le hc
  have hAdv  := Nat.le_trans hInv.adv_le hc
  simp only [koskBundleOkC, bindV, caseOptV, Comp.eval]
  rw [findHonestC_min_eq S st _ env hPrin hLe]
  congr 1; funext f
  rw [isAdvRegC_min_eq st _ _ (by simpa using hAdv) hLe]
  congr 1; funext idA
  rw [isGameSpkC_min_eq S st _ _ (by simpa using hSpks) hLe]
  congr 1; funext spkG
  rw [isAdvRegC_min_eq st _ _ (by simpa using hAdv) hLe]
  congr 1; funext spkA
  cases (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buOpkB
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v bu)).eval
    (.cons spkA (.cons spkG (.cons idA (.cons f env)))) with
  | none => rfl
  | some o =>
    dsimp only
    rw [isGameOpkC_min_eq S st _ _ (by simpa using hOpks) hLe]
    congr 1; funext opkG
    rw [isAdvRegC_min_eq st _ _ (by simpa using hAdv) hLe]

theorem koskSenderOkC_min_eq (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env))
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (koskSenderOkC S K₁ st ik).eval env = (koskSenderOkC S K₂ st ik).eval env := by
  have hPrin := Nat.le_trans hInv.prin_le hc
  have hAdv  := Nat.le_trans hInv.adv_le hc
  simp only [koskSenderOkC, letV, bindV, Comp.eval, pure_bind]
  rw [findHonestC_min_eq S st _ _ (by simpa using hPrin) hLe]
  congr 1; funext f
  rw [isAdvRegC_min_eq st _ _ (by simpa using hAdv) hLe]

theorem resolveSigPkC_min_eq (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) (env : Env Δ)
    (hLen : (stPrinList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (resolveSigPkC S K₁ st ik).eval env = (resolveSigPkC S K₂ st ik).eval env := by
  simp only [resolveSigPkC, letV, bindV, Comp.eval, pure_bind]
  rw [findHonestC_min_eq S st _ _ (by simpa using hLen) hLe]

theorem honestPeerC_min_eq (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32)) (env : Env Δ)
    (hLen : (stPrinList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (honestPeerC S K₁ st ik).eval env = (honestPeerC S K₂ st ik).eval env := by
  simp only [honestPeerC, bindV, Comp.eval]
  rw [findHonestC_min_eq S st _ env hLen hLe]

theorem checkProvC_min_eq (st : Var Γ₁ keyIndStateTy)
    (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env))
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (checkProvC S K₁ st bu).eval env = (checkProvC S K₂ st bu).eval env := by
  have hPrin := Nat.le_trans hInv.prin_le hc
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hOpks := Nat.le_trans hInv.opks_le hc
  simp only [checkProvC, bindV, caseOptV, letV, Comp.eval]
  rw [findHonestC_min_eq S st _ env hPrin hLe]
  congr 1; funext f
  cases f with
  | none => rfl
  | some kE =>
    rw [v_zero_eval]
    dsimp only
    rw [anyMV_min_eq_of_le _ _ _ (by simpa [stSpks, stSpksList, Expr.eval] using hSpks) hLe]
    congr 1; funext spkHon
    rw [eAny_eq_of_le _ _ _ (by simpa [stSpks, stSpksList, Expr.eval] using hSpks) hLe]
    congr 1; funext pqVal
    let someKE : (Ty.opt (Ty.prod .nat
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.principalEntryTy)).denote := some kE
    cases (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buOpkB
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v bu)).eval
      (.cons pqVal (.cons spkHon (.cons kE (.cons someKE env)))) with
    | none => rfl
    | some o =>
      dsimp only
      congr 1
      exact anyMV_min_eq_of_le _ _ _ (by simpa [stOpks, stOpksList, Expr.eval] using hOpks) hLe

theorem recordRespC_min_eq
    (p : Expr pqxdhOps Δ
      (.prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndRespEntryTy keyIndStateTy))
    (env : Env Δ)
    (hLen : (stSessList (p.eval env).2).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (recordRespC S K₁ p).eval env = (recordRespC S K₂ p).eval env := by
  simp only [recordRespC, letV, bindV, Comp.eval, pure_bind]
  rw [findMV_min_eq_of_le _ _ _ (by simpa [stSess, stSessList, Expr.eval] using hLen) hLe]

theorem preCheckC_min_eq (st : Var Γ₁ keyIndStateTy)
    (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (u : Var Γ₃ .nat) (bu : Var Γ₄ _root_.SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env))
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (preCheckC S K₁ st sid u bu).eval env = (preCheckC S K₂ st sid u bu).eval env := by
  have hSess := Nat.le_trans hInv.sess_le hc
  have hPrin := Nat.le_trans hInv.prin_le hc
  simp only [preCheckC, caseOptV, bindV, Comp.eval]
  rw [eAny_eq_of_le _ _ _ (by simpa [stSess, stSessList, Expr.eval] using hSess) hLe]
  split_ifs with hAny
  · rfl
  · rw [eFind_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, Expr.eval] using hPrin) hLe]
    cases (eFind K₂ _ _).eval env with
    | none => rfl
    | some uE =>
      dsimp only
      rw [koskBundleOkC_min_eq S st bu (.cons uE env) (by simpa using hInv) hc hLe]

theorem checkSigsC_min_eq (st : Var Γ₁ keyIndStateTy)
    (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ)
    (hLen : (stPrinList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (checkSigsC S K₁ st bu).eval env = (checkSigsC S K₂ st bu).eval env := by
  simp only [checkSigsC, bindV, Comp.eval]
  rw [resolveSigPkC_min_eq S st _ env hLen hLe]

theorem freshE_min_eq (st : Expr pqxdhOps Δ keyIndStateTy)
    (sid : Expr pqxdhOps Δ _root_.SignalPqxdh.LegacyCosted.sidT) (env : Env Δ)
    {c : Fin 3 → ℕ} (hInv : BaseOnlineLenInv c (st.eval env)) (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (freshE K₁ st sid).eval env = (freshE K₂ st sid).eval env := by
  have hSess  := Nat.le_trans hInv.sess_le hc
  have hResps := Nat.le_trans hInv.resps_le hc
  simp only [freshE, eLet2, eLet, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
    eFind, stSess, stResps, Expr.eval, v_eval_cons, v_zero_eval]
  rw [List.take_of_length_le (by simpa [stSessList] using hSess),
    List.take_of_length_le (Nat.le_trans (by simpa [stSessList] using hSess) hLe),
    List.take_of_length_le (by simpa [stRespsList] using hResps),
    List.take_of_length_le (Nat.le_trans (by simpa [stRespsList] using hResps) hLe)]

theorem kyberCheckE_min_eq
    (used : Expr pqxdhOps Δ (.list (.prod .nat (.prod _root_.SignalPqxdh.LegacyCosted.U32
      (.prod _root_.SignalPqxdh.LegacyCosted.U32 (_root_.SignalPqxdh.LegacyCosted.B 32))))))
    (entry : Expr pqxdhOps Δ (.prod .nat (.prod _root_.SignalPqxdh.LegacyCosted.U32
      (.prod _root_.SignalPqxdh.LegacyCosted.U32 (_root_.SignalPqxdh.LegacyCosted.B 32)))))
    (env : Env Δ)
    (hLen : (used.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (kyberCheckE K₁ used entry).eval env = (kyberCheckE K₂ used entry).eval env := by
  simp only [kyberCheckE, eLet2, eLet, eAny, Expr.eval, v_eval_cons, v_zero_eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

theorem initPrin1KeyB_min_eq (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ)
    (hLen : (stPrinList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (initPrin1KeyB K₁ st u).eval env = (initPrin1KeyB K₂ st u).eval env := by
  simp only [initPrin1KeyB, Comp.eval]
  rw [eAny_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, Expr.eval] using hLen) hLe]

theorem initPrinB_min_eq (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ)
    (hLen : (stPrinList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (initPrinB K₁ st u).eval env = (initPrinB K₂ st u).eval env := by
  simp only [initPrinB, Comp.eval]
  rw [eAny_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, Expr.eval] using hLen) hLe]

theorem corruptB_min_eq (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ)
    (hLen : (stPrinList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (corruptB K₁ st u).eval env = (corruptB K₂ st u).eval env := by
  simp only [corruptB, caseOptV, Comp.eval]
  rw [eFind_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, Expr.eval] using hLen) hLe]
  cases (eFind K₂ _ _).eval env with
  | none => rfl
  | some e =>
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUpd, Expr.eval]
    congr 4
    exact eMap_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, Expr.eval] using hLen) hLe

theorem genSpkB_min_eq (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env))
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (genSpkB K₁ st x).eval env = (genSpkB K₂ st x).eval env := by
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hPrin := Nat.le_trans hInv.prin_le hc
  simp only [genSpkB, caseOptV, Comp.eval]
  rw [eAny_eq_of_le _ _ _ (by simpa [stSpks, stSpksList, Expr.eval] using hSpks) hLe,
    eFind_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, Expr.eval] using hPrin) hLe]

theorem genOpkB_min_eq (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hLen : (stOpksList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (genOpkB K₁ st x).eval env = (genOpkB K₂ st x).eval env := by
  simp only [genOpkB, Comp.eval]
  rw [eAny_eq_of_le _ _ _ (by simpa [stOpks, stOpksList, Expr.eval] using hLen) hLe]

theorem testB_min_eq (st : Var Γ₁ keyIndStateTy)
    (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env))
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (testB K₁ st sid).eval env = (testB K₂ st sid).eval env := by
  have hSess  := Nat.le_trans hInv.sess_le hc
  have hResps := Nat.le_trans hInv.resps_le hc
  have hFr := freshE_min_eq (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st)
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v sid) env hInv hc hLe
  simp only [testB, caseOptV, Comp.eval]
  have hNotEq : (Expr.not (freshE K₁ (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st)
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v sid))).eval env =
    (Expr.not (freshE K₂ (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st)
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v sid))).eval env := by
    simp only [Expr.eval, hFr]
  rw [hNotEq]
  split_ifs with hNot
  · rfl
  · rw [eFind_eq_of_le _ _ _ (by simpa [stSess, stSessList, Expr.eval] using hSess) hLe]
    cases (eFind K₂ _ _).eval env with
    | none =>
      rw [eFind_eq_of_le _ _ _ (by simpa [stResps, stRespsList, Expr.eval] using hResps) hLe]
      cases (eFind K₂ _ _).eval env with
      | none => rfl
      | some r =>
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUpd, eMap, stResps, Expr.eval]
        rw [List.take_of_length_le (by simpa [stRespsList, Expr.eval] using hResps),
          List.take_of_length_le (Nat.le_trans (by simpa [stRespsList, Expr.eval] using hResps) hLe)]
    | some e =>
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUpd, eMap, stSess, Expr.eval]
      rw [List.take_of_length_le (by simpa [stSessList, Expr.eval] using hSess),
        List.take_of_length_le (Nat.le_trans (by simpa [stSessList, Expr.eval] using hSess) hLe)]

theorem revealB_min_eq (st : Var Γ₁ keyIndStateTy)
    (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env))
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (revealB K₁ st sid).eval env = (revealB K₂ st sid).eval env := by
  have hSess  := Nat.le_trans hInv.sess_le hc
  have hResps := Nat.le_trans hInv.resps_le hc
  simp only [revealB, caseOptV, Comp.eval]
  rw [eFind_eq_of_le _ _ _ (by simpa [stSess, stSessList, Expr.eval] using hSess) hLe]
  cases (eFind K₂ _ _).eval env with
  | none =>
    rw [eFind_eq_of_le _ _ _ (by simpa [stResps, stRespsList, Expr.eval] using hResps) hLe]
    cases (eFind K₂ _ _).eval env with
    | none => rfl
    | some r =>
      dsimp only
      split_ifs with hT
      · rfl
      · simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUpd, eMap, stResps, Expr.eval]
        rw [List.take_of_length_le (by simpa [stRespsList, Expr.eval] using hResps),
          List.take_of_length_le (Nat.le_trans (by simpa [stRespsList, Expr.eval] using hResps) hLe)]
  | some e =>
    dsimp only
    split_ifs with hT
    · rfl
    · simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUpd, eMap, stSess, Expr.eval]
      rw [List.take_of_length_le (by simpa [stSessList, Expr.eval] using hSess),
        List.take_of_length_le (Nat.le_trans (by simpa [stSessList, Expr.eval] using hSess) hLe)]

theorem revealDhB_min_eq (useRo : Bool) (st : Var Γ₁ keyIndStateTy) [Ext Γ₁ Δ]
    (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env))
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (revealDhB useRo K₁ st).eval env = (revealDhB useRo K₂ st).eval env := by
  have hPrin := Nat.le_trans hInv.prin_le hc
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hOpks := Nat.le_trans hInv.opks_le hc
  have hSess := Nat.le_trans hInv.sess_le hc
  cases useRo
  · simp only [revealDhB, Bool.false_eq_true, ↓reduceIte, Comp.eval,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rDh, eMap,
      stPrin, stSpks, stOpks, stSess, Expr.eval]
    rw [List.take_of_length_le (by simpa [stPrinList, Expr.eval] using hPrin),
      List.take_of_length_le (Nat.le_trans (by simpa [stPrinList, Expr.eval] using hPrin) hLe),
      List.take_of_length_le (by simpa [stSpksList, Expr.eval] using hSpks),
      List.take_of_length_le (Nat.le_trans (by simpa [stSpksList, Expr.eval] using hSpks) hLe),
      List.take_of_length_le (by simpa [stOpksList, Expr.eval] using hOpks),
      List.take_of_length_le (Nat.le_trans (by simpa [stOpksList, Expr.eval] using hOpks) hLe),
      List.take_of_length_le (by simpa [stSessList, Expr.eval] using hSess),
      List.take_of_length_le (Nat.le_trans (by simpa [stSessList, Expr.eval] using hSess) hLe)]
  · rfl

theorem revealSpkB_min_eq (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hLen : (stSpksList ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v st).eval env)).length ≤ K₁)
    (hLe : K₁ ≤ K₂) :
    (revealSpkB K₁ st x).eval env = (revealSpkB K₂ st x).eval env := by
  simp only [revealSpkB, caseOptV, Comp.eval]
  rw [eFind_eq_of_le _ _ _ (by simpa [stSpks, stSpksList, Expr.eval] using hLen) hLe]
  cases (eFind K₂ _ _).eval env with
  | none => rfl
  | some bE =>
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUpd, eMap, stSpks, Expr.eval]
    rw [List.take_of_length_le (by simpa [stSpksList, Expr.eval] using hLen),
      List.take_of_length_le (Nat.le_trans (by simpa [stSpksList, Expr.eval] using hLen) hLe)]

theorem shcrGenSpkB_min_eq (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v s).eval env).1)
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (shcrGenSpkB S K₁ s x).eval env = (shcrGenSpkB S K₂ s x).eval env := by
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hPrin := Nat.le_trans hInv.prin_le hc
  simp only [shcrGenSpkB, caseOptV, Comp.eval]
  cases (scTB (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v s)).eval env with
  | none =>
    simp only [onBase, letV, bindV, Comp.eval, pure_bind]
    rw [genSpkB_min_eq .zero x _ (by simpa [scBase, Expr.eval] using hInv) hc hLe]
  | some bIdx =>
    dsimp only
    have hGen : (onBase s fun g => genSpkB K₁ g x).eval (.cons bIdx env) =
        (onBase s fun g => genSpkB K₂ g x).eval (.cons bIdx env) := by
      simp only [onBase, letV, bindV, Comp.eval, pure_bind]
      rw [genSpkB_min_eq .zero x _ (by simpa [scBase, Expr.eval] using hInv) hc hLe]
    rw [hGen,
      eAny_eq_of_le _ _ _ (by simpa [stSpks, stSpksList, scBase, Expr.eval] using hSpks) hLe,
      eFind_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, scBase, Expr.eval] using hPrin) hLe]

theorem shcrActiveGenSpkLeg_min_eq (env : Env [shcrStTy, .prod .nat .nat]) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c (env.get .zero).1)
    (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (shcrActiveGenSpkLeg S K₁).eval env = (shcrActiveGenSpkLeg S K₂).eval env := by
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hPrin := Nat.le_trans hInv.prin_le hc
  simp only [shcrActiveGenSpkLeg, caseOptV, Comp.eval]
  cases (scTB (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v
      (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy))).eval env with
  | none =>
    simp only [onBase, letV, bindV, Comp.eval, pure_bind]
    rw [genSpkB_min_eq .zero (.succ .zero : Var [shcrStTy, .prod .nat .nat] (.prod .nat .nat)) _
      (by simpa [scBase, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v] using hInv)
      hc hLe]
  | some spkOrd =>
    dsimp only
    rw [eAny_eq_of_le _ _ _
      (by simpa [stSpks, stSpksList, scBase, Expr.eval,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v] using hSpks) hLe,
      eFind_eq_of_le _ _ _
        (by simpa [stPrin, stPrinList, scBase, Expr.eval,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v] using hPrin) hLe]
    congr 1
    cases (eFind K₂ _ _).eval (.cons spkOrd env) with
    | none => rfl
    | some uE =>
      dsimp only
      have hGen : (onBase (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy) fun g =>
          genSpkB K₁ g (.succ .zero : Var [shcrStTy, .prod .nat .nat] (.prod .nat .nat))).eval
            (.cons uE (.cons spkOrd env)) =
        (onBase (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy) fun g =>
          genSpkB K₂ g (.succ .zero : Var [shcrStTy, .prod .nat .nat] (.prod .nat .nat))).eval
            (.cons uE (.cons spkOrd env)) := by
        simp only [onBase, letV, bindV, Comp.eval, pure_bind]
        rw [genSpkB_min_eq .zero
          (.succ .zero : Var [shcrStTy, .prod .nat .nat] (.prod .nat .nat)) _
          (by simpa [scBase, Expr.eval,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v] using hInv) hc hLe]
      rw [hGen]

end FuelIdentity

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase
