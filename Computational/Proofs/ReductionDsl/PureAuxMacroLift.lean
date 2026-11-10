/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import Computational.Proofs.ReductionDsl.MacroLift
public import Computational.Proofs.CryptoGames.CKA.CKAProofDefs
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRNG.PRNGProofDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
import Computational.Proofs.GameHop.StateSim
import VCVio.EvalDist.Monad.Bool

/-!
# Auxiliary-Context Pure Macro Compiler, `CoinSimEquiv`, and Weighted Cost

Defines distributional equivalence (`CoinSimEquiv`) across coin-forwarding challengers and
`CostedReduction` simulators, a pure-`Expr` operator macro compiler (`PureAuxBundle`,
`compilePureAuxRed`) threading a read-only auxiliary context `aux : auxT.denote`, and parameterized
AST cost functions (`exprCostW`, `compCostW`).
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp GameCodec CostedReduction
  handlerImpl bits iterM findML anyML mapML consumeFirstML foldML
  atomicSig AtomicPureOp AtomicUnifBase atomicSamplers atomicFig8Ops
  B U64 BV128 toLEBytes bytesToWordLE)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal mapCtx mapVarAux auxVar mapEnvAux
  get_mapEnvAux get_auxVar callMacroAux callMacroAux_cost callMacroAux_size callMacroAux_queries
  callMacroAux_eval)
open Computational.Proofs.GameHop.Rnd (equivBitVecSplit evalDistEq_uniformSample_equiv
  evalDistEq_marginal_snd_of_bijective)
open CryptoGames (CKAScheme PRFPRNG FSAEADScheme MACScheme WireAEAD AEADScheme)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.E2E (Bytes)

namespace Computational.Proofs.ReductionDsl.PureAuxMacroLift

/-! ## `ValidCoinSim`, `CoinSimEquiv`, and challenger congruences -/

section CoinSim

/-- A stateful challenger or simulator `impl : QueryImpl T (StateT σ ProbComp)` interprets `fwdU`
as fresh uniform coins in `ProbComp`. -/
structure ValidCoinSim {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {σ : Type} (impl : QueryImpl T (StateT σ ProbComp)) : Prop where
  coin_eq : ∀ (n : ℕ) (s : σ),
    (simulateQ impl (fwdU n)).run s =ᵈ
      ((query (m := ProbComp) (spec := unifSpec) n) >>= fun u => pure (u, s))

/-- Distributional equivalence of `oa₁, oa₂ : OracleComp T α` under every `ValidCoinSim fwdU`
stateful challenger or reduction simulator. -/
structure CoinSimEquiv {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α : Type} (oa₁ oa₂ : OracleComp T α) : Prop where
  run_eq : ∀ {σ : Type} (impl : QueryImpl T (StateT σ ProbComp)),
    ValidCoinSim fwdU impl →
    ∀ (s : σ), (simulateQ impl oa₁).run s =ᵈ (simulateQ impl oa₂).run s

namespace CoinSimEquiv

variable {ι : Type} {T : OracleSpec.{0, 0} ι} {fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))}

theorem refl {α : Type} (oa : OracleComp T α) : CoinSimEquiv fwdU oa oa :=
  ⟨fun _ _ _ => EvalDistEq.rfl⟩

theorem of_eq {α : Type} {oa₁ oa₂ : OracleComp T α} (h : oa₁ = oa₂) :
    CoinSimEquiv fwdU oa₁ oa₂ :=
  h ▸ refl oa₁

theorem symm {α : Type} {oa₁ oa₂ : OracleComp T α} (h : CoinSimEquiv fwdU oa₁ oa₂) :
    CoinSimEquiv fwdU oa₂ oa₁ :=
  ⟨fun impl himpl s => (h.run_eq impl himpl s).symm⟩

theorem trans {α : Type} {oa₁ oa₂ oa₃ : OracleComp T α}
    (h₁ : CoinSimEquiv fwdU oa₁ oa₂) (h₂ : CoinSimEquiv fwdU oa₂ oa₃) :
    CoinSimEquiv fwdU oa₁ oa₃ :=
  ⟨fun impl himpl s => (h₁.run_eq impl himpl s).trans (h₂.run_eq impl himpl s)⟩

theorem bind {α β : Type} {oa₁ oa₂ : OracleComp T α} {k₁ k₂ : α → OracleComp T β}
    (hoa : CoinSimEquiv fwdU oa₁ oa₂)
    (hk : ∀ a, CoinSimEquiv fwdU (k₁ a) (k₂ a)) :
    CoinSimEquiv fwdU (oa₁ >>= k₁) (oa₂ >>= k₂) := ⟨by
  intro σ impl himpl s
  simp only [simulateQ_bind, StateT.run_bind]
  exact (hoa.run_eq impl himpl s).bind fun p => (hk p.1).run_eq impl himpl p.2⟩

theorem map {α β : Type} (f : α → β) {oa₁ oa₂ : OracleComp T α}
    (h : CoinSimEquiv fwdU oa₁ oa₂) :
    CoinSimEquiv fwdU (f <$> oa₁) (f <$> oa₂) := by
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  exact h.bind fun a => refl (pure (f a))

theorem iterM_congr {α : Type} {f₁ f₂ : α → OracleComp T α}
    (hf : ∀ a, CoinSimEquiv fwdU (f₁ a) (f₂ a)) :
    ∀ (n : ℕ) (a : α), CoinSimEquiv fwdU (iterM f₁ n a) (iterM f₂ n a)
  | 0, a => refl (pure a)
  | n + 1, a => (hf a).bind (iterM_congr hf n)

theorem findML_congr {α : Type} {p₁ p₂ : α → OracleComp T Bool}
    (hp : ∀ a, CoinSimEquiv fwdU (p₁ a) (p₂ a)) :
    ∀ (xs : List α), CoinSimEquiv fwdU (findML p₁ xs) (findML p₂ xs)
  | [] => refl (pure none)
  | x :: xs =>
    (hp x).bind fun b => by
      cases b
      · exact findML_congr hp xs
      · exact refl (pure (some x))

theorem anyML_congr {α : Type} {p₁ p₂ : α → OracleComp T Bool}
    (hp : ∀ a, CoinSimEquiv fwdU (p₁ a) (p₂ a)) :
    ∀ (xs : List α), CoinSimEquiv fwdU (anyML p₁ xs) (anyML p₂ xs)
  | [] => refl (pure false)
  | x :: xs =>
    (hp x).bind fun b => by
      cases b
      · exact anyML_congr hp xs
      · exact refl (pure true)

theorem mapML_congr {α β : Type} {f₁ f₂ : α → OracleComp T β}
    (hf : ∀ a, CoinSimEquiv fwdU (f₁ a) (f₂ a)) :
    ∀ (xs : List α), CoinSimEquiv fwdU (mapML f₁ xs) (mapML f₂ xs)
  | [] => refl (pure [])
  | x :: xs => (hf x).bind fun y => (mapML_congr hf xs).bind fun ys => refl (pure (y :: ys))

theorem consumeFirstML_congr {α : Type} {p₁ p₂ : α → OracleComp T Bool} (mk : α → α)
    (hp : ∀ a, CoinSimEquiv fwdU (p₁ a) (p₂ a)) :
    ∀ (xs : List α),
      CoinSimEquiv fwdU (consumeFirstML p₁ mk xs) (consumeFirstML p₂ mk xs)
  | [] => refl (pure (false, []))
  | x :: xs =>
    (hp x).bind fun b => by
      cases b
      · exact (consumeFirstML_congr mk hp xs).bind fun r => refl (pure (r.1, x :: r.2))
      · exact refl (pure (true, mk x :: xs))

theorem foldML_congr {α β : Type} {f₁ f₂ : α → β → OracleComp T β}
    (hf : ∀ a b, CoinSimEquiv fwdU (f₁ a b) (f₂ a b)) :
    ∀ (xs : List α) (b : β),
      CoinSimEquiv fwdU (foldML f₁ b xs) (foldML f₂ b xs)
  | [], b => refl (pure b)
  | x :: xs, b => (hf x b).bind (foldML_congr hf xs)

end CoinSimEquiv

theorem evalDistEq_simulateQ_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {σ : Type} (impl : QueryImpl T (StateT σ ProbComp))
    (himpl : ValidCoinSim I.fwdU impl) {α : Type} (p : ProbComp α) :
    ∀ (s : σ), (simulateQ impl (I.liftP p)).run s =ᵈ (p >>= fun a => pure (a, s)) := by
  induction p using OracleComp.inductionOn with
  | pure a => intro s; simp [Iface.liftP]
  | query_bind n k ih =>
    intro s
    unfold Iface.liftP
    rw [simulateQ_query_bind, simulateQ_bind, StateT.run_bind]
    change (simulateQ impl (I.fwdU n)).run s >>=
        (fun z => (simulateQ impl (I.liftP (k z.1))).run z.2) =ᵈ _
    refine ((himpl.coin_eq n s).bind fun z => ih z.1 z.2).trans ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl

theorem coinSimEquiv_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α : Type} {p₁ p₂ : ProbComp α} (h : p₁ =ᵈ p₂) :
    CoinSimEquiv I.fwdU (I.liftP p₁) (I.liftP p₂) := ⟨by
  intro σ impl himpl s
  exact (evalDistEq_simulateQ_liftP I impl himpl p₁ s).trans
    ((h.bind fun _ => EvalDistEq.rfl).trans
      (evalDistEq_simulateQ_liftP I impl himpl p₂ s).symm)⟩

def compCoinImpl {κ ι : Type} {G : OracleSpec.{0, 0} κ} {T : OracleSpec.{0, 0} ι}
    {σ₁ σ₂ : Type}
    (h : QueryImpl G (StateT σ₁ (OracleComp T)))
    (impl : QueryImpl T (StateT σ₂ ProbComp)) :
    QueryImpl G (StateT (σ₁ × σ₂) ProbComp) := fun q =>
  StateT.mk fun s => do
    let z ← (simulateQ impl ((h q).run s.1)).run s.2
    pure (z.1.1, (z.1.2, z.2))

theorem simulateQ_compCoinImpl_run {κ ι : Type} {G : OracleSpec.{0, 0} κ}
    {T : OracleSpec.{0, 0} ι} {σ₁ σ₂ α : Type}
    (h : QueryImpl G (StateT σ₁ (OracleComp T)))
    (impl : QueryImpl T (StateT σ₂ ProbComp))
    (oa : OracleComp G α) :
    ∀ (s₁ : σ₁) (s₂ : σ₂),
      (simulateQ impl ((simulateQ h oa).run s₁)).run s₂ =
        (fun p : α × (σ₁ × σ₂) => ((p.1, p.2.1), p.2.2)) <$>
          (simulateQ (compCoinImpl h impl) oa).run (s₁, s₂) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s₁ s₂; simp
  | query_bind q k ih =>
    intro s₁ s₂
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_query_bind, StateT.run_bind, map_bind]
    change (do
      let z ← (simulateQ impl ((h q).run s₁)).run s₂
      (simulateQ impl ((simulateQ h (k z.1.1)).run z.1.2)).run z.2) =
      (do
        let w ← (do
          let z ← (simulateQ impl ((h q).run s₁)).run s₂
          pure (z.1.1, (z.1.2, z.2)))
        (fun p : α × (σ₁ × σ₂) => ((p.1, p.2.1), p.2.2)) <$>
          (simulateQ (compCoinImpl h impl) (k w.1)).run w.2)
    rw [bind_assoc]
    refine bind_congr fun z => ?_
    rw [pure_bind]
    exact ih z.1.1 z.1.2 z.2

theorem validCoinSim_compCoinImpl {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec.{0, 0} ι} {I : Iface S T} {G : OracleSpec.{0, 0} κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out)
    {σ₂ : Type} {impl : QueryImpl T (StateT σ₂ ProbComp)}
    (himpl : ValidCoinSim I.fwdU impl) :
    ValidCoinSim (fun n => query (spec := unifSpec + G) (.inl n)) (compCoinImpl R.impl impl) := ⟨by
  intro n ⟨s₁, s₂⟩
  rw [simulateQ_HasQuery_query]
  change (do
    let z ← (simulateQ impl (I.fwdU n >>= fun x => pure (x, s₁))).run s₂
    pure (z.1.1, (z.1.2, z.2))) =ᵈ
    ((query (m := ProbComp) (spec := unifSpec) n) >>= fun u => pure (u, (s₁, s₂)))
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    bind_assoc, pure_bind]
  have hb := (himpl.coin_eq n s₂).bind
    (f := fun z : Fin (n + 1) × σ₂ => (pure (z.1, (s₁, z.2)) : ProbComp _))
    (g := fun z : Fin (n + 1) × σ₂ => (pure (z.1, (s₁, z.2)) : ProbComp _))
    (fun _ => EvalDistEq.rfl)
  simpa only [bind_assoc, pure_bind] using hb⟩

theorem costedReduction_eval_coinSimEquiv_congr {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec.{0, 0} ι} {I : Iface S T} {G : OracleSpec.{0, 0} κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out)
    {adv₁ adv₂ : aIn.denote → OracleComp (unifSpec + G) aOut.denote}
    (hA : ∀ a, CoinSimEquiv (fun n => query (spec := unifSpec + G) (.inl n)) (adv₁ a) (adv₂ a))
    (x : rIn.denote) :
    CoinSimEquiv I.fwdU (R.eval adv₁ x) (R.eval adv₂ x) := ⟨by
  intro σ₂ impl himpl s₂
  unfold CostedReduction.eval
  simp only [simulateQ_bind, StateT.run_bind]
  refine EvalDistEq.rfl.bind fun p0 => ?_
  rcases p0 with ⟨⟨a, s₁⟩, s₂'⟩
  rw [simulateQ_compCoinImpl_run, simulateQ_compCoinImpl_run]
  simp only [bind_map_left]
  exact ((hA a).run_eq (compCoinImpl R.impl impl)
    (validCoinSim_compCoinImpl R himpl) (s₁, s₂')).bind fun _ => EvalDistEq.rfl⟩

private def idCoinImpl : QueryImpl unifSpec (StateT Unit ProbComp) :=
  fun n => StateT.lift (query (m := ProbComp) (spec := unifSpec) n)

private theorem simulateQ_idCoinImpl_run {α : Type} (oa : ProbComp α) :
    (simulateQ idCoinImpl oa).run () = (·, ()) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [simulateQ_query_bind, StateT.run_bind, map_bind]
    change (do
      let p ← (do let u ← query (m := ProbComp) (spec := unifSpec) n; pure (u, ()))
      (simulateQ idCoinImpl (k p.1)).run p.2) =
      (do
        let u ← query (m := ProbComp) (spec := unifSpec) n
        (·, ()) <$> k u)
    rw [bind_assoc]
    refine bind_congr fun u => ?_
    rw [pure_bind]
    exact ih u

theorem CoinSimEquiv.evalDistEq_unifSpec {α : Type} {oa₁ oa₂ : ProbComp α}
    (h : CoinSimEquiv (fun n => query (spec := unifSpec) n) oa₁ oa₂) :
    oa₁ =ᵈ oa₂ := by
  have hv : ValidCoinSim (fun n => query (spec := unifSpec) n) idCoinImpl := ⟨fun n s => by
    cases s
    rw [simulateQ_HasQuery_query]
    dsimp only [idCoinImpl, StateT.lift, StateT.run]
    exact EvalDistEq.rfl⟩
  have hrun := (h.run_eq idCoinImpl hv ()).map Prod.fst
  rw [simulateQ_idCoinImpl_run, simulateQ_idCoinImpl_run, Functor.map_map, Functor.map_map] at hrun
  change id <$> oa₁ =ᵈ id <$> oa₂ at hrun
  simpa only [id_map] using hrun

theorem validCoinSim_challengerImpl {κ σ : Type} {H : OracleSpec.{0, 0} κ}
    (hOracle : QueryImpl H (StateT σ ProbComp)) :
    ValidCoinSim (fun n => query (spec := unifSpec + H) (.inl n))
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hOracle) := ⟨by
  intro n s
  rw [simulateQ_HasQuery_query, QueryImpl.add_apply_inl]
  dsimp only [QueryImpl.liftTarget, QueryImpl.ofLift, StateT.lift, StateT.run]
  exact EvalDistEq.rfl⟩

theorem ckaBranch_evalDistEq_of_coinSimEquiv {Key State Coins Msg CKey : Type}
    [SampleableType Key] [SampleableType Coins] [SampleableType CKey]
    (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ) (b : Bool)
    {adv₁ adv₂ : CryptoGames.CKA.Adversary State Coins Msg CKey}
    (h : CoinSimEquiv
      (fun n => query (spec := unifSpec + CryptoGames.CKA.spec State Coins Msg CKey) (.inl n))
      adv₁ adv₂) :
    CryptoGames.CKA.branch cka Δ tStar b adv₁ =ᵈ CryptoGames.CKA.branch cka Δ tStar b adv₂ := by
  unfold CryptoGames.CKA.branch
  refine EvalDistEq.rfl.bind fun k => ?_
  simp only [StateT.run']
  exact (h.run_eq _ (validCoinSim_challengerImpl _)
    (CryptoGames.CKA.initState cka k b)).map Prod.fst

theorem ckaGame_evalDistEq_of_coinSimEquiv {Key State Coins Msg CKey : Type}
    [SampleableType Key] [SampleableType Coins] [SampleableType CKey]
    (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
    {adv₁ adv₂ : CryptoGames.CKA.Adversary State Coins Msg CKey}
    (h : CoinSimEquiv
      (fun n => query (spec := unifSpec + CryptoGames.CKA.spec State Coins Msg CKey) (.inl n))
      adv₁ adv₂) :
    CryptoGames.CKA.game cka Δ tStar adv₁ =ᵈ CryptoGames.CKA.game cka Δ tStar adv₂ := by
  unfold CryptoGames.CKA.game
  refine EvalDistEq.rfl.bind fun b => EvalDistEq.rfl.bind fun k => ?_
  simp only [StateT.run']
  exact ((h.run_eq _ (validCoinSim_challengerImpl _)
    (CryptoGames.CKA.initState cka k b)).map Prod.fst).bind fun _ => EvalDistEq.rfl

theorem ckaAdvantage_congr {Key State Coins Msg CKey : Type}
    [SampleableType Key] [SampleableType Coins] [SampleableType CKey]
    (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
    {adv₁ adv₂ : CryptoGames.CKA.Adversary State Coins Msg CKey}
    (h : CoinSimEquiv
      (fun n => query (spec := unifSpec + CryptoGames.CKA.spec State Coins Msg CKey) (.inl n))
      adv₁ adv₂) :
    CryptoGames.CKA.advantage cka Δ tStar adv₁ = CryptoGames.CKA.advantage cka Δ tStar adv₂ := by
  unfold CryptoGames.CKA.advantage
  rw [(ckaGame_evalDistEq_of_coinSimEquiv cka Δ tStar h).evalDist_eq]

theorem prngBranch_evalDistEq_of_coinSimEquiv {Key State Input Output : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Input] [SampleableType Output]
    (P : PRFPRNG Key State Input Output) (b : Bool)
    {adv₁ adv₂ : PRFPRNG.Adversary State Input Output}
    (h : CoinSimEquiv
      (fun n => query (spec := unifSpec + PRFPRNG.spec State Input Output) (.inl n))
      adv₁ adv₂) :
    PRFPRNG.branch P b adv₁ =ᵈ PRFPRNG.branch P b adv₂ := by
  unfold PRFPRNG.branch
  refine EvalDistEq.rfl.bind fun k => ?_
  simp only [StateT.run']
  exact (h.run_eq _ (validCoinSim_challengerImpl _)
    ({ σ := P.init k, b := b } : PRFPRNG.GameState State Input Output)).map Prod.fst

theorem prngGame_evalDistEq_of_coinSimEquiv {Key State Input Output : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Input] [SampleableType Output]
    (P : PRFPRNG Key State Input Output)
    {adv₁ adv₂ : PRFPRNG.Adversary State Input Output}
    (h : CoinSimEquiv
      (fun n => query (spec := unifSpec + PRFPRNG.spec State Input Output) (.inl n))
      adv₁ adv₂) :
    PRFPRNG.game P adv₁ =ᵈ PRFPRNG.game P adv₂ := by
  unfold PRFPRNG.game
  refine EvalDistEq.rfl.bind fun b => EvalDistEq.rfl.bind fun k => ?_
  simp only [StateT.run']
  exact ((h.run_eq _ (validCoinSim_challengerImpl _)
    ({ σ := P.init k, b := b } : PRFPRNG.GameState State Input Output)).map Prod.fst).bind
    fun _ => EvalDistEq.rfl

theorem prngAdvantage_congr {Key State Input Output : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Input] [SampleableType Output]
    (P : PRFPRNG Key State Input Output)
    {adv₁ adv₂ : PRFPRNG.Adversary State Input Output}
    (h : CoinSimEquiv
      (fun n => query (spec := unifSpec + PRFPRNG.spec State Input Output) (.inl n))
      adv₁ adv₂) :
    PRFPRNG.advantage P adv₁ = PRFPRNG.advantage P adv₂ := by
  unfold PRFPRNG.advantage
  rw [(prngGame_evalDistEq_of_coinSimEquiv P h).evalDist_eq]

theorem fsaeadGame_evalDistEq_of_coinSimEquiv {Key SS RS AD Msg C : Type}
    [DecidableEq AD] [DecidableEq Msg] [DecidableEq C] [SampleableType Key]
    (fs : FSAEADScheme Key SS RS AD Msg C)
    {adv₁ adv₂ : CryptoGames.FSAEAD.Adversary SS RS AD Msg C}
    (h : CoinSimEquiv
      (fun n => query (spec := unifSpec + CryptoGames.FSAEAD.spec SS RS AD Msg C) (.inl n))
      adv₁ adv₂) :
    CryptoGames.FSAEAD.game fs adv₁ =ᵈ CryptoGames.FSAEAD.game fs adv₂ := by
  unfold CryptoGames.FSAEAD.game
  refine EvalDistEq.rfl.bind fun b => EvalDistEq.rfl.bind fun k => ?_
  exact (h.run_eq _ (validCoinSim_challengerImpl _) (CryptoGames.FSAEAD.initState fs k b)).bind
    fun _ => EvalDistEq.rfl

theorem fsaeadAdvantage_congr {Key SS RS AD Msg C : Type}
    [DecidableEq AD] [DecidableEq Msg] [DecidableEq C] [SampleableType Key]
    (fs : FSAEADScheme Key SS RS AD Msg C)
    {adv₁ adv₂ : CryptoGames.FSAEAD.Adversary SS RS AD Msg C}
    (h : CoinSimEquiv
      (fun n => query (spec := unifSpec + CryptoGames.FSAEAD.spec SS RS AD Msg C) (.inl n))
      adv₁ adv₂) :
    CryptoGames.FSAEAD.advantage fs adv₁ = CryptoGames.FSAEAD.advantage fs adv₂ := by
  unfold CryptoGames.FSAEAD.advantage
  rw [(fsaeadGame_evalDistEq_of_coinSimEquiv fs h).evalDist_eq]

theorem prgAdvantage_congr {Seed R : Type} [SampleableType Seed] [SampleableType R]
    (prg : PRGScheme Seed R) {adv₁ adv₂ : PRGScheme.PRGAdversary R}
    (h : ∀ r, adv₁ r =ᵈ adv₂ r) :
    prg.prgAdvantage adv₁ = prg.prgAdvantage adv₂ := by
  unfold PRGScheme.prgAdvantage PRGScheme.prgRealExperiment PRGScheme.prgIdealExperiment
  rw [(EvalDistEq.rfl.bind fun s => h (prg.gen s)).evalDist_eq,
    (EvalDistEq.rfl.bind h).evalDist_eq]

theorem prfAdvantage_congr {Key Input Tag : Type} [DecidableEq Input]
    [SampleableType Key] [SampleableType Tag]
    (mac : MACScheme Key Input Tag) {adv₁ adv₂ : MACScheme.PRFAdversary Input Tag}
    (h : CoinSimEquiv (fun n => query (spec := unifSpec + MACScheme.prfSpec Input Tag) (.inl n))
      adv₁ adv₂) :
    mac.prfAdvantage adv₁ = mac.prfAdvantage adv₂ := by
  unfold MACScheme.prfAdvantage
  have hg : mac.prfGame adv₁ =ᵈ mac.prfGame adv₂ := by
    unfold MACScheme.prfGame
    refine EvalDistEq.rfl.bind fun b => EvalDistEq.rfl.bind fun key => ?_
    simp only [StateT.run']
    exact ((h.run_eq _ (validCoinSim_challengerImpl _)
      ({ key := key, b := b } : MACScheme.PRFState Key Input Tag)).map Prod.fst).bind
      fun _ => EvalDistEq.rfl
  rw [hg.evalDist_eq]

theorem wireOtccaAdvantage_congr {K AD H M M' C T : Type}
    [SampleableType K] [SampleableType C] [SampleableType T] [DecidableEq AD] [DecidableEq T]
    (ae : WireAEAD K AD H M M' C T) {adv₁ adv₂ : WireAEAD.WireAdversary AD H M M' T}
    (h : CoinSimEquiv (fun n => query (spec := unifSpec + WireAEAD.wireSpec AD H M M' T) (.inl n))
      adv₁ adv₂) :
    ae.wireOtccaAdvantage adv₁ = ae.wireOtccaAdvantage adv₂ := by
  unfold WireAEAD.wireOtccaAdvantage
  have hg : ae.wireOtccaGame adv₁ =ᵈ ae.wireOtccaGame adv₂ := by
    unfold WireAEAD.wireOtccaGame
    refine EvalDistEq.rfl.bind fun b => EvalDistEq.rfl.bind fun key => ?_
    simp only [StateT.run']
    exact ((h.run_eq _ (validCoinSim_challengerImpl _)
      ({ key := key, b := b } : WireAEAD.WireState K AD T)).map Prod.fst).bind
      fun _ => EvalDistEq.rfl
  rw [hg.evalDist_eq]

theorem otccaAdvantage_congr {Key AD M C : Type}
    [DecidableEq AD] [DecidableEq C] [SampleableType Key] [SampleableType C]
    (ae : AEADScheme Key AD M C) {adv₁ adv₂ : AEADScheme.OTCCAAdversary AD M C}
    (h : CoinSimEquiv (fun n => query (spec := unifSpec + AEADScheme.otccaSpec AD M C) (.inl n))
      adv₁ adv₂) :
    ae.otccaAdvantage adv₁ = ae.otccaAdvantage adv₂ := by
  unfold AEADScheme.otccaAdvantage
  have hg : ae.otccaGame adv₁ =ᵈ ae.otccaGame adv₂ := by
    unfold AEADScheme.otccaGame
    refine EvalDistEq.rfl.bind fun b => EvalDistEq.rfl.bind fun key => ?_
    simp only [StateT.run']
    exact ((h.run_eq _ (validCoinSim_challengerImpl _)
      ({ key := key, b := b } : AEADScheme.OTCCAState Key AD C)).map Prod.fst).bind
      fun _ => EvalDistEq.rfl
  rw [hg.evalDist_eq]

end CoinSim

/-! ## Uniform `BitVec 64` and `Bool` sampling from `BitVec 128` -/

section SampleBool

private theorem extractLsb'_zero_bytesToWordLE64_cons (b : BitVec 8) (acc : BitVec 64) :
    ((acc <<< 8) ||| b.zeroExtend 64).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h64 : i < 64 := by omega
  simp [hi, h64]

private theorem extractLsb'_succ_bytesToWordLE64_cons (b : BitVec 8) (acc : BitVec 64) (j : ℕ)
    (hj : j + 1 < 8) :
    ((acc <<< 8) ||| b.zeroExtend 64).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 64 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToWordLE64 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h8 : j < 8) :
    (bytesToWordLE 64 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToWordLE] using
        extractLsb'_zero_bytesToWordLE64_cons b (bytesToWordLE 64 rest)
    | succ j =>
      have hcons : bytesToWordLE 64 (b :: rest) =
          (bytesToWordLE 64 rest <<< 8) ||| b.zeroExtend 64 := rfl
      rw [hcons, extractLsb'_succ_bytesToWordLE64_cons b (bytesToWordLE 64 rest) j h8,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem bytesToWordLE_64_toLEBytes_16_take_8 (x : BitVec 128) :
    bytesToWordLE 64 ((toLEBytes 16 x).take 8) = x.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 8 := by omega
  have hr : i % 8 < 8 := by omega
  have hlen : i / 8 < ((toLEBytes 16 x).take 8).length := by simp [toLEBytes, hj]
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToWordLE64 ((toLEBytes 16 x).take 8) (i / 8) hlen hj)
  simp only [toLEBytes, List.getElem_take, List.getElem_ofFn, BitVec.getLsbD_extractLsb',
    hr, hi, Nat.zero_add, decide_true, Bool.true_and, Nat.div_add_mod] at hbyte ⊢
  exact hbyte

theorem sample_u64_of_bv128_evalDistEq :
    (do
      let x ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
      pure (bytesToWordLE 64 ((toLEBytes 16 x).take 8))) =ᵈ
      ($ᵗ (BitVec 64) : ProbComp (BitVec 64)) := by
  simp only [bytesToWordLE_64_toLEBytes_16_take_8]
  have hm := evalDistEq_marginal_snd_of_bijective (equivBitVecSplit 64 64).bijective
  rw [map_eq_bind_pure_comp] at hm
  exact hm

private def equivBitVec1Bool : BitVec 1 ≃ Bool where
  toFun v := v == 1#1
  invFun b := if b then 1#1 else 0#1
  left_inv v := by
    rcases v with ⟨⟨_ | ⟨_ | _⟩, hv⟩⟩
    · rfl
    · rfl
    · omega
  right_inv b := by cases b <;> rfl

theorem sample_bool_of_bv128_evalDistEq :
    (do
      let x ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
      pure (decide ((bytesToWordLE 64 ((toLEBytes 16 x).take 8)).toNat % 2 = 1))) =ᵈ
      ($ᵗ Bool : ProbComp Bool) := by
  let fBool : BitVec 64 → ProbComp Bool := fun u => pure (decide (u.toNat % 2 = 1))
  have hstep :
      (do
        let x ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
        pure (decide ((bytesToWordLE 64 ((toLEBytes 16 x).take 8)).toNat % 2 = 1))) =ᵈ
      (($ᵗ (BitVec 64) : ProbComp (BitVec 64)) >>= fBool) := by
    have hb := sample_u64_of_bv128_evalDistEq.bind (f := fBool) (g := fBool)
      fun _ => EvalDistEq.rfl
    simpa only [fBool, bind_assoc, pure_bind] using hb
  refine hstep.trans ?_
  have hbit : ∀ u : BitVec 64,
      decide (u.toNat % 2 = 1) = equivBitVec1Bool (u.extractLsb' 0 1) := by
    intro u
    change decide (u.toNat % 2 = 1) = (u.extractLsb' 0 1 == 1#1)
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff, beq_iff_eq, ← BitVec.toNat_inj]
    dsimp only [BitVec.extractLsb']
    simp [BitVec.toNat_ofNat]
  dsimp only [fBool]
  simp only [hbit]
  have hm := (evalDistEq_marginal_snd_of_bijective (equivBitVecSplit 63 1).bijective).map
    equivBitVec1Bool
  rw [Functor.map_map, map_eq_bind_pure_comp] at hm
  exact hm.trans (evalDistEq_uniformSample_equiv equivBitVec1Bool)

def fig8PureOp (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {Γ : List (Ty (atomicSig ℓ Pt))} (o : AtomicPureOp)
    (a : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ (o.dom ℓ Pt)) :
    Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ (o.cod ℓ Pt) :=
  Expr.op (O := atomicFig8Ops ℓ Pt C Dh encPt encT lam) (Sum.inl (Sum.inl o)) a

theorem fig8PureOp_cost (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {Γ : List (Ty (atomicSig ℓ Pt))} (o : AtomicPureOp)
    (a : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ (o.dom ℓ Pt)) :
    (fig8PureOp ℓ Pt C Dh encPt encT lam o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem fig8PureOp_size (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {Γ : List (Ty (atomicSig ℓ Pt))} (o : AtomicPureOp)
    (a : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ (o.dom ℓ Pt)) :
    (fig8PureOp ℓ Pt C Dh encPt encT lam o a).size = a.size + o.opSize + 1 := rfl

theorem fig8PureOp_eval (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {Γ : List (Ty (atomicSig ℓ Pt))} (o : AtomicPureOp)
    (a : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (fig8PureOp ℓ Pt C Dh encPt encT lam o a).eval ρ = o.eval ℓ Pt (a.eval ρ) := rfl

def boolOfBv128Fig8Expr (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {Γ : List (Ty (atomicSig ℓ Pt))} :
    Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (BV128 :: Γ) .bool :=
  .eqN
    (.modK 2
      (fig8PureOp ℓ Pt C Dh encPt encT lam .u64ToNat
        (fig8PureOp ℓ Pt C Dh encPt encT lam .bytesToU64Le
          (fig8PureOp ℓ Pt C Dh encPt encT lam (.bytesTakeK 16 8)
            (fig8PureOp ℓ Pt C Dh encPt encT lam .bv128ToBytes16 (.var .zero))))))
    (.nat 1)

/-- `Comp` macro on `atomicFig8Ops` sampling a uniform `Bool` from a `BV128` coin draw `sampBv128`. -/
def sampleBoolFig8Comp (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} {Γ : List (Ty (atomicSig ℓ Pt))}
    (sampBv128 : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) I Γ BV128) :
    Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) I Γ .bool :=
  .bind sampBv128 (.ret (boolOfBv128Fig8Expr ℓ Pt C Dh encPt encT lam))

theorem boolOfBv128Fig8Expr_cost (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {Γ : List (Ty (atomicSig ℓ Pt))} :
    (boolOfBv128Fig8Expr ℓ Pt C Dh encPt encT lam (Γ := Γ)).cost ≤ 130 := by
  have hb2 : bits 2 = 2 := by decide
  have hb1 : bits 1 = 1 := by decide
  simp only [boolOfBv128Fig8Expr, fig8PureOp_cost, Expr.cost, AtomicPureOp.cost,
    PNat.val_ofNat, hb2, hb1]
  omega

theorem sampleBoolFig8Comp_cost (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} {Γ : List (Ty (atomicSig ℓ Pt))}
    (sampBv128 : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) I Γ BV128) :
    (sampleBoolFig8Comp ℓ Pt C Dh encPt encT lam sampBv128).cost ≤ sampBv128.cost + 132 := by
  have hb := boolOfBv128Fig8Expr_cost ℓ Pt C Dh encPt encT lam (Γ := Γ)
  simp only [sampleBoolFig8Comp, Comp.cost]
  omega

theorem boolOfBv128Fig8Expr_size (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {Γ : List (Ty (atomicSig ℓ Pt))} :
    (boolOfBv128Fig8Expr ℓ Pt C Dh encPt encT lam (Γ := Γ)).size ≤ 15 := by
  have hb2 : bits 2 = 2 := by decide
  have hb1 : bits 1 = 1 := by decide
  simp only [boolOfBv128Fig8Expr, fig8PureOp_size, AtomicPureOp.opSize, Expr.size, hb2, hb1]
  omega

theorem sampleBoolFig8Comp_size (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} {Γ : List (Ty (atomicSig ℓ Pt))}
    (sampBv128 : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) I Γ BV128) :
    (sampleBoolFig8Comp ℓ Pt C Dh encPt encT lam sampBv128).size ≤ sampBv128.size + 17 := by
  have hb := boolOfBv128Fig8Expr_size ℓ Pt C Dh encPt encT lam (Γ := Γ)
  simp only [sampleBoolFig8Comp, Comp.size]
  omega

theorem sampleBoolFig8Comp_queries (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} {Γ : List (Ty (atomicSig ℓ Pt))}
    (sampBv128 : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) I Γ BV128)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (sampleBoolFig8Comp ℓ Pt C Dh encPt encT lam sampBv128).queries w ws =
      sampBv128.queries w ws := by
  simp [sampleBoolFig8Comp, Comp.queries]

theorem sampleBoolFig8Comp_coinSimEquiv (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) {ι : Type} {T : OracleSpec.{0, 0} ι}
    {I : Iface (atomicSig ℓ Pt) T} {Γ : List (Ty (atomicSig ℓ Pt))}
    (sampBv128 : Comp (atomicFig8Ops ℓ Pt C Dh encPt encT lam) I Γ BV128)
    (ρ : Env Γ)
    (hSamp : sampBv128.eval ρ = I.liftP ($ᵗ (BitVec 128) : ProbComp (BitVec 128))) :
    CoinSimEquiv I.fwdU
      ((sampleBoolFig8Comp ℓ Pt C Dh encPt encT lam sampBv128).eval ρ)
      (I.liftP ($ᵗ Bool : ProbComp Bool)) := by
  have heval :
      (sampleBoolFig8Comp ℓ Pt C Dh encPt encT lam sampBv128).eval ρ =
        I.liftP (do
          let x ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
          pure (decide ((bytesToWordLE 64 ((toLEBytes 16 x).take 8)).toNat % 2 = 1))) := by
    simp only [sampleBoolFig8Comp, Comp.eval, hSamp]
    dsimp only [Iface.liftP]
    rw [simulateQ_bind]
    refine bind_congr fun x => ?_
    simp only [boolOfBv128Fig8Expr, fig8PureOp_eval, Expr.eval, Env.get,
      AtomicPureOp.eval, PNat.val_ofNat, simulateQ_pure]
  rw [heval]
  exact coinSimEquiv_liftP I sample_bool_of_bv128_evalDistEq

end SampleBool

/-! ## Auxiliary-context pure macro compiler -/

section PureAuxCompiler

def callPureMacroAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {a b : Ty S₂} (e : Expr O₂ [a, auxT] b) :
    Expr O₂ (a :: mapCtx f auxT Γ) b :=
  Expr.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ (auxVar f auxT Γ))
    e

@[simp] theorem callPureMacroAux_cost {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {a b : Ty S₂} (e : Expr O₂ [a, auxT] b) :
    (callPureMacroAux f auxT Γ e).cost = e.cost :=
  Expr.renameM_cost _ e

@[simp] theorem callPureMacroAux_size {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {a b : Ty S₂} (e : Expr O₂ [a, auxT] b) :
    (callPureMacroAux f auxT Γ e).size = e.size :=
  Expr.renameM_size _ e

theorem callPureMacroAux_eval {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote)
    {Γ : List (Ty S₁)} (ρ : Env Γ) {O₂ : Ops S₂} {a b : Ty S₂}
    (e : Expr O₂ [a, auxT] b) (x : a.denote) :
    (callPureMacroAux f auxT Γ e).eval (.cons x (mapEnvAux f toDen aux ρ)) =
      e.eval (.cons x (.cons aux .nil)) := by
  refine Expr.renameM_eval e ?_
  intro u v
  cases v with
  | zero => rfl
  | succ v =>
    cases v with
    | zero => exact get_auxVar f toDen aux ρ
    | succ v => nomatch v

/-- Bundle of pure `Expr` operator macros and `Comp` sampler/query macros with access to `(arg, aux)`. -/
structure PureAuxBundle (S₁ S₂ : Sig) (O₁ : Ops S₁) (O₂ : Ops S₂)
    {ι : Type} {T : OracleSpec ι} (I₁ : Iface S₁ T) (I₂ : Iface S₂ T)
    (auxT : Ty S₂) where
  fSort : S₁.Base → Ty S₂
  opMacro : (o : O₁.Op) → Expr O₂ [mapTy fSort (O₁.dom o), auxT] (mapTy fSort (O₁.cod o))
  sampMacro : (s : I₁.smp.Samp) →
    Comp O₂ I₂ [mapTy fSort (I₁.smp.sDom s), auxT] (mapTy fSort (I₁.smp.sTy s))
  queryMacro : (g : I₁.Tag) →
    Comp O₂ I₂ [mapTy fSort (I₁.dom g), auxT] (mapTy fSort (I₁.cod g))

variable {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
  {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}

def compilePureAuxExpr (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Expr O₁ Γ t → Expr O₂ (mapCtx M.fSort auxT Γ) (mapTy M.fSort t)
  | _, _, .var v => .var (mapVarAux M.fSort auxT v)
  | _, _, .unit => .unit
  | _, _, .bool b => .bool b
  | _, _, .nat n => .nat n
  | _, _, .add a b => .add (compilePureAuxExpr M a) (compilePureAuxExpr M b)
  | _, _, .sub a b => .sub (compilePureAuxExpr M a) (compilePureAuxExpr M b)
  | _, _, .mulK k a => .mulK k (compilePureAuxExpr M a)
  | _, _, .divK k a => .divK k (compilePureAuxExpr M a)
  | _, _, .modK k a => .modK k (compilePureAuxExpr M a)
  | _, _, .lt a b => .lt (compilePureAuxExpr M a) (compilePureAuxExpr M b)
  | _, _, .eqN a b => .eqN (compilePureAuxExpr M a) (compilePureAuxExpr M b)
  | _, _, .not a => .not (compilePureAuxExpr M a)
  | _, _, .and a b => .and (compilePureAuxExpr M a) (compilePureAuxExpr M b)
  | _, _, .ite c a b =>
    .ite (compilePureAuxExpr M c) (compilePureAuxExpr M a) (compilePureAuxExpr M b)
  | _, _, .pair a b => .pair (compilePureAuxExpr M a) (compilePureAuxExpr M b)
  | _, _, .fst a => .fst (compilePureAuxExpr M a)
  | _, _, .snd a => .snd (compilePureAuxExpr M a)
  | _, _, .inl a => .inl (compilePureAuxExpr M a)
  | _, _, .inr a => .inr (compilePureAuxExpr M a)
  | _, _, .none => .none
  | _, _, .some a => .some (compilePureAuxExpr M a)
  | _, _, .caseOpt e n s =>
    .caseOpt (compilePureAuxExpr M e) (compilePureAuxExpr M n) (compilePureAuxExpr M s)
  | _, _, .caseSum e l r =>
    .caseSum (compilePureAuxExpr M e) (compilePureAuxExpr M l) (compilePureAuxExpr M r)
  | _, _, .letE e b => .letE (compilePureAuxExpr M e) (compilePureAuxExpr M b)
  | Γ, _, .op o a =>
    .letE (compilePureAuxExpr M a) (callPureMacroAux M.fSort auxT Γ (M.opMacro o))
  | _, _, .nil => .nil
  | _, _, .cons x l => .cons (compilePureAuxExpr M x) (compilePureAuxExpr M l)
  | _, _, .len l => .len (compilePureAuxExpr M l)
  | _, _, .take n l => .take (compilePureAuxExpr M n) (compilePureAuxExpr M l)
  | _, _, .appendL K a b => .appendL K (compilePureAuxExpr M a) (compilePureAuxExpr M b)
  | _, _, .findB K l p => .findB K (compilePureAuxExpr M l) (compilePureAuxExpr M p)
  | _, _, .anyB K l p => .anyB K (compilePureAuxExpr M l) (compilePureAuxExpr M p)
  | _, _, .mapB K l f => .mapB K (compilePureAuxExpr M l) (compilePureAuxExpr M f)
  | _, _, .foldrB K l z f =>
    .foldrB K (compilePureAuxExpr M l) (compilePureAuxExpr M z) (compilePureAuxExpr M f)
  | _, _, .tconst a => .tconst (compilePureAuxExpr M a)
  | _, _, .tget m i => .tget (compilePureAuxExpr M m) (compilePureAuxExpr M i)
  | _, _, .tset m i a =>
    .tset (compilePureAuxExpr M m) (compilePureAuxExpr M i) (compilePureAuxExpr M a)

def compilePureAuxComp (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Comp O₁ I₁ Γ t → Comp O₂ I₂ (mapCtx M.fSort auxT Γ) (mapTy M.fSort t)
  | _, _, .ret e => .ret (compilePureAuxExpr M e)
  | _, _, .bind c k => .bind (compilePureAuxComp M c) (compilePureAuxComp M k)
  | _, _, .ite b c d =>
    .ite (compilePureAuxExpr M b) (compilePureAuxComp M c) (compilePureAuxComp M d)
  | _, _, .caseOpt e n s =>
    .caseOpt (compilePureAuxExpr M e) (compilePureAuxComp M n) (compilePureAuxComp M s)
  | _, _, .caseSum e l r =>
    .caseSum (compilePureAuxExpr M e) (compilePureAuxComp M l) (compilePureAuxComp M r)
  | Γ, _, .sample s e =>
    .bind (.ret (compilePureAuxExpr M e)) (callMacroAux M.fSort auxT Γ (M.sampMacro s))
  | Γ, _, .query g e =>
    .bind (.ret (compilePureAuxExpr M e)) (callMacroAux M.fSort auxT Γ (M.queryMacro g))
  | _, _, .iter n e body => .iter n (compilePureAuxExpr M e) (compilePureAuxComp M body)
  | _, _, .findM K l p => .findM K (compilePureAuxExpr M l) (compilePureAuxComp M p)
  | _, _, .anyM K l p => .anyM K (compilePureAuxExpr M l) (compilePureAuxComp M p)
  | _, _, .mapM K l f => .mapM K (compilePureAuxExpr M l) (compilePureAuxComp M f)
  | _, _, .consumeFirstM K l p mk =>
    .consumeFirstM K (compilePureAuxExpr M l) (compilePureAuxComp M p) (compilePureAuxExpr M mk)
  | _, _, .foldM K l z f =>
    .foldM K (compilePureAuxExpr M l) (compilePureAuxExpr M z) (compilePureAuxComp M f)

theorem compilePureAuxComp_queries_le (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hSampQ : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQueryQ : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureAuxComp M c).queries w₂ ws₂ ≤ c.queries w₁ ws₁ := by
  induction c with
  | ret _ => simp [compilePureAuxComp, Comp.queries]
  | bind _ _ ihc ihk => simp only [compilePureAuxComp, Comp.queries]; omega
  | ite _ _ _ ihc ihd | caseOpt _ _ _ ihc ihd | caseSum _ _ _ ihc ihd =>
    simp only [compilePureAuxComp, Comp.queries]; exact max_le_max ihc ihd
  | sample s _ =>
    simp only [compilePureAuxComp, Comp.queries, callMacroAux_queries, zero_add]; exact hSampQ s
  | query g _ =>
    simp only [compilePureAuxComp, Comp.queries, callMacroAux_queries, zero_add]; exact hQueryQ g
  | iter n _ _ ihb =>
    simp only [compilePureAuxComp, Comp.queries]; exact Nat.mul_le_mul_left n ihb
  | findM K _ _ ihp | anyM K _ _ ihp | mapM K _ _ ihp | consumeFirstM K _ _ _ ihp
  | foldM K _ _ _ ihp =>
    simp only [compilePureAuxComp, Comp.queries]; exact Nat.mul_le_mul_left K ihp

theorem compilePureAuxExpr_eval (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hOpE : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) x) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o x))
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) (ρ : Env Γ) :
    (compilePureAuxExpr M e).eval (mapEnvAux M.fSort toDen aux ρ) =
      toVal M.fSort toDen t (e.eval ρ) := by
  induction e with
  | var v => exact get_mapEnvAux M.fSort toDen aux ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 => simp [compilePureAuxExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | sub _ _ ih1 ih2 => simp [compilePureAuxExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | mulK _ _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | divK _ _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | modK _ _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | lt _ _ ih1 ih2 => simp [compilePureAuxExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | eqN _ _ ih1 ih2 => simp [compilePureAuxExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | not _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | and _ _ ih1 ih2 => simp [compilePureAuxExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | ite c _ _ ihc iha ihb =>
    simp only [compilePureAuxExpr, Expr.eval, ihc ρ, toVal]
    cases c.eval ρ <;> [exact ihb ρ; exact iha ρ]
  | pair _ _ ih1 ih2 => simp [compilePureAuxExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | fst _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | snd _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | inl _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | inr _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | some _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | caseOpt e _ _ ihe ihn ihs =>
    simp only [compilePureAuxExpr, Expr.eval, ihe ρ, toVal]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e _ _ ihe ihl ihr =>
    simp only [compilePureAuxExpr, Expr.eval, ihe ρ, toVal]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | letE e _ ihe ihb =>
    simp only [compilePureAuxExpr, Expr.eval, ihe ρ]
    exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha =>
    simp only [compilePureAuxExpr, Expr.eval, iha ρ, callPureMacroAux_eval M.fSort toDen aux ρ]
    exact hOpE o (a.eval ρ)
  | cons _ _ ih1 ih2 => simp [compilePureAuxExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | len _ ih => simp [compilePureAuxExpr, Expr.eval, toVal, ih ρ]
  | take _ _ ih1 ih2 => simp [compilePureAuxExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ, List.map_take]
  | appendL _ _ _ ih1 ih2 =>
    simp [compilePureAuxExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ, List.map_take, List.map_append]
  | findB K l p ihl ihp =>
    simp only [compilePureAuxExpr, Expr.eval, ihl ρ, toVal, ← List.map_take]
    rw [List.find?_map]
    congr 2; funext x; exact ihp (.cons x ρ)
  | anyB K l p ihl ihp =>
    simp only [compilePureAuxExpr, Expr.eval, ihl ρ, toVal, ← List.map_take, List.any_map]
    congr 1; funext x; exact ihp (.cons x ρ)
  | mapB K l f ihl ihf =>
    simp only [compilePureAuxExpr, Expr.eval, ihl ρ, toVal, ← List.map_take, List.map_map]
    congr 1; funext x; exact ihf (.cons x ρ)
  | foldrB K l z f ihl ihz ihf =>
    simp only [compilePureAuxExpr, Expr.eval, ihl ρ, ihz ρ, toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs, z.eval ρ = acc₀
    induction xs with
    | nil => rfl
    | cons x xs ihxs =>
      simp only [List.map_cons, List.foldr_cons, ihxs]
      exact ihf (.cons x (.cons (xs.foldr (fun y b => f.eval (.cons y (.cons b ρ))) acc₀) ρ))
  | tconst _ ih =>
    funext i; exact ih ρ
  | tget m i ihm ihi =>
    have hm := congrFun (ihm ρ) (i.eval ρ)
    simp only [compilePureAuxExpr, Expr.eval, ihi ρ, toVal] at hm ⊢
    exact hm
  | tset m i a ihm ihi iha =>
    funext j
    have hm := congrFun (ihm ρ) j
    simp only [compilePureAuxExpr, Expr.eval, ihi ρ, iha ρ, toVal] at hm ⊢
    split_ifs <;> [rfl; exact hm]

theorem compilePureAuxComp_eval (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hOpE : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) x) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o x))
    (hSampE : ∀ s x,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) x) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x))
    (hQueryE : ∀ g x,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) x) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _)))
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    (compilePureAuxComp M c).eval (mapEnvAux M.fSort toDen aux ρ) =
      toVal M.fSort toDen t <$> c.eval ρ := by
  induction c with
  | ret e =>
    simp [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE e ρ]
  | bind c k ihc ihk =>
    simp only [compilePureAuxComp, Comp.eval, ihc ρ, bind_map_left, map_bind]
    exact OracleComp.bind_congr' rfl fun x => ihk (.cons x ρ)
  | ite b _ _ ihc ihd =>
    simp only [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE b ρ, toVal]
    cases b.eval ρ <;> [exact ihd ρ; exact ihc ρ]
  | caseOpt e _ _ ihn ihs =>
    simp only [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE e ρ, toVal]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e _ _ ihl ihr =>
    simp only [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE e ρ, toVal]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | sample s e =>
    simp only [compilePureAuxComp, Comp.eval, pure_bind,
      compilePureAuxExpr_eval M toDen aux hOpE e ρ, callMacroAux_eval M.fSort toDen aux ρ]
    exact hSampE s (e.eval ρ)
  | query g e =>
    simp only [compilePureAuxComp, Comp.eval, pure_bind,
      compilePureAuxExpr_eval M toDen aux hOpE e ρ, callMacroAux_eval M.fSort toDen aux ρ]
    exact hQueryE g (e.eval ρ)
  | iter n e body ihb =>
    simp only [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE e ρ]
    generalize e.eval ρ = s₀
    induction n generalizing s₀ with
    | zero => simp [iterM]
    | succ n ihn =>
      simp only [iterM, map_bind]
      change ((compilePureAuxComp M body).eval (mapEnvAux M.fSort toDen aux (.cons s₀ ρ)) >>= _) = _
      rw [ihb (.cons s₀ ρ), bind_map_left]
      exact OracleComp.bind_congr' rfl fun s₁ => ihn s₁
  | findM K l p ihp =>
    simp only [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE l ρ,
      toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs
    induction xs with
    | nil => simp [findML]
    | cons x xs ihxs =>
      simp only [List.map_cons, findML, map_bind]
      change (do
        let c ← (compilePureAuxComp M p).eval (mapEnvAux M.fSort toDen aux (.cons x ρ))
        if c then pure (Option.some (toVal M.fSort toDen _ x)) else _) = _
      rw [ihp (.cons x ρ), bind_map_left]
      refine OracleComp.bind_congr' rfl fun b => ?_
      cases b <;> [exact ihxs; simp [toVal]]
  | anyM K l p ihp =>
    simp only [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE l ρ,
      toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs
    induction xs with
    | nil => simp [anyML]
    | cons x xs ihxs =>
      simp only [List.map_cons, anyML, map_bind]
      change (do
        let c ← (compilePureAuxComp M p).eval (mapEnvAux M.fSort toDen aux (.cons x ρ))
        if c then pure true else _) = _
      rw [ihp (.cons x ρ), bind_map_left]
      refine OracleComp.bind_congr' rfl fun b => ?_
      cases b <;> [exact ihxs; simp [toVal]]
  | mapM K l f ihf =>
    simp only [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE l ρ,
      toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs
    induction xs with
    | nil => simp [mapML]
    | cons x xs ihxs =>
      simp only [List.map_cons, mapML, ihxs, bind_map_left, map_bind, map_pure]
      change (do
        let y ← (compilePureAuxComp M f).eval (mapEnvAux M.fSort toDen aux (.cons x ρ))
        _) = _
      rw [ihf (.cons x ρ), bind_map_left]
  | consumeFirstM K l p mk ihp =>
    simp only [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE l ρ,
      toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs
    induction xs with
    | nil => simp [consumeFirstML]
    | cons x xs ihxs =>
      simp only [List.map_cons, consumeFirstML, ihxs, bind_map_left, map_bind]
      change (do
        let c ← (compilePureAuxComp M p).eval (mapEnvAux M.fSort toDen aux (.cons x ρ))
        if c then
          pure (true,
            (compilePureAuxExpr M mk).eval (mapEnvAux M.fSort toDen aux (.cons x ρ)) ::
              List.map (toVal M.fSort toDen _) xs)
        else _) = _
      rw [ihp (.cons x ρ), compilePureAuxExpr_eval M toDen aux hOpE mk (.cons x ρ), bind_map_left]
      refine OracleComp.bind_congr' rfl fun b => ?_
      cases b <;> simp [toVal, map_pure]
  | foldM K l z f ihf =>
    simp only [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE l ρ,
      compilePureAuxExpr_eval M toDen aux hOpE z ρ, toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs, z.eval ρ = acc₀
    induction xs generalizing acc₀ with
    | nil => simp [foldML]
    | cons x xs ihxs =>
      simp only [List.map_cons, foldML, map_bind]
      change (do
        let b' ← (compilePureAuxComp M f).eval
          (mapEnvAux M.fSort toDen aux (.cons x (.cons acc₀ ρ)))
        _) = _
      rw [ihf (.cons x (.cons acc₀ ρ)), bind_map_left]
      exact OracleComp.bind_congr' rfl fun acc₁ => ihxs acc₁

end PureAuxCompiler

section PureAuxCoinSim

private theorem iterM_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α β : Type} (g : α → β) (f₁ : α → OracleComp T α) (f₂ : β → OracleComp T β)
    (hf : ∀ a, CoinSimEquiv fwdU (f₂ (g a)) (g <$> f₁ a)) :
    ∀ (n : ℕ) (a : α), CoinSimEquiv fwdU (iterM f₂ n (g a)) (g <$> iterM f₁ n a)
  | 0, _ => CoinSimEquiv.of_eq (by simp [iterM])
  | n + 1, a => by
    dsimp only [iterM]
    refine ((hf a).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left, map_bind]
    exact (CoinSimEquiv.refl (f₁ a)).bind fun a' => iterM_coinSimEquiv_hom fwdU g f₁ f₂ hf n a'

private theorem findML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α β : Type} (g : α → β) (p₁ : α → OracleComp T Bool) (p₂ : β → OracleComp T Bool)
    (hp : ∀ x, CoinSimEquiv fwdU (p₂ (g x)) (p₁ x)) :
    ∀ xs : List α, CoinSimEquiv fwdU (findML p₂ (xs.map g)) (Option.map g <$> findML p₁ xs)
  | [] => CoinSimEquiv.of_eq (by simp [findML])
  | x :: xs => by
    dsimp only [List.map_cons, findML]; rw [map_bind]
    exact (hp x).bind fun b => match b with
      | true => CoinSimEquiv.of_eq (by simp)
      | false => findML_coinSimEquiv_hom fwdU g p₁ p₂ hp xs

private theorem anyML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α β : Type} (g : α → β) (p₁ : α → OracleComp T Bool) (p₂ : β → OracleComp T Bool)
    (hp : ∀ x, CoinSimEquiv fwdU (p₂ (g x)) (p₁ x)) :
    ∀ xs : List α, CoinSimEquiv fwdU (anyML p₂ (xs.map g)) (anyML p₁ xs)
  | [] => CoinSimEquiv.refl _
  | x :: xs => by
    dsimp only [List.map_cons, anyML]
    exact (hp x).bind fun b => match b with
      | true => CoinSimEquiv.refl _
      | false => anyML_coinSimEquiv_hom fwdU g p₁ p₂ hp xs

private theorem mapML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → OracleComp T β₁) (f₂ : α₂ → OracleComp T β₂)
    (hf : ∀ x, CoinSimEquiv fwdU (f₂ (g x)) (h <$> f₁ x)) :
    ∀ xs : List α₁, CoinSimEquiv fwdU (mapML f₂ (xs.map g)) (List.map h <$> mapML f₁ xs)
  | [] => CoinSimEquiv.of_eq (by simp [mapML])
  | x :: xs => by
    dsimp only [List.map_cons, mapML]
    refine ((hf x).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left, map_bind]
    refine (CoinSimEquiv.refl (f₁ x)).bind fun y => ?_
    rw [map_bind]
    refine ((mapML_coinSimEquiv_hom fwdU g h f₁ f₂ hf xs).bind fun _ =>
      CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left]; exact CoinSimEquiv.of_eq (by simp)

private theorem consumeFirstML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α β : Type} (g : α → β)
    (p₁ : α → OracleComp T Bool) (p₂ : β → OracleComp T Bool)
    (mk₁ : α → α) (mk₂ : β → β)
    (hp : ∀ x, CoinSimEquiv fwdU (p₂ (g x)) (p₁ x))
    (hmk : ∀ x, mk₂ (g x) = g (mk₁ x)) :
    ∀ xs : List α,
      CoinSimEquiv fwdU (consumeFirstML p₂ mk₂ (xs.map g))
        (Prod.map id (List.map g) <$> consumeFirstML p₁ mk₁ xs)
  | [] => CoinSimEquiv.of_eq (by simp [consumeFirstML])
  | x :: xs => by
    dsimp only [List.map_cons, consumeFirstML]; rw [map_bind]
    refine (hp x).bind fun b => ?_
    cases b with
    | true => exact CoinSimEquiv.of_eq (by simp [hmk x])
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [map_bind]
      refine ((consumeFirstML_coinSimEquiv_hom fwdU g p₁ p₂ mk₁ mk₂ hp hmk xs).bind fun _ =>
        CoinSimEquiv.refl _).trans ?_
      rw [bind_map_left]; exact CoinSimEquiv.of_eq (by simp)

private theorem foldML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → OracleComp T β₁) (f₂ : α₂ → β₂ → OracleComp T β₂)
    (hf : ∀ x b, CoinSimEquiv fwdU (f₂ (g x) (h b)) (h <$> f₁ x b)) :
    ∀ (b : β₁) (xs : List α₁),
      CoinSimEquiv fwdU (foldML f₂ (h b) (xs.map g)) (h <$> foldML f₁ b xs)
  | _, [] => CoinSimEquiv.of_eq (by simp [foldML])
  | b, x :: xs => by
    dsimp only [List.map_cons, foldML]
    refine ((hf x b).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left, map_bind]
    exact (CoinSimEquiv.refl (f₁ x b)).bind fun b' =>
      foldML_coinSimEquiv_hom fwdU g h f₁ f₂ hf b' xs

theorem compilePureAuxComp_coinSimEquiv {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hOpE : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) x) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o x))
    (hSampEq : ∀ s x,
      CoinSimEquiv I₂.fwdU
        ((M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) x) (.cons aux .nil)))
        (toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x)))
    (hQueryEq : ∀ g x,
      CoinSimEquiv I₂.fwdU
        ((M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) x) (.cons aux .nil)))
        (toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _))))
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    CoinSimEquiv I₂.fwdU
      ((compilePureAuxComp M c).eval (mapEnvAux M.fSort toDen aux ρ))
      (toVal M.fSort toDen t <$> c.eval ρ) := by
  induction c with
  | ret e =>
    exact CoinSimEquiv.of_eq
      (by simp [compilePureAuxComp, Comp.eval, compilePureAuxExpr_eval M toDen aux hOpE e ρ])
  | bind c k ihc ihk =>
    dsimp only [compilePureAuxComp, Comp.eval]
    refine ((ihc ρ).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left, map_bind]
    exact (CoinSimEquiv.refl (c.eval ρ)).bind fun x => ihk (.cons x ρ)
  | ite b c d ihc ihd =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE b ρ]; dsimp only [toVal]
    cases b.eval ρ with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ihd ρ
    | true => simp only [↓reduceIte]; exact ihc ρ
  | caseOpt e n s ihn ihs =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE e ρ]; dsimp only [toVal]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE e ρ]; dsimp only [toVal]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | sample s e =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [pure_bind, compilePureAuxExpr_eval M toDen aux hOpE e ρ,
      callMacroAux_eval M.fSort toDen aux ρ]
    exact hSampEq s (e.eval ρ)
  | query g e =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [pure_bind, compilePureAuxExpr_eval M toDen aux hOpE e ρ,
      callMacroAux_eval M.fSort toDen aux ρ]
    exact hQueryEq g (e.eval ρ)
  | iter n e body ihb =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE e ρ]
    exact iterM_coinSimEquiv_hom I₂.fwdU (toVal M.fSort toDen _)
      (fun a => body.eval (.cons a ρ)) _ (fun a => ihb (.cons a ρ)) n (e.eval ρ)
  | findM K l p ihp =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ]; dsimp only [toVal]; rw [← List.map_take]
    exact findML_coinSimEquiv_hom I₂.fwdU (toVal M.fSort toDen _)
      (fun x => p.eval (.cons x ρ)) _ (fun x => (ihp (.cons x ρ)).trans
        (CoinSimEquiv.of_eq (show id <$> p.eval (.cons x ρ) = _ from id_map _)))
      ((l.eval ρ).take K)
  | anyM K l p ihp =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ]; dsimp only [toVal]; rw [← List.map_take]
    refine (anyML_coinSimEquiv_hom I₂.fwdU (toVal M.fSort toDen _)
      (fun x => p.eval (.cons x ρ)) _ (fun x => (ihp (.cons x ρ)).trans
        (CoinSimEquiv.of_eq (show id <$> p.eval (.cons x ρ) = _ from id_map _)))
      ((l.eval ρ).take K)).trans ?_
    exact CoinSimEquiv.of_eq (show _ = id <$> _ from (id_map _).symm)
  | mapM K l f ihf =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ]; dsimp only [toVal]; rw [← List.map_take]
    exact mapML_coinSimEquiv_hom I₂.fwdU (toVal M.fSort toDen _) (toVal M.fSort toDen _)
      (fun x => f.eval (.cons x ρ)) _ (fun x => ihf (.cons x ρ)) ((l.eval ρ).take K)
  | consumeFirstM K l p mk ihp =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ]; dsimp only [toVal]; rw [← List.map_take]
    exact consumeFirstML_coinSimEquiv_hom I₂.fwdU (toVal M.fSort toDen _)
      (fun x => p.eval (.cons x ρ)) _ (fun x => mk.eval (.cons x ρ)) _
      (fun x => (ihp (.cons x ρ)).trans
        (CoinSimEquiv.of_eq (show id <$> p.eval (.cons x ρ) = _ from id_map _)))
      (fun x => compilePureAuxExpr_eval M toDen aux hOpE mk (.cons x ρ)) ((l.eval ρ).take K)
  | foldM K l z f ihf =>
    dsimp only [compilePureAuxComp, Comp.eval]
    rw [compilePureAuxExpr_eval M toDen aux hOpE l ρ,
      compilePureAuxExpr_eval M toDen aux hOpE z ρ]
    dsimp only [toVal]; rw [← List.map_take]
    exact foldML_coinSimEquiv_hom I₂.fwdU (toVal M.fSort toDen _) (toVal M.fSort toDen _)
      (fun x acc => f.eval (.cons x (.cons acc ρ))) _
      (fun x acc => ihf (.cons x (.cons acc ρ))) (z.eval ρ) ((l.eval ρ).take K)

end PureAuxCoinSim

section CompilePureAuxRed

variable {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
  {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
  {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
  {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G} {auxT : Ty S₂}

/-- Adapter expressions reshaping source/target reduction boundary types and game codecs, with
query-aware response adaptation `adaptR : Expr O₂ [mapTy fSort C₁.R, C₂.Q] C₂.R`. -/
structure PureAuxAdapters (fSort : S₁.Base → Ty S₂) (O₂ : Ops S₂)
    (C₁ : GameCodec S₁ G) (C₂ : GameCodec S₂ G) (auxT : Ty S₂)
    (rIn₁ aIn₁ aOut₁ out₁ : Ty S₁) (rIn₂ aIn₂ aOut₂ out₂ : Ty S₂) where
  splitIn : Expr O₂ [rIn₂] (.prod (mapTy fSort rIn₁) auxT)
  adaptAIn : Expr O₂ [mapTy fSort aIn₁] aIn₂
  adaptQ : Expr O₂ [C₂.Q] (mapTy fSort C₁.Q)
  adaptR : Expr O₂ [mapTy fSort C₁.R, C₂.Q] C₂.R
  adaptAOut : Expr O₂ [aOut₂] (mapTy fSort aOut₁)
  adaptOut : Expr O₂ [mapTy fSort out₁] out₂

def callAdaptR {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T) :
    Expr O₂ (r₁T :: a :: b :: c :: d :: e :: [q₂T]) r₂T :=
  Expr.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ (.succ (.succ (.succ (.succ (.succ .zero)))))
      | .succ (.succ w) => nomatch w)
    adR

@[simp] theorem callAdaptR_cost {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T) :
    (callAdaptR (a := a) (b := b) (c := c) (d := d) (e := e) adR).cost = adR.cost :=
  Expr.renameM_cost _ adR

@[simp] theorem callAdaptR_size {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T) :
    (callAdaptR (a := a) (b := b) (c := c) (d := d) (e := e) adR).size = adR.size :=
  Expr.renameM_size _ adR

theorem callAdaptR_eval {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T)
    (r₁ : r₁T.denote) (x₁ : a.denote) (x₂ : b.denote) (x₃ : c.denote)
    (x₄ : d.denote) (x₅ : e.denote) (q₂ : q₂T.denote) :
    (callAdaptR (a := a) (b := b) (c := c) (d := d) (e := e) adR).eval
        (.cons r₁ (.cons x₁ (.cons x₂ (.cons x₃ (.cons x₄ (.cons x₅ (.cons q₂ .nil))))))) =
      adR.eval (.cons r₁ (.cons q₂ .nil)) := by
  refine Expr.renameM_eval adR ?_
  intro u v
  cases v with
  | zero => rfl
  | succ v =>
    cases v with
    | zero => rfl
    | succ w => nomatch w

def compilePureAuxRed (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁) :
    CostedReduction O₂ I₂ G C₂ rIn₂ aIn₂ aOut₂ out₂ where
  σ := .prod (mapTy M.fSort R.σ) auxT
  init :=
    .bind (.ret A.splitIn)
      (.bind (.ret (.snd (.var .zero)))
        (.bind (.ret (.fst (.var (.succ .zero))))
          (.bind
            (Comp.wkTop2 (compilePureAuxComp M R.init))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptAIn))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ .zero)))))))))
  handle :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptQ)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compilePureAuxComp M R.handle))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (callAdaptR A.adaptR))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ (.succ .zero))))))))))
  finish :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptAOut)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compilePureAuxComp M R.finish))
            (.ret
              (.letE (.var .zero) (Expr.wkTop1 A.adaptOut))))))

theorem compilePureAuxRed_totalQueries_le (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hSampQ : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQueryQ : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    (q : ℕ) :
    (compilePureAuxRed M A R).totalQueries w₂ ws₂ q ≤ R.totalQueries w₁ ws₁ q := by
  have hi := compilePureAuxComp_queries_le M w₁ ws₁ w₂ ws₂ hSampQ hQueryQ R.init
  have hh := compilePureAuxComp_queries_le M w₁ ws₁ w₂ ws₂ hSampQ hQueryQ R.handle
  have hf := compilePureAuxComp_queries_le M w₁ ws₁ w₂ ws₂ hSampQ hQueryQ R.finish
  have hmul := Nat.mul_le_mul_left q hh
  simp only [CostedReduction.totalQueries, compilePureAuxRed, Comp.queries, Comp.renameM_queries,
    zero_add, add_zero]
  omega

private theorem simulateQ_state_hom
    {σ₁ σ₂ : Type} (proj : σ₁ → σ₂)
    {impl₁ : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T))}
    {impl₂ : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T))}
    (hStep : ∀ q s₁, (impl₂ q).run (proj s₁) = Prod.map id proj <$> (impl₁ q).run s₁)
    {α : Type} (oa : OracleComp (unifSpec + G) α) :
    ∀ s₁ : σ₁,
      (simulateQ impl₂ oa).run (proj s₁) = Prod.map id proj <$> (simulateQ impl₁ oa).run s₁ := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s₁; simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s₁
    simp only [simulateQ_query_bind, StateT.run_bind]
    change
      (do let p ← (impl₂ q).run (proj s₁); (simulateQ impl₂ (mx p.1)).run p.2) =
        Prod.map id proj <$>
          (do let p ← (impl₁ q).run s₁; (simulateQ impl₁ (mx p.1)).run p.2)
    rw [hStep q s₁, bind_map_left, map_bind]
    exact bind_congr fun p => ih p.1 p.2

private theorem simulateQ_state_coinSimEquiv
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {σ₁ σ₂ : Type} (proj : σ₁ → σ₂)
    {impl₁ : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T))}
    {impl₂ : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T))}
    (hStep : ∀ q s₁,
      CoinSimEquiv fwdU ((impl₂ q).run (proj s₁)) (Prod.map id proj <$> (impl₁ q).run s₁))
    {α : Type} (oa : OracleComp (unifSpec + G) α) :
    ∀ s₁ : σ₁,
      CoinSimEquiv fwdU ((simulateQ impl₂ oa).run (proj s₁))
        (Prod.map id proj <$> (simulateQ impl₁ oa).run s₁) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s₁; exact CoinSimEquiv.of_eq (by simp)
  | query_bind q mx ih =>
    intro s₁
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    change CoinSimEquiv fwdU
      ((impl₂ q).run (proj s₁) >>= fun p => (simulateQ impl₂ (mx p.1)).run p.2)
      (Prod.map id proj <$> ((impl₁ q).run s₁ >>= fun p => (simulateQ impl₁ (mx p.1)).run p.2))
    rw [map_bind]
    refine ((hStep q s₁).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left]
    exact (CoinSimEquiv.refl ((impl₁ q).run s₁)).bind fun p => ih p.1 p.2

/-- Strict `.eval` agreement for `compilePureAuxRed` when all sampler and query macros agree
by `=`. -/
theorem compilePureAuxRed_eval (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (Ad : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote)
    (x₂ : rIn₂.denote) (x₁ : rIn₁.denote) (aux : auxT.denote)
    (hSplit : Ad.splitIn.eval (.cons x₂ .nil) = (toVal M.fSort toDen rIn₁ x₁, aux))
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOpE : ∀ o z,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) z) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o z))
    (hSampE : ∀ s z,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s z))
    (hQueryE : ∀ g z,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g z <$> (liftM (T.query (I₁.enc g z)) : OracleComp T _)))
    (hQ : ∀ t : κ,
      Ad.adaptQ.eval (.cons (C₂.qenc t) .nil) = toVal M.fSort toDen C₁.Q (C₁.qenc t))
    (hR : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R r₁) (.cons (C₂.qenc t) .nil))) =
        C₁.rdec t r₁)
    (adv₁ : aIn₁.denote → OracleComp (unifSpec + G) aOut₁.denote)
    (adv₂ : aIn₂.denote → OracleComp (unifSpec + G) aOut₂.denote)
    (toOut : aOut₁.denote → aOut₂.denote)
    (hAdv : ∀ a₁ : aIn₁.denote,
      adv₂ (Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ a₁) .nil)) = toOut <$> adv₁ a₁)
    (hAOut : ∀ b₁ : aOut₁.denote,
      Ad.adaptAOut.eval (.cons (toOut b₁) .nil) = toVal M.fSort toDen aOut₁ b₁)
    {outEq : out₁.denote → out₂.denote}
    (hOut : ∀ y₁ : out₁.denote,
      Ad.adaptOut.eval (.cons (toVal M.fSort toDen out₁ y₁) .nil) = outEq y₁) :
    (compilePureAuxRed M Ad R).eval adv₂ x₂ = outEq <$> R.eval adv₁ x₁ := by
  let mkSt : R.σ.denote → (compilePureAuxRed M Ad R).σ.denote :=
    fun s => (toVal M.fSort toDen R.σ s, aux)
  have hInit :
      (compilePureAuxRed M Ad R).init.eval (.cons x₂ .nil) =
        (fun (p : (aIn₁.prod R.σ).denote) =>
          ((Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ p.1) .nil),
            mkSt p.2) : (aIn₂.prod (compilePureAuxRed M Ad R).σ).denote)) <$>
          R.init.eval (.cons x₁ .nil) := by
    simp only [compilePureAuxRed, Comp.eval, pure_bind, Expr.eval, Env.get, hSplit]
    rw [Comp.wkTop2_eval]
    change (do
      let x ← (compilePureAuxComp M R.init).eval (mapEnvAux M.fSort toDen aux (.cons x₁ .nil))
      _) = _
    rw [compilePureAuxComp_eval M toDen aux hOpE hSampE hQueryE R.init (.cons x₁ .nil),
      bind_map_left]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun p => ?_
    congr 1; congr 1
    dsimp only [toVal]
    exact Expr.wkTop1_eval Ad.adaptAIn _ _
  have hStep :
      ∀ (q : (unifSpec + G).Domain) (s₁ : R.σ.denote),
        ((compilePureAuxRed M Ad R).impl q).run (mkSt s₁) =
          Prod.map id mkSt <$> (R.impl q).run s₁ := by
    intro q s₁
    rcases q with n | t
    · change
        (StateT.lift (I₂.fwdU n)).run (mkSt s₁) =
          Prod.map id mkSt <$> (StateT.lift (I₁.fwdU n)).run s₁
      rw [StateT.run_lift, StateT.run_lift, hFwdU n]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]
    · simp only [CostedReduction.impl, handlerImpl, StateT.run_mk, compilePureAuxRed,
        Comp.eval, pure_bind, Expr.eval, Env.get, mkSt]
      have hq' :
          (Expr.wkTop1 Ad.adaptQ).eval
            (Env.cons (C₂.qenc t)
              (Env.cons aux
                (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
                  (toVal M.fSort toDen R.σ s₁, aux) (Env.cons (C₂.qenc t) Env.nil)))) =
            toVal M.fSort toDen C₁.Q (C₁.qenc t) := by
        rw [Expr.wkTop1_eval]; exact hQ t
      rw [hq', Comp.wkTop3_eval]
      have hm :
          Env.cons (toVal M.fSort toDen R.σ s₁)
            (Env.cons (toVal M.fSort toDen C₁.Q (C₁.qenc t)) (Env.cons aux Env.nil)) =
            mapEnvAux M.fSort toDen aux (.cons s₁ (.cons (C₁.qenc t) .nil)) := rfl
      dsimp only [compilePureAuxRed, Ty.denote]
      rw [hm, compilePureAuxComp_eval M toDen aux hOpE hSampE hQueryE R.handle
        (.cons s₁ (.cons (C₁.qenc t) .nil)), bind_map_left, bind_assoc, map_bind]
      refine OracleComp.bind_congr' rfl fun p => ?_
      simp only [pure_bind, map_pure, Prod.map, id_eq, toVal]
      congr 1; congr 1
      rw [callAdaptR_eval]
      exact hR t p.1
  unfold CostedReduction.eval
  rw [hInit, bind_map_left, map_bind]
  refine OracleComp.bind_congr' rfl fun p => ?_
  rcases p with ⟨a₁, s₁⟩
  dsimp only
  rw [hAdv a₁, simulateQ_map, StateT.run_map,
    simulateQ_state_hom mkSt hStep (adv₁ a₁) s₁]
  simp only [bind_map_left, map_bind, Prod.map, id_eq]
  refine OracleComp.bind_congr' rfl fun p' => ?_
  rcases p' with ⟨b₁, s₁'⟩
  dsimp only
  simp only [compilePureAuxRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt]
  have hb' :
      (Expr.wkTop1 Ad.adaptAOut).eval
        (Env.cons (toOut b₁)
          (Env.cons aux
            (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
              (toVal M.fSort toDen R.σ s₁', aux) (Env.cons (toOut b₁) Env.nil)))) =
        toVal M.fSort toDen aOut₁ b₁ := by
    rw [Expr.wkTop1_eval]; exact hAOut b₁
  rw [hb', Comp.wkTop3_eval]
  have hm' :
      Env.cons (toVal M.fSort toDen R.σ s₁')
        (Env.cons (toVal M.fSort toDen aOut₁ b₁) (Env.cons aux Env.nil)) =
        mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil)) := rfl
  rw [hm', compilePureAuxComp_eval M toDen aux hOpE hSampE hQueryE R.finish
      (.cons s₁' (.cons b₁ .nil)),
    bind_map_left, map_eq_bind_pure_comp, Function.comp_def]
  refine OracleComp.bind_congr' rfl fun y₁ => ?_
  congr 1
  rw [Expr.wkTop1_eval, hOut y₁]

/-- `CoinSimEquiv` evaluation agreement for `compilePureAuxRed` under distributional sampler
macros and `CoinSimEquiv`-related input adversaries. -/
theorem compilePureAuxRed_coinSimEquiv (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (Ad : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote)
    (x₂ : rIn₂.denote) (x₁ : rIn₁.denote) (aux : auxT.denote)
    (hSplit : Ad.splitIn.eval (.cons x₂ .nil) = (toVal M.fSort toDen rIn₁ x₁, aux))
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOpE : ∀ o z,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) z) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o z))
    (hSampEq : ∀ s z,
      CoinSimEquiv I₂.fwdU
        ((M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) z) (.cons aux .nil)))
        (toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s z)))
    (hQueryEq : ∀ g z,
      CoinSimEquiv I₂.fwdU
        ((M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) z) (.cons aux .nil)))
        (toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g z <$> (liftM (T.query (I₁.enc g z)) : OracleComp T _))))
    (hQ : ∀ t : κ,
      Ad.adaptQ.eval (.cons (C₂.qenc t) .nil) = toVal M.fSort toDen C₁.Q (C₁.qenc t))
    (hR : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R r₁) (.cons (C₂.qenc t) .nil))) =
        C₁.rdec t r₁)
    (adv₁ : aIn₁.denote → OracleComp (unifSpec + G) aOut₁.denote)
    (adv₂ : aIn₂.denote → OracleComp (unifSpec + G) aOut₂.denote)
    (toOut : aOut₁.denote → aOut₂.denote)
    (hAdv : ∀ a₁ : aIn₁.denote,
      CoinSimEquiv (fun n => query (spec := unifSpec + G) (.inl n))
        (adv₂ (Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ a₁) .nil)))
        (toOut <$> adv₁ a₁))
    (hAOut : ∀ b₁ : aOut₁.denote,
      Ad.adaptAOut.eval (.cons (toOut b₁) .nil) = toVal M.fSort toDen aOut₁ b₁)
    {outEq : out₁.denote → out₂.denote}
    (hOut : ∀ y₁ : out₁.denote,
      Ad.adaptOut.eval (.cons (toVal M.fSort toDen out₁ y₁) .nil) = outEq y₁) :
    CoinSimEquiv I₂.fwdU ((compilePureAuxRed M Ad R).eval adv₂ x₂) (outEq <$> R.eval adv₁ x₁) := by
  let mkSt : R.σ.denote → (compilePureAuxRed M Ad R).σ.denote :=
    fun s => (toVal M.fSort toDen R.σ s, aux)
  have hInit :
      CoinSimEquiv I₂.fwdU
        ((compilePureAuxRed M Ad R).init.eval (.cons x₂ .nil))
        ((fun (p : (aIn₁.prod R.σ).denote) =>
          ((Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ p.1) .nil),
            mkSt p.2) : (aIn₂.prod (compilePureAuxRed M Ad R).σ).denote)) <$>
          R.init.eval (.cons x₁ .nil)) := by
    simp only [compilePureAuxRed, Comp.eval, pure_bind, Expr.eval, Env.get, hSplit]
    rw [Comp.wkTop2_eval]
    change CoinSimEquiv I₂.fwdU
      ((compilePureAuxComp M R.init).eval (mapEnvAux M.fSort toDen aux (.cons x₁ .nil)) >>= _)
      _
    refine ((compilePureAuxComp_coinSimEquiv M toDen aux hOpE hSampEq hQueryEq R.init
      (.cons x₁ .nil)).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left]
    refine CoinSimEquiv.of_eq ?_
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun p => ?_
    congr 1; congr 1
    dsimp only [toVal]
    exact Expr.wkTop1_eval Ad.adaptAIn _ _
  have hStep :
      ∀ (q : (unifSpec + G).Domain) (s₁ : R.σ.denote),
        CoinSimEquiv I₂.fwdU
          (((compilePureAuxRed M Ad R).impl q).run (mkSt s₁))
          (Prod.map id mkSt <$> (R.impl q).run s₁) := by
    intro q s₁
    rcases q with n | t
    · refine CoinSimEquiv.of_eq ?_
      change
        (StateT.lift (I₂.fwdU n)).run (mkSt s₁) =
          Prod.map id mkSt <$> (StateT.lift (I₁.fwdU n)).run s₁
      rw [StateT.run_lift, StateT.run_lift, hFwdU n]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]
    · simp only [CostedReduction.impl, handlerImpl, StateT.run_mk, compilePureAuxRed,
        Comp.eval, pure_bind, bind_assoc, Expr.eval, Env.get, mkSt]
      have hq' :
          (Expr.wkTop1 Ad.adaptQ).eval
            (Env.cons (C₂.qenc t)
              (Env.cons aux
                (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
                  (toVal M.fSort toDen R.σ s₁, aux) (Env.cons (C₂.qenc t) Env.nil)))) =
            toVal M.fSort toDen C₁.Q (C₁.qenc t) := by
        rw [Expr.wkTop1_eval]; exact hQ t
      rw [hq', Comp.wkTop3_eval]
      have hm :
          Env.cons (toVal M.fSort toDen R.σ s₁)
            (Env.cons (toVal M.fSort toDen C₁.Q (C₁.qenc t)) (Env.cons aux Env.nil)) =
            mapEnvAux M.fSort toDen aux (.cons s₁ (.cons (C₁.qenc t) .nil)) := rfl
      dsimp only [compilePureAuxRed, Ty.denote]
      rw [hm, map_bind]
      refine ((compilePureAuxComp_coinSimEquiv M toDen aux hOpE hSampEq hQueryEq R.handle
        (.cons s₁ (.cons (C₁.qenc t) .nil))).bind fun _ => CoinSimEquiv.refl _).trans ?_
      rw [bind_map_left]
      refine CoinSimEquiv.of_eq ?_
      refine bind_congr fun p => ?_
      simp only [map_pure, Prod.map, id_eq, toVal]
      congr 1; congr 1
      rw [callAdaptR_eval]
      exact hR t p.1
  refine ⟨fun {σc} impl himpl sc => ?_⟩
  unfold CostedReduction.eval
  simp only [map_bind, simulateQ_bind, StateT.run_bind]
  refine ((hInit.run_eq impl himpl sc).bind fun _ => EvalDistEq.rfl).trans ?_
  simp only [simulateQ_map, StateT.run_map, bind_map_left]
  refine (EvalDistEq.rfl (m := ProbComp)).bind fun p0 => ?_
  rcases p0 with ⟨⟨a₁, s₁⟩, sc₁⟩
  dsimp only
  let R₂ := compilePureAuxRed M Ad R
  have hAdvRun :
      (simulateQ impl
        ((simulateQ R₂.impl
          (adv₂ (Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ a₁) .nil)))).run
          (mkSt s₁))).run sc₁ =ᵈ
      (simulateQ impl
        ((simulateQ R₂.impl (toOut <$> adv₁ a₁)).run (mkSt s₁))).run sc₁ := by
    rw [simulateQ_compCoinImpl_run, simulateQ_compCoinImpl_run]
    exact ((hAdv a₁).run_eq (compCoinImpl R₂.impl impl)
      (validCoinSim_compCoinImpl R₂ himpl) (mkSt s₁, sc₁)).map _
  refine (hAdvRun.bind fun _ => EvalDistEq.rfl).trans ?_
  rw [simulateQ_map, StateT.run_map]
  have hHom := (simulateQ_state_coinSimEquiv I₂.fwdU mkSt hStep (adv₁ a₁) s₁).map
    (Prod.map toOut id)
  rw [Functor.map_map] at hHom
  refine ((hHom.run_eq impl himpl sc₁).bind fun _ => EvalDistEq.rfl).trans ?_
  simp only [simulateQ_map, StateT.run_map, bind_map_left]
  refine (EvalDistEq.rfl (m := ProbComp)).bind fun p1 => ?_
  rcases p1 with ⟨⟨b₁, s₁'⟩, sc₂⟩
  dsimp only [Prod.map, id_eq, R₂]
  simp only [compilePureAuxRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt]
  have hb' :
      (Expr.wkTop1 Ad.adaptAOut).eval
        (Env.cons (toOut b₁)
          (Env.cons aux
            (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
              (toVal M.fSort toDen R.σ s₁', aux) (Env.cons (toOut b₁) Env.nil)))) =
        toVal M.fSort toDen aOut₁ b₁ := by
    rw [Expr.wkTop1_eval]; exact hAOut b₁
  rw [hb', Comp.wkTop3_eval]
  have hm' :
      Env.cons (toVal M.fSort toDen R.σ s₁')
        (Env.cons (toVal M.fSort toDen aOut₁ b₁) (Env.cons aux Env.nil)) =
        mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil)) := rfl
  rw [hm']
  have hFinL :
      ((compilePureAuxComp M R.finish).eval (mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil))) >>=
        fun z => pure ((Expr.wkTop1 Ad.adaptOut).eval
          (Env.cons z (Env.cons z (Env.cons (toVal M.fSort toDen R.σ s₁')
            (Env.cons (toVal M.fSort toDen aOut₁ b₁)
              (Env.cons aux (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
                (toVal M.fSort toDen R.σ s₁', aux)
                (Env.cons (toOut b₁) Env.nil))))))))) =
      (fun z => Ad.adaptOut.eval (.cons z .nil)) <$>
        (compilePureAuxComp M R.finish).eval
          (mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil))) := by
    rw [map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun z => ?_
    rw [Expr.wkTop1_eval]
  have hFinR :
      (fun z => Ad.adaptOut.eval (.cons z .nil)) <$>
        (toVal M.fSort toDen out₁ <$> R.finish.eval (.cons s₁' (.cons b₁ .nil))) =
      outEq <$> R.finish.eval (.cons s₁' (.cons b₁ .nil)) := by
    rw [Functor.map_map]
    congr 1
    funext y₁
    exact hOut y₁
  have hFin := (compilePureAuxComp_coinSimEquiv M toDen aux hOpE hSampEq hQueryEq R.finish
    (.cons s₁' (.cons b₁ .nil))).map (fun z => Ad.adaptOut.eval (.cons z .nil))
  rw [← hFinL, hFinR] at hFin
  have hFinRun := hFin.run_eq impl himpl sc₂
  rw [simulateQ_map, StateT.run_map] at hFinRun
  exact hFinRun

end CompilePureAuxRed

/-! ## Weighted AST cost and `bits` monotonicity -/

section WeightedCost

theorem bits_mono {m n : ℕ} (h : m ≤ n) : bits m ≤ bits n :=
  Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem bits_lt_pow {m k : ℕ} (hk : 0 < k) (h : m < 2 ^ k) : bits m ≤ k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [bits]; omega
  · have hlog : Nat.log 2 m < k := Nat.log_lt_of_lt_pow (Nat.ne_of_gt hm) h
    unfold bits; omega

theorem bits_add_const (n k : ℕ) : bits (n + k) ≤ bits n + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsucc : bits (n + k + 1) ≤ bits (n + k) + 1 := by
      rcases Nat.eq_zero_or_pos (n + k) with h0 | hpos
      · simp [h0, bits]
      · unfold bits
        have hlt : n + k + 1 < 2 ^ (Nat.log 2 (n + k) + 2) := by
          have h1 : n + k < 2 ^ (Nat.log 2 (n + k) + 1) :=
            Nat.lt_pow_succ_log_self (by decide) (n + k)
          have h2 : 2 ^ (Nat.log 2 (n + k) + 2) = 2 ^ (Nat.log 2 (n + k) + 1) * 2 :=
            pow_succ 2 (Nat.log 2 (n + k) + 1)
          omega
        have hlog : Nat.log 2 (n + k + 1) < Nat.log 2 (n + k) + 2 :=
          Nat.log_lt_of_lt_pow (by omega) hlt
        omega
    rw [← Nat.add_assoc]
    omega

/-- Parameterized static cost of `Expr O Γ t` with custom per-op weight `opC`. -/
def exprCostW {S : Sig} {O : Ops S} (opC : O.Op → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .none | _, _, .nil => 1
  | _, _, .nat n => bits n
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b
  | _, _, .and a b | _, _, .pair a b | _, _, .cons a b | _, _, .take a b
  | _, _, .letE a b => exprCostW opC a + exprCostW opC b + 1
  | _, _, .mulK k a | _, _, .divK k a | _, _, .modK k a => exprCostW opC a + bits k
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a
  | _, _, .some a | _, _, .len a | _, _, .tconst a => exprCostW opC a + 1
  | _, _, .ite c a b | _, _, .caseOpt c a b | _, _, .caseSum c a b =>
    exprCostW opC c + max (exprCostW opC a) (exprCostW opC b) + 1
  | _, _, .op o a => exprCostW opC a + opC o
  | _, _, .appendL K a b => exprCostW opC a + exprCostW opC b + K + 1
  | _, _, .findB K l p | _, _, .anyB K l p | _, _, .mapB K l p =>
    exprCostW opC l + K * (exprCostW opC p + 1) + 1
  | _, _, .foldrB K l z f =>
    exprCostW opC l + exprCostW opC z + K * (exprCostW opC f + 1) + 1
  | _, _, .tget m i => exprCostW opC m + exprCostW opC i + 64
  | _, _, .tset m i a => exprCostW opC m + exprCostW opC i + exprCostW opC a + 128

/-- Parameterized static cost of `Comp O I Γ t` with custom op, sampler, and query weights. -/
def compCostW {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => exprCostW opC e + 1
  | _, _, .bind c k => compCostW opC sC qC c + compCostW opC sC qC k + 1
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    exprCostW opC b + max (compCostW opC sC qC c) (compCostW opC sC qC d) + 1
  | _, _, .sample s e => exprCostW opC e + sC s
  | _, _, .query g e => exprCostW opC e + qC g
  | _, _, .iter n e body => exprCostW opC e + n * (compCostW opC sC qC body + 1) + 1
  | _, _, .findM K l p | _, _, .anyM K l p | _, _, .mapM K l p =>
    exprCostW opC l + K * (compCostW opC sC qC p + 1) + 1
  | _, _, .consumeFirstM K l p mk =>
    exprCostW opC l + K * (compCostW opC sC qC p + exprCostW opC mk + 1) + 1
  | _, _, .foldM K l z f =>
    exprCostW opC l + exprCostW opC z + K * (compCostW opC sC qC f + 1) + 1

@[simp] theorem exprCostW_rename {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (e : Expr O Γ t) :
    exprCostW opC (Expr.renameM ξ e) = exprCostW opC e := by
  induction e generalizing Δ <;> simp [Expr.renameM, exprCostW, *]

@[simp] theorem compCostW_rename {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (c : Comp O I Γ t) :
    compCostW opC sC qC (Comp.renameM ξ c) = compCostW opC sC qC c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compCostW, *]

@[simp] theorem exprCostW_eq_cost {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) :
    exprCostW O.cost e = e.cost := by
  induction e <;> simp [exprCostW, Expr.cost, *]

@[simp] theorem compCostW_eq_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compCostW O.cost I.smp.sCost I.qCost c = c.cost := by
  induction c <;> simp [compCostW, Comp.cost, *]

theorem exprCostW_mono {S : Sig} {O : Ops S} {opC₁ opC₂ : O.Op → ℕ}
    (hOp : ∀ o, opC₁ o ≤ opC₂ o) {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    exprCostW opC₁ e ≤ exprCostW opC₂ e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2
  | and _ _ ih1 ih2 | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2
  | letE _ _ ih1 ih2 | appendL _ _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    simp only [exprCostW]; omega
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [exprCostW]; omega
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb =>
    have hm := max_le_max iha ihb
    simp only [exprCostW]; omega
  | op o _ iha =>
    have ho := hOp o
    simp only [exprCostW]; omega
  | findB K _ _ ihl ihp | anyB K _ _ ihl ihp | mapB K _ _ ihl ihp =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihp 1)
    simp only [exprCostW]; omega
  | foldrB K _ _ _ ihl ihz ihf =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihf 1)
    simp only [exprCostW]; omega
  | tset _ _ _ ih1 ih2 ih3 =>
    simp only [exprCostW]; omega

theorem compCostW_mono {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {opC₁ opC₂ : O.Op → ℕ} {sC₁ sC₂ : I.smp.Samp → ℕ} {qC₁ qC₂ : I.Tag → ℕ}
    (hOp : ∀ o, opC₁ o ≤ opC₂ o)
    (hS : ∀ s, sC₁ s ≤ sC₂ s)
    (hQ : ∀ g, qC₁ g ≤ qC₂ g)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compCostW opC₁ sC₁ qC₁ c ≤ compCostW opC₂ sC₂ qC₂ c := by
  induction c with
  | ret e =>
    have he := exprCostW_mono hOp e
    simp only [compCostW]; omega
  | bind _ _ ihc ihk =>
    simp only [compCostW]; omega
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := exprCostW_mono hOp b
    have hm := max_le_max ihc ihd
    simp only [compCostW]; omega
  | sample s e =>
    have he := exprCostW_mono hOp e
    have hs := hS s
    simp only [compCostW]; omega
  | query g e =>
    have he := exprCostW_mono hOp e
    have hq := hQ g
    simp only [compCostW]; omega
  | iter n e _ ihb =>
    have he := exprCostW_mono hOp e
    have hm := Nat.mul_le_mul_left n (Nat.add_le_add_right ihb 1)
    simp only [compCostW]; omega
  | findM K l _ ihp | anyM K l _ ihp | mapM K l _ ihp =>
    have hl := exprCostW_mono hOp l
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihp 1)
    simp only [compCostW]; omega
  | consumeFirstM K l _ mk ihp =>
    have hl := exprCostW_mono hOp l
    have hmk := exprCostW_mono hOp mk
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right (Nat.add_le_add ihp hmk) 1)
    simp only [compCostW]; omega
  | foldM K l z _ ihf =>
    have hl := exprCostW_mono hOp l
    have hz := exprCostW_mono hOp z
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihf 1)
    simp only [compCostW]; omega

theorem compilePureAuxExpr_cost_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) (opC : O₁.Op → ℕ)
    (hOp : ∀ o, (M.opMacro o).cost + 1 ≤ opC o)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureAuxExpr M e).cost ≤ exprCostW opC e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb
  | and _ _ iha ihb | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb
  | letE _ _ iha ihb | appendL _ _ _ iha ihb | tget _ _ iha ihb =>
    simp only [compilePureAuxExpr, Expr.cost, exprCostW]; omega
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | len _ iha | tconst _ iha =>
    simp only [compilePureAuxExpr, Expr.cost, exprCostW]; omega
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb =>
    have hm := max_le_max iha ihb
    simp only [compilePureAuxExpr, Expr.cost, exprCostW]; omega
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureAuxExpr, Expr.cost, callPureMacroAux_cost, exprCostW]; omega
  | findB K _ _ ihl ihp | anyB K _ _ ihl ihp | mapB K _ _ ihl ihp =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihp 1)
    simp only [compilePureAuxExpr, Expr.cost, exprCostW]; omega
  | foldrB K _ _ _ ihl ihz ihf =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihf 1)
    simp only [compilePureAuxExpr, Expr.cost, exprCostW]; omega
  | tset _ _ _ ihm ihi iha =>
    simp only [compilePureAuxExpr, Expr.cost, exprCostW]; omega

theorem compilePureAuxComp_cost_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (opC : O₁.Op → ℕ) (sC : I₁.smp.Samp → ℕ) (qC : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).cost + 1 ≤ opC o)
    (hSamp : ∀ s, (M.sampMacro s).cost + 2 ≤ sC s)
    (hQuery : ∀ g, (M.queryMacro g).cost + 2 ≤ qC g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureAuxComp M c).cost ≤ compCostW opC sC qC c := by
  induction c with
  | ret e =>
    have he := compilePureAuxExpr_cost_le M opC hOp e
    simp only [compilePureAuxComp, Comp.cost, compCostW]; omega
  | bind _ _ ihc ihk =>
    simp only [compilePureAuxComp, Comp.cost, compCostW]; omega
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := compilePureAuxExpr_cost_le M opC hOp b
    have hm := max_le_max ihc ihd
    simp only [compilePureAuxComp, Comp.cost, compCostW]; omega
  | sample s e =>
    have he := compilePureAuxExpr_cost_le M opC hOp e
    have hs := hSamp s
    simp only [compilePureAuxComp, Comp.cost, callMacroAux_cost, compCostW]; omega
  | query g e =>
    have he := compilePureAuxExpr_cost_le M opC hOp e
    have hq := hQuery g
    simp only [compilePureAuxComp, Comp.cost, callMacroAux_cost, compCostW]; omega
  | iter n e _ ihb =>
    have he := compilePureAuxExpr_cost_le M opC hOp e
    have hm := Nat.mul_le_mul_left n (Nat.add_le_add_right ihb 1)
    simp only [compilePureAuxComp, Comp.cost, compCostW]; omega
  | findM K l _ ihp | anyM K l _ ihp | mapM K l _ ihp =>
    have hl := compilePureAuxExpr_cost_le M opC hOp l
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihp 1)
    simp only [compilePureAuxComp, Comp.cost, compCostW]; omega
  | consumeFirstM K l _ mk ihp =>
    have hl := compilePureAuxExpr_cost_le M opC hOp l
    have hmk := compilePureAuxExpr_cost_le M opC hOp mk
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right (Nat.add_le_add ihp hmk) 1)
    simp only [compilePureAuxComp, Comp.cost, compCostW]; omega
  | foldM K l z _ ihf =>
    have hl := compilePureAuxExpr_cost_le M opC hOp l
    have hz := compilePureAuxExpr_cost_le M opC hOp z
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihf 1)
    simp only [compilePureAuxComp, Comp.cost, compCostW]; omega

theorem compilePureAuxRed_totalCost_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (opC : O₁.Op → ℕ) (sC : I₁.smp.Samp → ℕ) (qC : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).cost + 1 ≤ opC o)
    (hSamp : ∀ s, (M.sampMacro s).cost + 2 ≤ sC s)
    (hQuery : ∀ g, (M.queryMacro g).cost + 2 ≤ qC g)
    (q : ℕ) :
    (compilePureAuxRed M A R).totalCost q ≤
      (compCostW opC sC qC R.init + A.splitIn.cost + A.adaptAIn.cost + 24) +
      q * max I₂.uCost
        (compCostW opC sC qC R.handle + A.adaptQ.cost + A.adaptR.cost + C₂.codecCost + 28) +
      (compCostW opC sC qC R.finish + A.adaptAOut.cost + A.adaptOut.cost + 22) := by
  have hi := compilePureAuxComp_cost_le M opC sC qC hOp hSamp hQuery R.init
  have hh := compilePureAuxComp_cost_le M opC sC qC hOp hSamp hQuery R.handle
  have hf := compilePureAuxComp_cost_le M opC sC qC hOp hSamp hQuery R.finish
  have hinit :
      (compilePureAuxRed M A R).init.cost ≤
        compCostW opC sC qC R.init + A.splitIn.cost + A.adaptAIn.cost + 24 := by
    simp only [compilePureAuxRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hhandle :
      (compilePureAuxRed M A R).handle.cost ≤
        compCostW opC sC qC R.handle + A.adaptQ.cost + A.adaptR.cost + 28 := by
    simp only [compilePureAuxRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, callAdaptR_cost,
      Expr.cost]
    omega
  have hfinish :
      (compilePureAuxRed M A R).finish.cost ≤
        compCostW opC sC qC R.finish + A.adaptAOut.cost + A.adaptOut.cost + 22 := by
    simp only [compilePureAuxRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hmax :
      max I₂.uCost ((compilePureAuxRed M A R).handle.cost + C₂.codecCost) ≤
      max I₂.uCost (compCostW opC sC qC R.handle + A.adaptQ.cost + A.adaptR.cost +
        C₂.codecCost + 28) :=
    max_le_max le_rfl (by omega)
  have hmul := Nat.mul_le_mul_left q hmax
  dsimp only [CostedReduction.totalCost]
  omega

theorem compilePureAuxExpr_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (S_max : ℕ) (hS : 1 ≤ S_max)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ S_max)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureAuxExpr M e).size ≤ S_max * e.size := by
  induction e with
  | var _ | unit | bool _ | none | nil =>
    simp only [compilePureAuxExpr, Expr.size]; omega
  | nat _ =>
    simp only [compilePureAuxExpr, Expr.size]; nlinarith
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | tget _ _ ih1 ih2 | letE _ _ ih1 ih2 =>
    simp only [compilePureAuxExpr, Expr.size]; nlinarith
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [compilePureAuxExpr, Expr.size]; nlinarith
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb
  | foldrB _ _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp only [compilePureAuxExpr, Expr.size]; nlinarith
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureAuxExpr, Expr.size, callPureMacroAux_size]; nlinarith
  | findB _ _ _ ihl ihp | anyB _ _ _ ihl ihp | mapB _ _ _ ihl ihp =>
    simp only [compilePureAuxExpr, Expr.size]; nlinarith

theorem compilePureAuxComp_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (S_max : ℕ) (hS : 1 ≤ S_max)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ S_max)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureAuxComp M c).size ≤ S_max * c.size := by
  induction c with
  | ret e =>
    have he := compilePureAuxExpr_size_le M S_max hS hOp e
    simp only [compilePureAuxComp, Comp.size]; nlinarith
  | bind _ _ ihc ihk =>
    simp only [compilePureAuxComp, Comp.size]; nlinarith
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := compilePureAuxExpr_size_le M S_max hS hOp b
    simp only [compilePureAuxComp, Comp.size]; nlinarith
  | sample s e =>
    have he := compilePureAuxExpr_size_le M S_max hS hOp e
    have hs := hSamp s
    simp only [compilePureAuxComp, Comp.size, callMacroAux_size]; nlinarith
  | query g e =>
    have he := compilePureAuxExpr_size_le M S_max hS hOp e
    have hq := hQuery g
    simp only [compilePureAuxComp, Comp.size, callMacroAux_size]; nlinarith
  | iter _ e _ ihb =>
    have he := compilePureAuxExpr_size_le M S_max hS hOp e
    simp only [compilePureAuxComp, Comp.size]; nlinarith
  | findM _ l _ ihp | anyM _ l _ ihp | mapM _ l _ ihp =>
    have hl := compilePureAuxExpr_size_le M S_max hS hOp l
    simp only [compilePureAuxComp, Comp.size]; nlinarith
  | consumeFirstM _ l _ mk ihp =>
    have hl := compilePureAuxExpr_size_le M S_max hS hOp l
    have hmk := compilePureAuxExpr_size_le M S_max hS hOp mk
    simp only [compilePureAuxComp, Comp.size]; nlinarith
  | foldM _ l z _ ihf =>
    have hl := compilePureAuxExpr_size_le M S_max hS hOp l
    have hz := compilePureAuxExpr_size_le M S_max hS hOp z
    simp only [compilePureAuxComp, Comp.size]; nlinarith

theorem compilePureAuxRed_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (S_max : ℕ) (hS : 1 ≤ S_max)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ S_max) :
    (compilePureAuxRed M A R).size ≤
      S_max * R.size + A.splitIn.size + A.adaptAIn.size +
      A.adaptQ.size + A.adaptR.size + A.adaptAOut.size + A.adaptOut.size + 74 := by
  have hi := compilePureAuxComp_size_le M S_max hS hOp hSamp hQuery R.init
  have hh := compilePureAuxComp_size_le M S_max hS hOp hSamp hQuery R.handle
  have hf := compilePureAuxComp_size_le M S_max hS hOp hSamp hQuery R.finish
  have hinit :
      (compilePureAuxRed M A R).init.size ≤
        S_max * R.init.size + A.splitIn.size + A.adaptAIn.size + 24 := by
    simp only [compilePureAuxRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hhandle :
      (compilePureAuxRed M A R).handle.size ≤
        S_max * R.handle.size + A.adaptQ.size + A.adaptR.size + 28 := by
    simp only [compilePureAuxRed, Comp.size, Comp.renameM_size, Expr.renameM_size, callAdaptR_size,
      Expr.size]
    omega
  have hfinish :
      (compilePureAuxRed M A R).finish.size ≤
        S_max * R.finish.size + A.adaptAOut.size + A.adaptOut.size + 22 := by
    simp only [compilePureAuxRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  dsimp only [CostedReduction.size]
  nlinarith

theorem compilePureAuxExpr_size_le_nodes {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) (S_max : ℕ)
    (hOp : ∀ o, (M.opMacro o).size ≤ S_max)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureAuxExpr M e).size ≤ e.size + S_max * e.nodes := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp only [compilePureAuxExpr, Expr.size, Expr.nodes]; omega
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | tget _ _ ih1 ih2 | letE _ _ ih1 ih2
  | findB _ _ _ ih1 ih2 | anyB _ _ _ ih1 ih2 | mapB _ _ _ ih1 ih2 =>
    simp only [compilePureAuxExpr, Expr.size, Expr.nodes]; nlinarith
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [compilePureAuxExpr, Expr.size, Expr.nodes]; nlinarith
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb
  | foldrB _ _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp only [compilePureAuxExpr, Expr.size, Expr.nodes]; nlinarith
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureAuxExpr, Expr.size, Expr.nodes, callPureMacroAux_size]; nlinarith

theorem compilePureAuxComp_size_le_nodes {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) (S_max : ℕ)
    (hOp : ∀ o, (M.opMacro o).size ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 1 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 1 ≤ S_max)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureAuxComp M c).size ≤ c.size + S_max * c.nodes := by
  induction c with
  | ret e =>
    have he := compilePureAuxExpr_size_le_nodes M S_max hOp e
    simp only [compilePureAuxComp, Comp.size, Comp.nodes]; nlinarith
  | bind _ _ ihc ihk =>
    simp only [compilePureAuxComp, Comp.size, Comp.nodes]; nlinarith
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := compilePureAuxExpr_size_le_nodes M S_max hOp b
    simp only [compilePureAuxComp, Comp.size, Comp.nodes]; nlinarith
  | sample s e =>
    have he := compilePureAuxExpr_size_le_nodes M S_max hOp e
    have hs := hSamp s
    simp only [compilePureAuxComp, Comp.size, Comp.nodes, callMacroAux_size]; nlinarith
  | query g e =>
    have he := compilePureAuxExpr_size_le_nodes M S_max hOp e
    have hq := hQuery g
    simp only [compilePureAuxComp, Comp.size, Comp.nodes, callMacroAux_size]; nlinarith
  | iter _ e _ ihb | findM _ e _ ihb | anyM _ e _ ihb | mapM _ e _ ihb =>
    have he := compilePureAuxExpr_size_le_nodes M S_max hOp e
    simp only [compilePureAuxComp, Comp.size, Comp.nodes]; nlinarith
  | consumeFirstM _ l _ mk ihp =>
    have hl := compilePureAuxExpr_size_le_nodes M S_max hOp l
    have hmk := compilePureAuxExpr_size_le_nodes M S_max hOp mk
    simp only [compilePureAuxComp, Comp.size, Comp.nodes]; nlinarith
  | foldM _ l z _ ihf =>
    have hl := compilePureAuxExpr_size_le_nodes M S_max hOp l
    have hz := compilePureAuxExpr_size_le_nodes M S_max hOp z
    simp only [compilePureAuxComp, Comp.size, Comp.nodes]; nlinarith

theorem compilePureAuxRed_size_le_nodes {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (S_max : ℕ)
    (hOp : ∀ o, (M.opMacro o).size ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 1 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 1 ≤ S_max) :
    (compilePureAuxRed M A R).size ≤
      R.size + S_max * R.nodes + A.splitIn.size + A.adaptAIn.size +
      A.adaptQ.size + A.adaptR.size + A.adaptAOut.size + A.adaptOut.size + 74 := by
  have hi := compilePureAuxComp_size_le_nodes M S_max hOp hSamp hQuery R.init
  have hh := compilePureAuxComp_size_le_nodes M S_max hOp hSamp hQuery R.handle
  have hf := compilePureAuxComp_size_le_nodes M S_max hOp hSamp hQuery R.finish
  have hinit :
      (compilePureAuxRed M A R).init.size ≤
        R.init.size + S_max * R.init.nodes + A.splitIn.size + A.adaptAIn.size + 24 := by
    simp only [compilePureAuxRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hhandle :
      (compilePureAuxRed M A R).handle.size ≤
        R.handle.size + S_max * R.handle.nodes + A.adaptQ.size + A.adaptR.size + 28 := by
    simp only [compilePureAuxRed, Comp.size, Comp.renameM_size, Expr.renameM_size, callAdaptR_size,
      Expr.size]
    omega
  have hfinish :
      (compilePureAuxRed M A R).finish.size ≤
        R.finish.size + S_max * R.finish.nodes + A.adaptAOut.size + A.adaptOut.size + 22 := by
    simp only [compilePureAuxRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  dsimp only [CostedReduction.size, CostedReduction.nodes]
  nlinarith

def exprExcessOf {S : Sig} {O : Ops S} (opEx : O.Op → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .nat _ | _, _, .none | _, _, .nil => 0
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b | _, _, .and a b
  | _, _, .pair a b | _, _, .cons a b | _, _, .take a b | _, _, .appendL _ a b
  | _, _, .letE a b | _, _, .tget a b => exprExcessOf opEx a + exprExcessOf opEx b
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a | _, _, .not a | _, _, .fst a
  | _, _, .snd a | _, _, .inl a | _, _, .inr a | _, _, .some a | _, _, .len a
  | _, _, .tconst a => exprExcessOf opEx a
  | _, _, .ite c a b | _, _, .caseOpt c a b | _, _, .caseSum c a b =>
    exprExcessOf opEx c + max (exprExcessOf opEx a) (exprExcessOf opEx b)
  | _, _, .op o a => exprExcessOf opEx a + opEx o
  | _, _, .findB K l p | _, _, .anyB K l p | _, _, .mapB K l p =>
    exprExcessOf opEx l + K * exprExcessOf opEx p
  | _, _, .foldrB K l z f =>
    exprExcessOf opEx l + exprExcessOf opEx z + K * exprExcessOf opEx f
  | _, _, .tset m i a => exprExcessOf opEx m + exprExcessOf opEx i + exprExcessOf opEx a

def compExcessOf {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opEx : O.Op → ℕ) (sEx : I.smp.Samp → ℕ) (qEx : I.Tag → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => exprExcessOf opEx e
  | _, _, .bind c k => compExcessOf opEx sEx qEx c + compExcessOf opEx sEx qEx k
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    exprExcessOf opEx b + max (compExcessOf opEx sEx qEx c) (compExcessOf opEx sEx qEx d)
  | _, _, .sample s e => exprExcessOf opEx e + sEx s
  | _, _, .query g e => exprExcessOf opEx e + qEx g
  | _, _, .iter n e body => exprExcessOf opEx e + n * compExcessOf opEx sEx qEx body
  | _, _, .findM K l p | _, _, .anyM K l p | _, _, .mapM K l p =>
    exprExcessOf opEx l + K * compExcessOf opEx sEx qEx p
  | _, _, .consumeFirstM K l p mk =>
    exprExcessOf opEx l + K * (compExcessOf opEx sEx qEx p + exprExcessOf opEx mk)
  | _, _, .foldM K l z f =>
    exprExcessOf opEx l + exprExcessOf opEx z + K * compExcessOf opEx sEx qEx f

theorem exprCostW_le_cost_add_excess {S : Sig} {O : Ops S}
    (opEx opC : O.Op → ℕ) (hOp : ∀ o, opC o ≤ O.cost o + opEx o)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    exprCostW opC e ≤ e.cost + exprExcessOf opEx e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil => simp [Expr.cost, exprExcessOf, exprCostW]
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | letE _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    simp only [Expr.cost, exprExcessOf, exprCostW]; omega
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [Expr.cost, exprExcessOf, exprCostW]; omega
  | ite c a b ihc iha ihb | caseOpt c a b ihc iha ihb | caseSum c a b ihc iha ihb =>
    have hmax : max (exprCostW opC a) (exprCostW opC b) ≤
        max a.cost b.cost + max (exprExcessOf opEx a) (exprExcessOf opEx b) :=
      le_trans (max_le_max iha ihb) (by omega)
    simp only [Expr.cost, exprExcessOf, exprCostW]; omega
  | op o _ iha =>
    have ho := hOp o
    simp only [Expr.cost, exprExcessOf, exprCostW]; omega
  | findB K l p ihl ihp | anyB K l p ihl ihp | mapB K l p ihl ihp =>
    have hm : K * (exprCostW opC p + 1) ≤ K * (p.cost + 1 + exprExcessOf opEx p) :=
      Nat.mul_le_mul_left K (by omega)
    simp only [Expr.cost, exprExcessOf, exprCostW]; nlinarith
  | foldrB K l z f ihl ihz ihf =>
    have hm : K * (exprCostW opC f + 1) ≤ K * (f.cost + 1 + exprExcessOf opEx f) :=
      Nat.mul_le_mul_left K (by omega)
    simp only [Expr.cost, exprExcessOf, exprCostW]; nlinarith
  | tset _ _ _ ih1 ih2 ih3 =>
    simp only [Expr.cost, exprExcessOf, exprCostW]; omega

theorem compCostW_le_cost_add_excess {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opEx opC : O.Op → ℕ) (sEx sC : I.smp.Samp → ℕ) (qEx qC : I.Tag → ℕ)
    (hOp : ∀ o, opC o ≤ O.cost o + opEx o)
    (hS : ∀ s, sC s ≤ I.smp.sCost s + sEx s)
    (hQ : ∀ g, qC g ≤ I.qCost g + qEx g)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compCostW opC sC qC c ≤ c.cost + compExcessOf opEx sEx qEx c := by
  induction c with
  | ret e =>
    have he := exprCostW_le_cost_add_excess opEx opC hOp e
    simp only [Comp.cost, compExcessOf, compCostW]; omega
  | bind _ _ ihc ihk =>
    simp only [Comp.cost, compExcessOf, compCostW]; omega
  | ite b c d ihc ihd | caseOpt b c d ihc ihd | caseSum b c d ihc ihd =>
    have hb := exprCostW_le_cost_add_excess opEx opC hOp b
    have hmax : max (compCostW opC sC qC c) (compCostW opC sC qC d) ≤
        max c.cost d.cost + max (compExcessOf opEx sEx qEx c) (compExcessOf opEx sEx qEx d) :=
      le_trans (max_le_max ihc ihd) (by omega)
    simp only [Comp.cost, compExcessOf, compCostW]; omega
  | sample s e =>
    have he := exprCostW_le_cost_add_excess opEx opC hOp e
    have hs := hS s
    simp only [Comp.cost, compExcessOf, compCostW]; omega
  | query g e =>
    have he := exprCostW_le_cost_add_excess opEx opC hOp e
    have hq := hQ g
    simp only [Comp.cost, compExcessOf, compCostW]; omega
  | iter n e body ihb =>
    have he := exprCostW_le_cost_add_excess opEx opC hOp e
    have hm : n * (compCostW opC sC qC body + 1) ≤
        n * (body.cost + 1 + compExcessOf opEx sEx qEx body) :=
      Nat.mul_le_mul_left n (by omega)
    simp only [Comp.cost, compExcessOf, compCostW]; nlinarith
  | findM K l p ihp | anyM K l p ihp | mapM K l p ihp =>
    have hl := exprCostW_le_cost_add_excess opEx opC hOp l
    have hm : K * (compCostW opC sC qC p + 1) ≤
        K * (p.cost + 1 + compExcessOf opEx sEx qEx p) :=
      Nat.mul_le_mul_left K (by omega)
    simp only [Comp.cost, compExcessOf, compCostW]; nlinarith
  | consumeFirstM K l p mk ihp =>
    have hl := exprCostW_le_cost_add_excess opEx opC hOp l
    have hmk := exprCostW_le_cost_add_excess opEx opC hOp mk
    have hm : K * (compCostW opC sC qC p + exprCostW opC mk + 1) ≤
        K * (p.cost + mk.cost + 1 + (compExcessOf opEx sEx qEx p + exprExcessOf opEx mk)) :=
      Nat.mul_le_mul_left K (by omega)
    simp only [Comp.cost, compExcessOf, compCostW]; nlinarith
  | foldM K l z f ihf =>
    have hl := exprCostW_le_cost_add_excess opEx opC hOp l
    have hz := exprCostW_le_cost_add_excess opEx opC hOp z
    have hm : K * (compCostW opC sC qC f + 1) ≤
        K * (f.cost + 1 + compExcessOf opEx sEx qEx f) :=
      Nat.mul_le_mul_left K (by omega)
    simp only [Comp.cost, compExcessOf, compCostW]; nlinarith

end WeightedCost

end Computational.Proofs.ReductionDsl.PureAuxMacroLift
