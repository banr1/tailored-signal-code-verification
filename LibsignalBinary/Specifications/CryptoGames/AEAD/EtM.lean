/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# OT-CCA security of Encrypt-then-MAC

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves one-time chosen-ciphertext (OT-CCA) security of `AEADScheme.etm` (`EtMDefs.lean`) from
one-time IND-CPA security of the cipher (`redCipher`) and PRF security of the MAC (`redMACChall`,
`redMACForge`), plus a tag-guessing term `qd / Fintype.card T` over at most `qd` decryption
queries.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames

namespace AEADScheme

section EtM

variable {KE KM AD M C T : Type}

/-! ### Proof of `etm_otcca` -/

namespace EtMProof

variable {KE KM AD M C T : Type}

/-- Composition of `simulateQ`. -/
theorem simulateQ_simulateQ {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl' : QueryImpl spec' m)
    (impl : QueryImpl spec (OracleComp spec')) {α : Type} (oa : OracleComp spec α) :
    simulateQ impl' (simulateQ impl oa) = simulateQ (fun t => simulateQ impl' (impl t)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, ih]

/-- A stateful simulation is preserved by a state map `F` under an invariant `I`. -/
theorem run_map {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (F : σ₂ → σ₁) (I : σ₂ → Prop)
    (hstep : ∀ t s, I s → (impl₁ t).run (F s) = Prod.map id F <$> (impl₂ t).run s ∧
      ∀ z ∈ support ((impl₂ t).run s), I z.2)
    {α : Type} (oa : OracleComp spec α) :
    ∀ s, I s → (simulateQ impl₁ oa).run (F s) = Prod.map id F <$> (simulateQ impl₂ oa).run s := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _; simp
  | query_bind t k ih =>
    intro s hI
    obtain ⟨h1, h2⟩ := hstep t s hI
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [h1, bind_map_left, map_bind]
    exact bind_congr_of_forall_mem_support _ fun z hz => ih z.1 z.2 (h2 z hz)

/-- Uniform product sampling splits into sequential uniform sampling. -/
theorem uniform_prod (α β : Type) [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do let a ← $ᵗ α; let b ← $ᵗ β; pure (a, b)) := by
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp_apply]
  rfl

/-- Adversary coins in any `StateT σ ProbComp`. -/
abbrev coin {σ : Type} (n : ℕ) : StateT σ ProbComp (Fin (n + 1)) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) n

theorem mem_support_coin {σ : Type} {n : ℕ} {s : σ} {z : Fin (n + 1) × σ}
    (hz : z ∈ support ((coin n : StateT σ ProbComp _).run s)) : z.2 = s := by
  simp only [coin, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨u, _, rfl⟩ := hz
  rfl

/-- Combined oracle specification for OT-CCA adversaries. -/
abbrev QSpec (AD M C T : Type) := unifSpec + otccaSpec AD M (C × T)

/-- Key-free one-time-encrypt / reject-decrypt oracle implementation, parameterized by `encStep`. -/
def implOnce (encStep : AD → M → ProbComp (C × T)) :
    QueryImpl (QSpec AD M C T) (StateT Bool ProbComp)
  | .inl n => coin n
  | .inr (.inl ⟨a, m⟩) => StateT.mk fun qd =>
      if qd then pure (none, true)
      else (fun e => (some e, true)) <$> encStep a m
  | .inr (.inr _) => StateT.mk fun qd => pure (none, qd)

/-- Run `B` against `implOnce encStep` starting from `queried = false`. -/
def runOnce (encStep : AD → M → ProbComp (C × T))
    (B : OTCCAAdversary AD M (C × T)) : ProbComp Bool :=
  (simulateQ (implOnce encStep) B).run' false

variable [DecidableEq AD] [DecidableEq C] [DecidableEq T]

/-- The OT-CCA game oracle implementation for `etm cipher mac`. -/
def implO [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T) :
    QueryImpl (QSpec AD M C T)
      (StateT (OTCCAState (KE × KM) AD (C × T)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (OTCCAState (KE × KM) AD (C × T)) ProbComp)
    + ((etm cipher mac).otccaEncrypt + (etm cipher mac).otccaDecrypt)

/-- The OT-CCA game for `etm cipher mac` with a fixed hidden bit `b`. -/
def otccaBranch [SampleableType KE] [SampleableType KM] [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (b : Bool) (B : OTCCAAdversary AD M (C × T)) : ProbComp Bool := do
  let key ← $ᵗ (KE × KM)
  (simulateQ (implO cipher mac) B).run' { key, b }

theorem otccaAdvantage_eq_boolDist [SampleableType KE] [SampleableType KM]
    [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (B : OTCCAAdversary AD M (C × T)) :
    (etm cipher mac).otccaAdvantage B =
      𝒟[otccaBranch cipher mac true B].boolDist 𝒟[otccaBranch cipher mac false B] := by
  have hcoin : ∀ x : Bool, 𝒟[($ᵗ Bool : ProbComp Bool)] {x} = 1 / 2 := fun _ => by simp
  rw [← evalDist_boolBias_bind_coin ($ᵗ Bool) _ _ (hcoin true) (hcoin false)]
  unfold otccaAdvantage otccaGame
  congr 2
  refine bind_congr fun b => ?_
  cases b <;> simp [otccaBranch, implO]

/-- In the ideal OT-CCA branch (`b = true`), the run equals `implOnce (fun _ _ => $ᵗ (C × T))`. -/
theorem otcca_ideal_eq_implOnce [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    {α : Type} (oa : OracleComp (QSpec AD M C T) α)
    (s : OTCCAState (KE × KM) AD (C × T)) (hb : s.b = true) :
    (simulateQ (implOnce (fun _ _ => $ᵗ (C × T))) oa).run s.chal.isSome =
      Prod.map id (fun z => z.chal.isSome) <$> (simulateQ (implO cipher mac) oa).run s := by
  refine run_map (implOnce (fun _ _ => $ᵗ (C × T))) (implO cipher mac)
    (fun z => z.chal.isSome) (fun z => z.b = true) (fun t z hz => ?_) oa s hb
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · refine ⟨by simp [implOnce, implO, coin], fun w hw => ?_⟩
    have hw' : w ∈ support ((coin n : StateT _ ProbComp _).run z) := by
      simpa [implO, coin] using hw
    rw [mem_support_coin hw']; exact hz
  · by_cases hc : z.chal.isSome = true
    · refine ⟨by simp [implOnce, implO, otccaEncrypt, hc], fun w hw => ?_⟩
      simp [implO, otccaEncrypt, hc] at hw
      subst hw; exact hz
    · refine ⟨by simp [implOnce, implO, otccaEncrypt, hc, hz, Functor.map_map],
        fun w hw => ?_⟩
      simp [implO, otccaEncrypt, hc, hz] at hw
      rcases hw with ⟨_, _, rfl⟩; rfl
  · refine ⟨by simp [implOnce, implO, otccaDecrypt, hz], fun w hw => ?_⟩
    simp [implO, otccaDecrypt, hz] at hw
    subst hw; exact hz

theorem evalDist_otccaBranch_true [SampleableType KE] [SampleableType KM]
    [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (B : OTCCAAdversary AD M (C × T)) :
    𝒟[otccaBranch cipher mac true B] = 𝒟[runOnce (fun _ _ => $ᵗ (C × T)) B] := by
  unfold otccaBranch runOnce
  have h : ∀ key : KE × KM,
      (simulateQ (implO cipher mac) B).run' { key, b := true } =
        (simulateQ (implOnce (fun _ _ => $ᵗ (C × T))) B).run' false := by
    intro key
    have h1 := congrArg (Prod.fst <$> ·)
      (otcca_ideal_eq_implOnce cipher mac B { key, b := true } rfl)
    simpa [StateT.run'_eq, Functor.map_map] using h1.symm
  simp only [h, OracleComp.evalDist_bind_const]

/-- Oracle implementation of `cipher.branch`. -/
def cImpl [SampleableType C] (cipher : CipherScheme KE M C) :
    QueryImpl (unifSpec + CipherScheme.indcpaSpec M C)
      (StateT (CipherScheme.INDCPAState KE) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (CipherScheme.INDCPAState KE) ProbComp) + CipherScheme.indcpaEncrypt cipher

omit [DecidableEq C] in
theorem cipher_branch_eq [SampleableType KE] [SampleableType C]
    (cipher : CipherScheme KE M C) (b : Bool) (A : CipherScheme.INDCPAAdversary M C) :
    cipher.branch b A = (do
      let key ← $ᵗ KE
      (simulateQ (cImpl cipher) A).run' { key, b }) := rfl

omit [DecidableEq C] in
@[simp] theorem simulateQ_cImpl_encryptQuery [SampleableType C]
    (cipher : CipherScheme KE M C) (m : M) :
    simulateQ (cImpl cipher) (CipherScheme.encryptQuery m) =
      CipherScheme.indcpaEncrypt cipher m := by
  simp [CipherScheme.encryptQuery, cImpl]

omit [DecidableEq C] in
@[simp] theorem simulateQ_cImpl_liftM [SampleableType C] (cipher : CipherScheme KE M C)
    {α : Type} (oa : ProbComp α) :
    simulateQ (cImpl cipher)
      (liftM oa : OracleComp (unifSpec + CipherScheme.indcpaSpec M C) α) =
      liftM oa := by
  simp [cImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

omit [DecidableEq AD] [DecidableEq C] [DecidableEq T] in
/-- `redCipher` in `cipher.branch true` equals `implOnce (fun _ _ => $ᵗ (C × T))`. -/
theorem cipher_ideal_eq_implOnce [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C)
    {α : Type} (oa : OracleComp (QSpec AD M C T) α)
    (s : CipherScheme.INDCPAState KE) (hb : s.b = true) :
    (simulateQ (implOnce (fun _ _ => $ᵗ (C × T))) oa).run s.queried =
      Prod.map id (fun z => z.queried) <$>
        (simulateQ (cImpl cipher) (simulateQ cipherRedImpl oa)).run s := by
  rw [simulateQ_simulateQ]
  refine run_map (implOnce (fun _ _ => $ᵗ (C × T)))
    (fun t => simulateQ (cImpl cipher) (cipherRedImpl t))
    (fun z => z.queried) (fun z => z.b = true) (fun t z hz => ?_) oa s hb
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · refine ⟨by simp [implOnce, cipherRedImpl, cImpl, coin], fun w hw => ?_⟩
    have hw' : w ∈ support ((coin n : StateT _ ProbComp _).run z) := by
      simpa [cipherRedImpl, cImpl, coin] using hw
    rw [mem_support_coin hw']; exact hz
  · by_cases hq : z.queried = true
    · refine ⟨by simp [implOnce, cipherRedImpl, CipherScheme.indcpaEncrypt, hq], fun w hw => ?_⟩
      simp [cipherRedImpl, CipherScheme.indcpaEncrypt, hq] at hw
      subst hw; exact hz
    · refine ⟨?_, fun w hw => ?_⟩
      · simp [implOnce, cipherRedImpl, CipherScheme.indcpaEncrypt, hq, hz, uniform_prod C T,
          map_eq_bind_pure_comp, bind_assoc]
      · simp [cipherRedImpl, CipherScheme.indcpaEncrypt, hq, hz] at hw
        rcases hw with ⟨_, _, rfl⟩; rfl
  · refine ⟨by simp [implOnce, cipherRedImpl], fun w hw => ?_⟩
    simp [cipherRedImpl] at hw
    subst hw; exact hz

omit [DecidableEq AD] [DecidableEq C] [DecidableEq T] in
theorem evalDist_cipher_branch_true [SampleableType KE] [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (B : OTCCAAdversary AD M (C × T)) :
    𝒟[cipher.branch true (redCipher B)] = 𝒟[runOnce (fun _ _ => $ᵗ (C × T)) B] := by
  rw [cipher_branch_eq]
  unfold redCipher runOnce
  have h : ∀ key : KE,
      (simulateQ (cImpl cipher) (simulateQ cipherRedImpl B)).run' { key, b := true } =
        (simulateQ (implOnce (fun _ _ => $ᵗ (C × T))) B).run' false := by
    intro key
    have h1 := congrArg (Prod.fst <$> ·)
      (cipher_ideal_eq_implOnce cipher B { key, b := true } rfl)
    simpa [StateT.run'_eq, Functor.map_map] using h1.symm
  simp only [h, OracleComp.evalDist_bind_const]

omit [DecidableEq AD] [DecidableEq C] [DecidableEq T] in
/-- `redCipher` in `cipher.branch false` with key `ke` equals
`implOnce (fun _ m => (cipher.enc ke m, ·) <$> ($ᵗ T))`. -/
theorem cipher_real_eq_implOnce [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (ke : KE)
    {α : Type} (oa : OracleComp (QSpec AD M C T) α)
    (s : CipherScheme.INDCPAState KE) (hb : s.b = false ∧ s.key = ke) :
    (simulateQ (implOnce (fun _ m => (cipher.enc ke m, ·) <$> ($ᵗ T))) oa).run s.queried =
      Prod.map id (fun z => z.queried) <$>
        (simulateQ (cImpl cipher) (simulateQ cipherRedImpl oa)).run s := by
  rw [simulateQ_simulateQ]
  refine run_map (implOnce (fun _ m => (cipher.enc ke m, ·) <$> ($ᵗ T)))
    (fun t => simulateQ (cImpl cipher) (cipherRedImpl t))
    (fun z => z.queried) (fun z => z.b = false ∧ z.key = ke) (fun t z ⟨hzb, hzk⟩ => ?_) oa s hb
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · refine ⟨by simp [implOnce, cipherRedImpl, cImpl, coin], fun w hw => ?_⟩
    have hw' : w ∈ support ((coin n : StateT _ ProbComp _).run z) := by
      simpa [cipherRedImpl, cImpl, coin] using hw
    rw [mem_support_coin hw']; exact ⟨hzb, hzk⟩
  · by_cases hq : z.queried = true
    · refine ⟨by simp [implOnce, cipherRedImpl, CipherScheme.indcpaEncrypt, hq], fun w hw => ?_⟩
      simp [cipherRedImpl, CipherScheme.indcpaEncrypt, hq] at hw
      subst hw; exact ⟨hzb, hzk⟩
    · refine ⟨?_, fun w hw => ?_⟩
      · simp [implOnce, cipherRedImpl, CipherScheme.indcpaEncrypt, hq, hzb, hzk,
          map_eq_bind_pure_comp, bind_assoc]
      · simp [cipherRedImpl, CipherScheme.indcpaEncrypt, hq, hzb] at hw
        rcases hw with ⟨_, rfl⟩; exact ⟨rfl, hzk⟩
  · refine ⟨by simp [implOnce, cipherRedImpl], fun w hw => ?_⟩
    simp [cipherRedImpl] at hw
    subst hw; exact ⟨hzb, hzk⟩

omit [DecidableEq AD] [DecidableEq C] [DecidableEq T] in
theorem cipher_branch_false_eq [SampleableType KE] [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (B : OTCCAAdversary AD M (C × T)) :
    cipher.branch false (redCipher B) =
      (do let ke ← $ᵗ KE; runOnce (fun _ m => (cipher.enc ke m, ·) <$> ($ᵗ T)) B) := by
  rw [cipher_branch_eq]
  unfold redCipher runOnce
  refine bind_congr fun ke => ?_
  have h1 := congrArg (Prod.fst <$> ·)
    (cipher_real_eq_implOnce cipher ke B { key := ke, b := false } ⟨rfl, rfl⟩)
  simpa [StateT.run'_eq, Functor.map_map] using h1.symm

/-- Oracle implementation of `mac.branch`. -/
def mImpl [SampleableType T] (mac : MACScheme KM (AD × C) T) :
    QueryImpl (unifSpec + MACScheme.prfSpec (AD × C) T)
      (StateT (MACScheme.PRFState KM (AD × C) T) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (MACScheme.PRFState KM (AD × C) T) ProbComp) + MACScheme.prfEval mac

omit [DecidableEq T] in
theorem mac_branch_eq [SampleableType KM] [SampleableType T]
    (mac : MACScheme KM (AD × C) T) (b : Bool) (A : MACScheme.PRFAdversary (AD × C) T) :
    mac.branch b A = (do
      let key ← $ᵗ KM
      (simulateQ (mImpl mac) A).run' { key, b }) := rfl

omit [DecidableEq T] in
@[simp] theorem simulateQ_mImpl_liftM_run [SampleableType T] (mac : MACScheme KM (AD × C) T)
    {α : Type} (oa : ProbComp α) (pst : MACScheme.PRFState KM (AD × C) T) :
    (simulateQ (mImpl mac)
      (liftM oa : OracleComp (unifSpec + MACScheme.prfSpec (AD × C) T) α)).run pst =
      oa >>= fun a => pure (a, pst) := by
  simp [mImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

omit [DecidableEq T] in
@[simp] theorem prfEval_run_false [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (x : AD × C) (pst : MACScheme.PRFState KM (AD × C) T) (hb : pst.b = false) :
    (MACScheme.prfEval mac x).run pst = pure (mac.tag pst.key x, pst) := by
  simp [MACScheme.prfEval, hb]

omit [DecidableEq T] in
@[simp] theorem prfEval_run_true_nil [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (x : AD × C) (pst : MACScheme.PRFState KM (AD × C) T)
    (hb : pst.b = true) (ht : pst.table = []) :
    (MACScheme.prfEval mac x).run pst =
      ($ᵗ T) >>= fun t => pure (t, { pst with table := [(x, t)] }) := by
  simp [MACScheme.prfEval, hb, ht]

omit [DecidableEq T] in
@[simp] theorem prfEval_run_true_hit [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (x : AD × C) (τStar : T) (pst : MACScheme.PRFState KM (AD × C) T)
    (hb : pst.b = true) (ht : pst.table = [(x, τStar)]) :
    (MACScheme.prfEval mac x).run pst = pure (τStar, pst) := by
  simp [MACScheme.prfEval, hb, ht]

omit [DecidableEq T] in
theorem prfEval_run_true_miss [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (x y : AD × C) (τStar : T) (pst : MACScheme.PRFState KM (AD × C) T)
    (hb : pst.b = true) (ht : pst.table = [(y, τStar)]) (hne : x ≠ y) :
    (MACScheme.prfEval mac x).run pst =
      ($ᵗ T) >>= fun t => pure (t, { pst with table := (x, t) :: [(y, τStar)] }) := by
  have hne' : (@BEq.beq (AD × C) (@instBEqOfDecidableEq (AD × C) inferInstance) x y) = false :=
    decide_eq_false hne
  simp [MACScheme.prfEval, hb, ht, List.lookup, hne']

/-- Run `challRedImpl cipher ke` inside `mImpl mac`. -/
def runChall [SampleableType T] (mac : MACScheme KM (AD × C) T) (cipher : CipherScheme KE M C)
    (ke : KE) {α : Type} (oa : OracleComp (QSpec AD M C T) α)
    (qd : Bool) (pst : MACScheme.PRFState KM (AD × C) T) :
    ProbComp ((α × Bool) × MACScheme.PRFState KM (AD × C) T) :=
  (simulateQ (mImpl mac) ((simulateQ (challRedImpl cipher ke) oa).run qd)).run pst

omit [DecidableEq T] in
@[simp] theorem runChall_pure [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE)
    {α : Type} (a : α) (qd : Bool) (pst : MACScheme.PRFState KM (AD × C) T) :
    runChall mac cipher ke (pure a) qd pst = pure ((a, qd), pst) := by
  simp [runChall]

omit [DecidableEq T] in
theorem runChall_query_bind [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE)
    {α : Type} (q : (QSpec AD M C T).Domain)
    (k : (QSpec AD M C T).Range q → OracleComp (QSpec AD M C T) α)
    (qd : Bool) (pst : MACScheme.PRFState KM (AD × C) T) :
    runChall mac cipher ke (liftM (OracleSpec.query q) >>= k) qd pst =
      (simulateQ (mImpl mac) ((challRedImpl cipher ke q).run qd)).run pst >>= fun r =>
        runChall mac cipher ke (k r.1.1) r.1.2 r.2 := by
  simp [runChall, simulateQ_bind, simulateQ_query]

omit [DecidableEq T] in
@[simp] theorem challStep_inl [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (n : ℕ)
    (qd : Bool) (pst : MACScheme.PRFState KM (AD × C) T) :
    (simulateQ (mImpl mac)
      ((challRedImpl (AD := AD) (T := T) cipher ke (.inl n)).run qd)).run pst =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure ((u, qd), pst) := by
  simp [challRedImpl, mImpl]

omit [DecidableEq T] in
@[simp] theorem challStep_enc_true [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (a : AD) (m : M)
    (pst : MACScheme.PRFState KM (AD × C) T) :
    (simulateQ (mImpl mac)
      ((challRedImpl (AD := AD) (T := T) cipher ke (.inr (.inl (a, m)))).run true)).run pst =
      pure ((none, true), pst) := by
  simp [challRedImpl]

omit [DecidableEq T] in
@[simp] theorem challStep_enc_false [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (a : AD) (m : M)
    (pst : MACScheme.PRFState KM (AD × C) T) :
    (simulateQ (mImpl mac)
      ((challRedImpl (AD := AD) (T := T) cipher ke (.inr (.inl (a, m)))).run false)).run pst =
      (MACScheme.prfEval mac (a, cipher.enc ke m)).run pst >>= fun r =>
        pure ((some (cipher.enc ke m, r.1), true), r.2) := by
  simp [challRedImpl, MACScheme.evalQuery, mImpl]

omit [DecidableEq T] in
@[simp] theorem challStep_dec [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (a : AD) (e : C × T)
    (qd : Bool) (pst : MACScheme.PRFState KM (AD × C) T) :
    (simulateQ (mImpl mac)
      ((challRedImpl (AD := AD) (T := T) cipher ke (.inr (.inr (a, e)))).run qd)).run pst =
      pure ((none, qd), pst) := by
  simp [challRedImpl]

omit [DecidableEq AD] [DecidableEq C] [DecidableEq T] in
theorem implOnce_query_bind (encStep : AD → M → ProbComp (C × T))
    {α : Type} (q : (QSpec AD M C T).Domain)
    (k : (QSpec AD M C T).Range q → OracleComp (QSpec AD M C T) α) (qd : Bool) :
    (simulateQ (implOnce encStep) (liftM (OracleSpec.query q) >>= k)).run qd =
      (implOnce encStep q).run qd >>= fun r =>
        (simulateQ (implOnce encStep) (k r.1)).run r.2 := by
  simp [simulateQ_bind, simulateQ_query]

omit [DecidableEq T] in
/-- `runChall` in `pst.b = true` matches `implOnce (fun _ m => (cipher.enc ke m, ·) <$> ($ᵗ T))`. -/
theorem runChall_true_eq [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE)
    {α : Type} (oa : OracleComp (QSpec AD M C T) α) :
    ∀ (qd : Bool) (pst : MACScheme.PRFState KM (AD × C) T),
      pst.b = true → (qd = false → pst.table = []) →
      (fun r => r.1.1) <$> runChall mac cipher ke oa qd pst =
        Prod.fst <$> (simulateQ (implOnce (fun _ m => (cipher.enc ke m, ·) <$> ($ᵗ T))) oa).run qd := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro qd pst _ _; simp
  | query_bind t k ih =>
    intro qd pst hb htab
    rw [runChall_query_bind, implOnce_query_bind, map_bind, map_bind]
    rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [challStep_inl, implOnce, coin, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u qd pst hb htab
    · rcases qd with _ | _
      · have ht0 : pst.table = [] := htab rfl
        simp only [challStep_enc_false, prfEval_run_true_nil mac _ pst hb ht0,
          implOnce, Bool.false_eq_true, ↓reduceIte, StateT.run_mk,
          bind_map_left, bind_assoc, pure_bind]
        exact bind_congr fun τ =>
          ih (some (cipher.enc ke m, τ)) true
            { pst with table := [((a, cipher.enc ke m), τ)] } hb (by simp)
      · simp only [challStep_enc_true, implOnce, ↓reduceIte, StateT.run_mk, pure_bind]
        exact ih none true pst hb (by simp)
    · simp only [challStep_dec, implOnce, StateT.run_mk, pure_bind]
      exact ih none qd pst hb htab

omit [DecidableEq T] in
theorem evalDist_mac_branch_true_chall [SampleableType KE] [SampleableType KM]
    [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (B : OTCCAAdversary AD M (C × T)) :
    𝒟[mac.branch true (redMACChall cipher B)] = 𝒟[cipher.branch false (redCipher B)] := by
  rw [cipher_branch_false_eq, mac_branch_eq]
  unfold redMACChall runOnce
  have h : ∀ km : KM,
      (simulateQ (mImpl mac) (do
        let ke ← (liftM ($ᵗ KE : ProbComp KE) :
          OracleComp (unifSpec + MACScheme.prfSpec (AD × C) T) KE)
        (simulateQ (challRedImpl cipher ke) B).run' false)).run' { key := km, b := true } =
      (do let ke ← $ᵗ KE
          (simulateQ (implOnce (fun _ m => (cipher.enc ke m, ·) <$> ($ᵗ T))) B).run' false) := by
    intro km
    simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind,
      simulateQ_mImpl_liftM_run, bind_assoc, pure_bind]
    refine bind_congr fun ke => ?_
    simpa [runChall, StateT.run'_eq, Functor.map_map] using
      runChall_true_eq mac cipher ke B false { key := km, b := true } rfl (fun _ => rfl)
  simp only [h, OracleComp.evalDist_bind_const]

omit [DecidableEq T] in
/-- `runChall` in `pst.b = false` matches
`implOnce (fun a m => pure (cipher.enc ke m, mac.tag km (a, cipher.enc ke m)))`. -/
theorem runChall_false_eq [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (km : KM)
    {α : Type} (oa : OracleComp (QSpec AD M C T) α) :
    ∀ (qd : Bool) (pst : MACScheme.PRFState KM (AD × C) T),
      pst.b = false → pst.key = km →
      (fun r => r.1.1) <$> runChall mac cipher ke oa qd pst =
        Prod.fst <$> (simulateQ (implOnce (fun a m =>
          pure (cipher.enc ke m, mac.tag km (a, cipher.enc ke m)))) oa).run qd := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro qd pst _ _; simp
  | query_bind t k ih =>
    intro qd pst hb hk
    rw [runChall_query_bind, implOnce_query_bind, map_bind, map_bind]
    rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [challStep_inl, implOnce, coin, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u qd pst hb hk
    · rcases qd with _ | _
      · simp only [challStep_enc_false, prfEval_run_false mac _ pst hb, hk,
          implOnce, Bool.false_eq_true, ↓reduceIte, StateT.run_mk, map_pure, pure_bind]
        exact ih (some (cipher.enc ke m, mac.tag km (a, cipher.enc ke m))) true pst hb hk
      · simp only [challStep_enc_true, implOnce, ↓reduceIte, StateT.run_mk, pure_bind]
        exact ih none true pst hb hk
    · simp only [challStep_dec, implOnce, StateT.run_mk, pure_bind]
      exact ih none qd pst hb hk

omit [DecidableEq T] in
theorem mac_branch_false_chall_eq [SampleableType KE] [SampleableType KM] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (B : OTCCAAdversary AD M (C × T)) :
    mac.branch false (redMACChall cipher B) =
      (do let km ← $ᵗ KM; let ke ← $ᵗ KE
          runOnce (fun a m => pure (cipher.enc ke m, mac.tag km (a, cipher.enc ke m))) B) := by
  rw [mac_branch_eq]
  unfold redMACChall runOnce
  refine bind_congr fun km => ?_
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind,
    simulateQ_mImpl_liftM_run, bind_assoc, pure_bind]
  refine bind_congr fun ke => ?_
  simpa [runChall, StateT.run'_eq, Functor.map_map] using
    runChall_false_eq mac cipher ke km B false { key := km, b := false } rfl rfl

/-! #### Reject-decryption flag game `implNF` -/

abbrev St (KE KM AD C T : Type) := OTCCAState (KE × KM) AD (C × T)

/-- Real-world (`b = false`) encryption transition on `St`. -/
def encT (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (s : St KE KM AD C T) (a : AD) (m : M) : Option (C × T) × St KE KM AD C T :=
  if s.chal.isSome then (none, s)
  else
    let e := (etm cipher mac).enc s.key a m
    (some e, { s with chal := some (a, e) })

/-- Whether the real decryption oracle accepts the non-challenge query `(a, e)`. -/
def hit (mac : MACScheme KM (AD × C) T) (s : St KE KM AD C T) (a : AD) (e : C × T) : Bool :=
  s.chal != some (a, e) && mac.tag s.key.2 (a, e.1) == e.2

/-- `implNF`: the real world whose decryption oracle always answers `none` and raises the flag
when the real oracle would have accepted. -/
def implNF (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T) :
    QueryImpl (QSpec AD M C T)
      (StateT (St KE KM AD C T × Bool) ProbComp)
  | .inl n => coin n
  | .inr (.inl ⟨a, m⟩) => StateT.mk fun s =>
      pure ((encT cipher mac s.1 a m).1, ((encT cipher mac s.1 a m).2, s.2))
  | .inr (.inr ⟨a, e⟩) => StateT.mk fun s =>
      pure (none, (s.1, s.2 || hit mac s.1 a e))

theorem implO_query_bind [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    {α : Type} (q : (QSpec AD M C T).Domain)
    (cont : (QSpec AD M C T).Range q → OracleComp (QSpec AD M C T) α)
    (s : St KE KM AD C T) :
    (simulateQ (implO cipher mac) (liftM (OracleSpec.query q) >>= cont)).run s =
      (implO cipher mac q).run s >>= fun x =>
        (simulateQ (implO cipher mac) (cont x.1)).run x.2 := by
  simp [simulateQ_bind, simulateQ_query]

theorem implNF_query_bind (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    {α : Type} (q : (QSpec AD M C T).Domain)
    (cont : (QSpec AD M C T).Range q → OracleComp (QSpec AD M C T) α)
    (s : St KE KM AD C T × Bool) :
    (simulateQ (implNF cipher mac) (liftM (OracleSpec.query q) >>= cont)).run s =
      (implNF cipher mac q).run s >>= fun x =>
        (simulateQ (implNF cipher mac) (cont x.1)).run x.2 := by
  simp [simulateQ_bind, simulateQ_query]

@[simp] theorem implNF_inl (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (n : ℕ) (s : St KE KM AD C T × Bool) :
    (implNF cipher mac (.inl n)).run s =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, s) := by
  simp [implNF, coin]

/-- The first projection of `implNF` matches `implOnce`. -/
theorem nf_eq_implOnce (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (ke : KE) (km : KM) {α : Type} (oa : OracleComp (QSpec AD M C T) α)
    (s : St KE KM AD C T × Bool) (hs : s.1.key = (ke, km)) :
    (simulateQ (implOnce (fun a m =>
        pure (cipher.enc ke m, mac.tag km (a, cipher.enc ke m)))) oa).run s.1.chal.isSome =
      Prod.map id (fun z => z.1.chal.isSome) <$> (simulateQ (implNF cipher mac) oa).run s := by
  refine run_map
    (implOnce (fun a m => pure (cipher.enc ke m, mac.tag km (a, cipher.enc ke m))))
    (implNF cipher mac) (fun z => z.1.chal.isSome) (fun z => z.1.key = (ke, km))
    (fun t z hz => ?_) oa s hs
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · refine ⟨by simp [implOnce, implNF, coin], fun w hw => ?_⟩
    have hw' : w ∈ support ((coin n : StateT _ ProbComp _).run z) := by
      simpa [implNF, coin] using hw
    rw [mem_support_coin hw']; exact hz
  · by_cases hc : z.1.chal.isSome = true
    · refine ⟨by simp [implOnce, implNF, encT, hc], fun w hw => ?_⟩
      simp [implNF, encT, hc] at hw
      subst hw; exact hz
    · refine ⟨by simp [implOnce, implNF, encT, etm, hc, hz], fun w hw => ?_⟩
      simp [implNF, encT, hc] at hw
      subst hw; exact hz
  · refine ⟨by simp [implOnce, implNF], fun w hw => ?_⟩
    simp [implNF] at hw
    subst hw; exact hz

theorem evalDist_nf_fst_eq_chall [SampleableType KE] [SampleableType KM] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (B : OTCCAAdversary AD M (C × T)) :
    𝒟[do let key ← $ᵗ (KE × KM)
         Prod.fst <$> (simulateQ (implNF cipher mac) B).run ({ key, b := false }, false)] =
      𝒟[mac.branch false (redMACChall cipher B)] := by
  rw [mac_branch_false_chall_eq, uniform_prod KE KM]
  simp only [bind_assoc, pure_bind]
  have h1 : ∀ (ke : KE) (km : KM),
      Prod.fst <$> (simulateQ (implNF cipher mac) B).run ({ key := (ke, km), b := false }, false) =
        runOnce (fun a m => pure (cipher.enc ke m, mac.tag km (a, cipher.enc ke m))) B := by
    intro ke km
    have h2 := congrArg (Prod.fst <$> ·)
      (nf_eq_implOnce cipher mac ke km B ({ key := (ke, km), b := false }, false) rfl)
    simpa [runOnce, StateT.run'_eq, Functor.map_map] using h2.symm
  simp only [h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ KE) ($ᵗ KM) _

/-- The flag in `implNF` only ever gets OR-ed with its initial value. -/
theorem nf_flag (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    {α : Type} (oa : OracleComp (QSpec AD M C T) α)
    (s : St KE KM AD C T) (fl : Bool) :
    (simulateQ (implNF cipher mac) oa).run (s, fl) =
      Prod.map id (fun z : St KE KM AD C T × Bool => (z.1, fl || z.2)) <$>
        (simulateQ (implNF cipher mac) oa).run (s, false) := by
  have := run_map (implNF cipher mac) (implNF cipher mac)
    (fun z : St KE KM AD C T × Bool => (z.1, fl || z.2)) (fun _ => True)
    (fun t z _ => ?_) oa (s, false) trivial
  · simpa using this
  refine ⟨?_, fun _ _ => trivial⟩
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · simp [implNF, coin]
  · simp [implNF]
  · simp [implNF, Bool.or_assoc]

theorem flag_or (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    {α : Type} (oa : OracleComp (QSpec AD M C T) α)
    (s : St KE KM AD C T) (fl : Bool) :
    (fun z : α × St KE KM AD C T × Bool => z.2.2) <$>
        (simulateQ (implNF cipher mac) oa).run (s, fl) =
      (fl || ·) <$> ((fun z : α × St KE KM AD C T × Bool => z.2.2) <$>
        (simulateQ (implNF cipher mac) oa).run (s, false)) := by
  rw [nf_flag cipher mac oa s fl, Functor.map_map, Functor.map_map]
  rfl

theorem const_true_eq_one {α : Type} (mx : ProbComp α) :
    𝒟[mx >>= fun _ => (pure true : ProbComp Bool)] {true} = 1 :=
  le_antisymm (le_trans (measure_mono (Set.subset_univ _)) (evalDist_apply_univ_eq_one _).le)
    (le_evalDist_bind_apply_of_support _ _ (measurableSet_singleton _) fun _ _ => by simp)

theorem apply_le_one {α : Type} [MeasurableSpace α] (mx : ProbComp α) (E : Set α) :
    𝒟[mx] E ≤ 1 :=
  le_trans (measure_mono (Set.subset_univ _)) (evalDist_apply_univ_eq_one _).le

omit [DecidableEq AD] [DecidableEq C] in
theorem encT_b (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (s : St KE KM AD C T) (a : AD) (m : M) :
    (encT cipher mac s a m).2.b = s.b := by
  unfold encT; split <;> rfl

theorem dec_none (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (s : St KE KM AD C T) (a : AD) (e : C × T) (hh : hit mac s a e = false) :
    (if (s.chal == some (a, e)) = true then none else (etm cipher mac).dec s.key a e) = none := by
  split
  · rfl
  · rename_i hc
    simp only [hit, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hh
    simp only [beq_iff_eq] at hc
    rcases hh with hh | hh
    · exact absurd hh hc
    · simp [etm, beq_eq_false_iff_ne.mp hh]

/-- The real OT-CCA world is `implNF` until the flag is raised. -/
theorem real_le [SampleableType C] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (oa : OracleComp (QSpec AD M C T) Bool) :
    ∀ s : St KE KM AD C T, s.b = false → ∀ x : Bool,
      𝒟[(fun z => z.1 == x) <$> (simulateQ (implO cipher mac) oa).run s] {true} ≤
        𝒟[(fun z => z.1 == x) <$> (simulateQ (implNF cipher mac) oa).run (s, false)] {true} +
          𝒟[(fun z => z.2.2) <$> (simulateQ (implNF cipher mac) oa).run (s, false)] {true} := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _ x; simp
  | query_bind q k ih =>
    intro s hb x
    rw [implO_query_bind, implNF_query_bind, map_bind, map_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · have hcoin : (implO cipher mac (.inl n)).run s =
          (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
            fun u => pure (u, s) := by
        simp [implO]
      rw [hcoin, implNF_inl]
      simp only [bind_assoc, pure_bind]
      exact evalDist_bind_apply_le_add_of_support _ _ _ _ (measurableSet_singleton _)
        fun u _ => ih u s hb x
    · have henc : (implO cipher mac (.inr (.inl ⟨a, m⟩))).run s =
          pure (encT cipher mac s a m) := by
        simp [implO, otccaEncrypt, hb, encT]
        split <;> simp
      rw [henc]
      simp only [implNF, StateT.run_mk, pure_bind]
      exact ih _ _ ((encT_b cipher mac s a m).trans hb) x
    · have hdec : (implO cipher mac (.inr (.inr ⟨a, e⟩))).run s =
          pure ((if s.b || s.chal == some (a, e) then none
                 else (etm cipher mac).dec s.key a e), s) := by
        simp [implO, otccaDecrypt]
        split <;> simp
      rw [hdec]
      simp only [implNF, StateT.run_mk, pure_bind, hb, Bool.false_or]
      rcases hh : hit mac s a e
      · rw [dec_none cipher mac s a e hh]
        exact ih none s hb x
      · refine le_trans (apply_le_one _ _) (le_trans (le_of_eq ?_) le_add_self)
        have hf := flag_or cipher mac (k none) s true
        rw [hf, Functor.map_map, map_eq_bind_pure_comp]
        exact (const_true_eq_one _).symm

/-! #### Bounding the flag via `redMACForge` -/

/-- Run `forgeRedImpl cipher ke j` inside `mImpl mac`. -/
def runForge [SampleableType T] (mac : MACScheme KM (AD × C) T) (cipher : CipherScheme KE M C)
    (ke : KE) (j : ℕ) {α : Type} (oa : OracleComp (QSpec AD M C T) α)
    (st : ForgeState AD C T) (pst : MACScheme.PRFState KM (AD × C) T) :
    ProbComp ((α × ForgeState AD C T) × MACScheme.PRFState KM (AD × C) T) :=
  (simulateQ (mImpl mac) ((simulateQ (forgeRedImpl cipher ke j) oa).run st)).run pst

@[simp] theorem runForge_pure [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (j : ℕ)
    {α : Type} (a : α) (st : ForgeState AD C T) (pst : MACScheme.PRFState KM (AD × C) T) :
    runForge mac cipher ke j (pure a) st pst = pure ((a, st), pst) := by
  simp [runForge]

theorem runForge_query_bind [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (j : ℕ)
    {α : Type} (q : (QSpec AD M C T).Domain)
    (cont : (QSpec AD M C T).Range q → OracleComp (QSpec AD M C T) α)
    (st : ForgeState AD C T) (pst : MACScheme.PRFState KM (AD × C) T) :
    runForge mac cipher ke j (liftM (OracleSpec.query q) >>= cont) st pst =
      (simulateQ (mImpl mac) ((forgeRedImpl cipher ke j q).run st)).run pst >>= fun r =>
        runForge mac cipher ke j (cont r.1.1) r.1.2 r.2 := by
  simp [runForge, simulateQ_bind, simulateQ_query]

@[simp] theorem forgeStep_inl [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (j : ℕ) (n : ℕ)
    (st : ForgeState AD C T) (pst : MACScheme.PRFState KM (AD × C) T) :
    (simulateQ (mImpl mac)
      ((forgeRedImpl (AD := AD) (T := T) cipher ke j (.inl n)).run st)).run pst =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure ((u, st), pst) := by
  simp [forgeRedImpl, mImpl]

@[simp] theorem forgeStep_enc [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (j : ℕ) (a : AD) (m : M)
    (st : ForgeState AD C T) (pst : MACScheme.PRFState KM (AD × C) T) :
    (simulateQ (mImpl mac)
      ((forgeRedImpl (AD := AD) (T := T) cipher ke j (.inr (.inl (a, m)))).run st)).run pst =
      if st.chal.isSome then
        pure ((none, st), pst)
      else
        (MACScheme.prfEval mac (a, cipher.enc ke m)).run pst >>= fun r =>
          pure ((some (cipher.enc ke m, r.1),
            { st with chal := some (a, (cipher.enc ke m, r.1)) }), r.2) := by
  by_cases hc : st.chal.isSome = true <;> simp [forgeRedImpl, hc, MACScheme.evalQuery, mImpl]

@[simp] theorem forgeStep_dec [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (j : ℕ) (a : AD) (c : C) (τ : T)
    (st : ForgeState AD C T) (pst : MACScheme.PRFState KM (AD × C) T) :
    (simulateQ (mImpl mac)
      ((forgeRedImpl cipher ke j (.inr (.inr (a, (c, τ))))).run st)).run pst =
      if st.idx == j && (st.chal != some (a, (c, τ))) then
        (MACScheme.prfEval mac (a, c)).run pst >>= fun r =>
          pure ((none, { st with idx := st.idx + 1, forged := st.forged || (r.1 == τ) }), r.2)
      else
        pure ((none, { st with idx := st.idx + 1 }), pst) := by
  unfold forgeRedImpl
  by_cases h : (st.idx == j && (st.chal != some (a, (c, τ)))) = true
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte,
      StateT.run_lift, StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure]
    simp [MACScheme.evalQuery, mImpl]
  · have hf : (st.idx == j && (st.chal != some (a, (c, τ)))) = false := Bool.eq_false_iff.mpr h
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hf, Bool.false_eq_true, ↓reduceIte,
      StateT.run_set, StateT.run_pure, simulateQ_pure]

/-- Once `j < st.idx`, `runForge` never modifies `st.forged`. -/
theorem runForge_forged_of_lt [SampleableType T] (mac : MACScheme KM (AD × C) T)
    (cipher : CipherScheme KE M C) (ke : KE) (j : ℕ)
    {α : Type} (oa : OracleComp (QSpec AD M C T) α) :
    ∀ (st : ForgeState AD C T) (pst : MACScheme.PRFState KM (AD × C) T),
      j < st.idx →
      𝒟[(fun r => r.1.2.forged) <$> runForge mac cipher ke j oa st pst] =
        𝒟[(pure st.forged : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st pst _; simp
  | query_bind t k ih =>
    intro st pst hlt
    rw [runForge_query_bind, map_bind]
    rcases t with n | ⟨a, m⟩ | ⟨a, ⟨c, τ⟩⟩
    · simp only [forgeStep_inl, bind_assoc, pure_bind]
      refine (evalDist_bind_congr _ _ (fun _ => pure st.forged) fun u => ?_).trans
        (OracleComp.evalDist_bind_const _ _)
      exact ih u st pst hlt
    · rcases hc : st.chal.isSome
      · simp only [forgeStep_enc, hc, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine (evalDist_bind_congr _ _ (fun _ => pure st.forged) fun r => ?_).trans
          (OracleComp.evalDist_bind_const _ _)
        exact ih (some (cipher.enc ke m, r.1))
          { st with chal := some (a, (cipher.enc ke m, r.1)) } r.2 hlt
      · simp only [forgeStep_enc, hc, ↓reduceIte, pure_bind]
        exact ih none st pst hlt
    · have hne : (st.idx == j) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hlt)
      simp only [forgeStep_dec, hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_bind]
      exact ih none { st with idx := st.idx + 1 } pst (Nat.lt_succ_of_lt hlt)

/-- Union bound for a flag raised before a continuation. -/
theorem union_step {α : Type} (mx : ProbComp α) (a : α → Bool) (g : α → ProbComp Bool) :
    𝒟[mx >>= fun x => (a x || ·) <$> g x] {true} ≤
      𝒟[mx >>= fun x => pure (a x)] {true} + 𝒟[mx >>= g] {true} := by
  refine evalDist_bind_apply_le_add_of_support mx _ _ _ (measurableSet_singleton _)
    fun x _ => ?_
  cases a x
  · simp
  · simp only [Bool.true_or]
    refine le_add_right ?_
    calc _ ≤ 𝒟[(Function.const Bool true <$> g x)] Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := evalDist_apply_univ_eq_one _
      _ ≤ _ := by simp

theorem bind_le_sum_bind {α : Type} (mx : ProbComp α) (f : α → ProbComp Bool)
    (s : Finset ℕ) (g : ℕ → α → ProbComp Bool)
    (h : ∀ u ∈ support mx, 𝒟[f u] {true} ≤ ∑ k ∈ s, 𝒟[g k u] {true}) :
    𝒟[mx >>= f] {true} ≤ ∑ k ∈ s, 𝒟[mx >>= g k] {true} := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable]
    rw [← MeasureTheory.lintegral_finsetSum' s
      (fun _ _ => Measurable.of_discrete.aemeasurable)]
    exact MeasureTheory.lintegral_mono fun u => ih u fun a ha =>
      h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

/-- The `implNF` flag is bounded by the sum over `k < n` of `runForge` in the real PRF world. -/
theorem nf_flag_le_sum_forge_real [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (ke : KE) (km : KM) (oa : OracleComp (QSpec AD M C T) Bool) :
    ∀ (n : ℕ), oa.IsQueryBoundP (fun q => isDecQuery q = true) n →
      ∀ (chal : Option (AD × (C × T))) (i : ℕ),
        𝒟[(fun z => z.2.2) <$> (simulateQ (implNF cipher mac) oa).run
            ({ key := (ke, km), b := false, chal }, false)] {true} ≤
          ∑ k ∈ Finset.range n,
            𝒟[(fun r => r.1.2.forged) <$>
              runForge mac cipher ke (i + k) oa { chal, idx := i, forged := false }
                { key := km, b := false, table := [] }] {true} := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _ chal i; simp
  | query_bind q cont ih =>
    intro n hn chal i
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [implNF_query_bind, map_bind]
    simp only [runForge_query_bind, map_bind]
    rcases q with m | ⟨a, msg⟩ | ⟨a, ⟨c, τ⟩⟩
    · have hndec : isDecQuery (AD := AD) (M := M) (C := C × T) (.inl m) = false := rfl
      simp only [implNF_inl, forgeStep_inl, bind_assoc, pure_bind]
      exact bind_le_sum_bind _ _ _ _ fun u _ =>
        ih u n (by simpa only [hndec, Bool.false_eq_true, ↓reduceIte] using hn.2 u) chal i
    · have hndec : isDecQuery (AD := AD) (M := M) (C := C × T) (.inr (.inl ⟨a, msg⟩)) = false := rfl
      rcases hc : chal.isSome
      · simp only [implNF, encT, etm, hc, Bool.false_eq_true, ↓reduceIte, StateT.run_mk, pure_bind,
          forgeStep_enc, prfEval_run_false _ _ { key := km, b := false, table := [] } rfl]
        exact ih _ n (by simpa only [hndec, Bool.false_eq_true, ↓reduceIte] using hn.2 _) _ i
      · simp only [implNF, encT, hc, ↓reduceIte, StateT.run_mk, pure_bind, forgeStep_enc]
        exact ih none n (by simpa only [hndec, Bool.false_eq_true, ↓reduceIte] using hn.2 none) chal i
    · have hdec : isDecQuery (AD := AD) (M := M) (C := C × T) (.inr (.inr ⟨a, ⟨c, τ⟩⟩)) = true := rfl
      have hpos : 0 < n := hn.1.resolve_left (by simp [hdec])
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hcont : (cont none).IsQueryBoundP (fun q => isDecQuery q = true) m := by
        simpa only [hdec, ↓reduceIte, Nat.add_sub_cancel] using hn.2 none
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      have hLHS : 𝒟[(implNF cipher mac (.inr (.inr (a, c, τ)))).run
            ({ key := (ke, km), b := false, chal }, false) >>= fun x =>
              (fun z => z.2.2) <$> (simulateQ (implNF cipher mac) (cont x.1)).run x.2] {true} ≤
          𝒟[(pure (hit mac { key := (ke, km), b := false, chal } a (c, τ)) : ProbComp Bool)] {true} +
          𝒟[(fun z => z.2.2) <$> (simulateQ (implNF cipher mac) (cont none)).run
            ({ key := (ke, km), b := false, chal }, false)] {true} := by
        have hstep : ((implNF cipher mac (.inr (.inr (a, c, τ)))).run
              ({ key := (ke, km), b := false, chal }, false) >>= fun x =>
                (fun z => z.2.2) <$> (simulateQ (implNF cipher mac) (cont x.1)).run x.2) =
            (pure () : ProbComp Unit) >>= fun _ =>
              (hit mac { key := (ke, km), b := false, chal } a (c, τ) || ·) <$>
                ((fun z => z.2.2) <$> (simulateQ (implNF cipher mac) (cont none)).run
                  ({ key := (ke, km), b := false, chal }, false)) := by
          simp only [implNF, StateT.run_mk, pure_bind, Bool.false_or]
          exact flag_or cipher mac (cont none) { key := (ke, km), b := false, chal } _
        rw [hstep]
        simpa using union_step (pure ())
          (fun _ => hit mac { key := (ke, km), b := false, chal } a (c, τ))
          (fun _ => (fun z => z.2.2) <$> (simulateQ (implNF cipher mac) (cont none)).run
            ({ key := (ke, km), b := false, chal }, false))
      have hRHS0 : 𝒟[(simulateQ (mImpl mac) ((forgeRedImpl cipher ke i (.inr (.inr (a, c, τ)))).run
              { chal, idx := i, forged := false })).run { key := km, b := false, table := [] } >>=
              fun r => (fun r => r.1.2.forged) <$>
                runForge mac cipher ke i (cont r.1.1) r.1.2 r.2] =
          𝒟[(pure (hit mac { key := (ke, km), b := false, chal } a (c, τ)) : ProbComp Bool)] := by
        by_cases hch : (chal != some (a, (c, τ))) = true
        · simp only [forgeStep_dec, beq_self_eq_true, hch, Bool.true_and, ↓reduceIte,
            prfEval_run_false _ _ { key := km, b := false, table := [] } rfl,
            pure_bind, Bool.false_or]
          rw [runForge_forged_of_lt mac cipher ke i (cont none) _ _ (Nat.lt_succ_self i)]
          simp [hit, hch]
        · have hchf : (chal != some (a, (c, τ))) = false := Bool.eq_false_iff.mpr hch
          simp only [forgeStep_dec, beq_self_eq_true, hchf, Bool.true_and, Bool.false_eq_true,
            ↓reduceIte, pure_bind]
          rw [runForge_forged_of_lt mac cipher ke i (cont none) _ _ (Nat.lt_succ_self i)]
          simp [hit, hchf]
      have hRHS_succ : ∀ k,
          ((simulateQ (mImpl mac) ((forgeRedImpl cipher ke (i + (k + 1)) (.inr (.inr (a, c, τ)))).run
            { chal, idx := i, forged := false })).run { key := km, b := false, table := [] } >>=
            fun r => (fun r => r.1.2.forged) <$>
              runForge mac cipher ke (i + (k + 1)) (cont r.1.1) r.1.2 r.2) =
          (fun r => r.1.2.forged) <$> runForge mac cipher ke ((i + 1) + k) (cont none)
            { chal, idx := i + 1, forged := false } { key := km, b := false, table := [] } := by
        intro k
        have hne : (i == i + (k + 1)) = false := beq_eq_false_iff_ne.mpr (by omega)
        have heq : i + (k + 1) = (i + 1) + k := by omega
        simp only [forgeStep_dec, hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [heq]
      simp only [hRHS0, hRHS_succ]
      rw [add_comm (∑ k ∈ Finset.range m, _)]
      exact hLHS.trans (add_le_add le_rfl (ih none m hcont chal (i + 1)))

theorem mac_branch_false_forge_eq [SampleableType KE] [SampleableType KM] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T) (j : ℕ)
    (B : OTCCAAdversary AD M (C × T)) :
    mac.branch false (redMACForge cipher j B) =
      (do let km ← $ᵗ KM; let ke ← $ᵗ KE
          (fun r => r.1.2.forged) <$>
            runForge mac cipher ke j B {} { key := km, b := false, table := [] }) := by
  rw [mac_branch_eq]
  unfold redMACForge
  refine bind_congr fun km => ?_
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind,
    simulateQ_mImpl_liftM_run, bind_assoc, pure_bind]
  refine bind_congr fun ke => ?_
  simp [runForge]

theorem nf_flag_le_sum_branch_false [SampleableType KE] [SampleableType KM] [SampleableType T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (B : OTCCAAdversary AD M (C × T)) {qd : ℕ} (hqd : MakesAtMostDecQueries B qd) :
    𝒟[do let key ← $ᵗ (KE × KM)
         (fun z : Bool × St KE KM AD C T × Bool => z.2.2) <$>
           (simulateQ (implNF cipher mac) B).run (({ key, b := false } : St KE KM AD C T), false)]
      {true} ≤
      ∑ j ∈ Finset.range qd, 𝒟[mac.branch false (redMACForge cipher j B)] {true} := by
  have hswap : 𝒟[do let key ← $ᵗ (KE × KM)
                    (fun z : Bool × St KE KM AD C T × Bool => z.2.2) <$>
                      (simulateQ (implNF cipher mac) B).run
                        (({ key, b := false } : St KE KM AD C T), false)] =
    𝒟[do let km ← $ᵗ KM; let ke ← $ᵗ KE
         (fun z : Bool × St KE KM AD C T × Bool => z.2.2) <$>
           (simulateQ (implNF cipher mac) B).run
             (({ key := (ke, km), b := false } : St KE KM AD C T), false)] := by
    rw [uniform_prod KE KM]
    simp only [bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_bind_swap ($ᵗ KE) ($ᵗ KM) _
  rw [hswap]
  simp only [mac_branch_false_forge_eq]
  refine bind_le_sum_bind ($ᵗ KM) _ _ _ fun km _ => ?_
  refine bind_le_sum_bind ($ᵗ KE) _ _ _ fun ke _ => ?_
  simpa using nf_flag_le_sum_forge_real cipher mac ke km B qd hqd none 0

/-! #### Bounding `mac.branch true (redMACForge cipher j B)` by `(Fintype.card T)⁻¹` -/

theorem bind_le_of_support {α β : Type} [MeasurableSpace β] (mx : ProbComp α)
    (f : α → ProbComp β) {E : Set β} (hE : MeasurableSet E) {r : ℝ≥0∞}
    (h : ∀ a ∈ support mx, 𝒟[f a] E ≤ r) : 𝒟[mx >>= f] E ≤ r := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply hE Measurable.of_discrete.aemeasurable]
    calc _ ≤ ∫⁻ _u, r ∂𝒟[(query t : ProbComp _)] :=
          lintegral_mono fun u => ih u fun a ha =>
            h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)
      _ = r := by rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem uniform_tag_eq [SampleableType T] [Fintype T] (v : T) :
    𝒟[(fun u => u == v) <$> ($ᵗ T : ProbComp T)] {true} = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace T := ⊤
  have : (fun u : T => u == v) ⁻¹' {true} = {v} := by ext u; simp
  rw [evalDist_map _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _), this,
    SampleableType.evalDist_uniformSample_singleton]

/-- State invariant of `runForge` in the ideal PRF world (`pst.b = true`) before query `j`. -/
def IdealForgeInv (st : ForgeState AD C T) (pst : MACScheme.PRFState KM (AD × C) T) : Prop :=
  pst.b = true ∧ st.forged = false ∧
    ((st.chal = none ∧ pst.table = []) ∨
     ∃ a c τ, st.chal = some (a, (c, τ)) ∧ pst.table = [((a, c), τ)])

theorem runForge_true_le [SampleableType T] [Fintype T]
    (mac : MACScheme KM (AD × C) T) (cipher : CipherScheme KE M C) (ke : KE) (j : ℕ)
    (oa : OracleComp (QSpec AD M C T) Bool) :
    ∀ (st : ForgeState AD C T) (pst : MACScheme.PRFState KM (AD × C) T),
      IdealForgeInv st pst →
      𝒟[(fun r => r.1.2.forged) <$> runForge mac cipher ke j oa st pst] {true} ≤
        (Fintype.card T : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st pst ⟨_, hfg, _⟩
    simp [hfg]
  | query_bind q cont ih =>
    intro st pst ⟨hb, hfg, htab⟩
    by_cases hgt : j < st.idx
    · rw [runForge_forged_of_lt mac cipher ke j _ st pst hgt, hfg]
      simp
    · rw [runForge_query_bind, map_bind]
      rcases q with m | ⟨a, msg⟩ | ⟨a, ⟨c, τ⟩⟩
      · simp only [forgeStep_inl, bind_assoc, pure_bind]
        exact bind_le_of_support _ _ (measurableSet_singleton _) fun u _ =>
          ih u st pst ⟨hb, hfg, htab⟩
      · rcases htab with ⟨hchal, htbl⟩ | ⟨aStar, cStar, τStar, hchal, htbl⟩
        · simp only [forgeStep_enc, hchal, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            prfEval_run_true_nil mac _ pst hb htbl, bind_assoc, pure_bind]
          exact bind_le_of_support _ _ (measurableSet_singleton _) fun τ' _ =>
            ih _ _ _ ⟨hb, hfg, Or.inr ⟨a, cipher.enc ke msg, τ', rfl, rfl⟩⟩
        · simp only [forgeStep_enc, hchal, Option.isSome_some, ↓reduceIte, pure_bind]
          exact ih none st pst ⟨hb, hfg, Or.inr ⟨aStar, cStar, τStar, hchal, htbl⟩⟩
      · by_cases hcheck : (st.idx == j && (st.chal != some (a, (c, τ)))) = true
        · obtain ⟨hij, hch⟩ := Bool.and_eq_true_iff.mp hcheck
          have hij_eq : st.idx = j := beq_iff_eq.mp hij
          simp only [forgeStep_dec, hcheck, ↓reduceIte, hfg, Bool.false_or]
          rcases htab with ⟨hchal, htbl⟩ | ⟨aStar, cStar, τStar, hchal, htbl⟩
          · simp only [prfEval_run_true_nil mac _ pst hb htbl, bind_assoc, pure_bind]
            have hpost : 𝒟[($ᵗ T : ProbComp T) >>= fun τ' =>
                (fun r => r.1.2.forged) <$>
                  runForge mac cipher ke j (cont none)
                    { st with idx := st.idx + 1, forged := (τ' == τ) }
                    { pst with table := [((a, c), τ')] }] =
              𝒟[(fun τ' => τ' == τ) <$> ($ᵗ T : ProbComp T)] := by
              rw [map_eq_bind_pure_comp]
              exact evalDist_bind_congr ($ᵗ T) _ _ fun τ' =>
                runForge_forged_of_lt mac cipher ke j (cont none) _ _
                  (hij_eq ▸ Nat.lt_succ_self st.idx)
            rw [hpost, uniform_tag_eq τ]
          · by_cases hac : (a, c) = (aStar, cStar)
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hac
              have hne_τ : (τStar == τ) = false := by
                rw [beq_eq_false_iff_ne]
                intro hτ; subst hτ; simp [hchal] at hch
              simp only [prfEval_run_true_hit mac _ τStar pst hb htbl, pure_bind, hne_τ]
              rw [runForge_forged_of_lt mac cipher ke j (cont none) _ _
                (hij_eq ▸ Nat.lt_succ_self st.idx)]
              simp
            · simp only [prfEval_run_true_miss mac _ _ τStar pst hb htbl hac, bind_assoc, pure_bind]
              have hpost : 𝒟[($ᵗ T : ProbComp T) >>= fun τ' =>
                  (fun r => r.1.2.forged) <$>
                    runForge mac cipher ke j (cont none)
                      { st with idx := st.idx + 1, forged := (τ' == τ) }
                      { pst with table := ((a, c), τ') :: [((aStar, cStar), τStar)] }] =
                𝒟[(fun τ' => τ' == τ) <$> ($ᵗ T : ProbComp T)] := by
                rw [map_eq_bind_pure_comp]
                exact evalDist_bind_congr ($ᵗ T) _ _ fun τ' =>
                  runForge_forged_of_lt mac cipher ke j (cont none) _ _
                    (hij_eq ▸ Nat.lt_succ_self st.idx)
              rw [hpost, uniform_tag_eq τ]
        · have hskip : (st.idx == j && (st.chal != some (a, (c, τ)))) = false :=
            Bool.eq_false_iff.mpr hcheck
          simp only [forgeStep_dec, hskip, Bool.false_eq_true, ↓reduceIte, pure_bind]
          exact ih none { st with idx := st.idx + 1 } pst ⟨hb, hfg, htab⟩

theorem mac_branch_true_forge_le [SampleableType KE] [SampleableType KM]
    [SampleableType T] [Fintype T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T) (j : ℕ)
    (B : OTCCAAdversary AD M (C × T)) :
    𝒟[mac.branch true (redMACForge cipher j B)] {true} ≤ (Fintype.card T : ℝ≥0∞)⁻¹ := by
  rw [mac_branch_eq]
  unfold redMACForge
  refine bind_le_of_support ($ᵗ KM) _ (measurableSet_singleton true) fun km _ => ?_
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind,
    simulateQ_mImpl_liftM_run, bind_assoc, pure_bind]
  refine bind_le_of_support ($ᵗ KE) _ (measurableSet_singleton true) fun ke _ => ?_
  simpa [runForge] using
    runForge_true_le mac cipher ke j B {} { key := km, b := true } ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem apply_eq_beq (mx : ProbComp Bool) (x : Bool) :
    𝒟[mx] {x} = 𝒟[(· == x) <$> mx] {true} := by
  rw [evalDist_map _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  congr 1; ext y; simp

end EtMProof

open EtMProof

/-- OT-CCA security of Encrypt-then-MAC (`etm`) for any adversary `B` making at most `qd`
decryption queries. -/
theorem etm_otcca [DecidableEq AD] [DecidableEq C] [DecidableEq T]
    [SampleableType KE] [SampleableType KM] [SampleableType C] [SampleableType T] [Fintype T]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T)
    (B : OTCCAAdversary AD M (C × T)) (qd : ℕ)
    (hqd : MakesAtMostDecQueries B qd) :
    (etm cipher mac).otccaAdvantage B ≤
      cipher.indcpaAdvantage (redCipher B) +
      mac.prfAdvantage (redMACChall cipher B) +
      ∑ j ∈ Finset.range qd, mac.prfAdvantage (redMACForge cipher j B) +
      qd / Fintype.card T := by
  rw [otccaAdvantage_eq_boolDist, evalDist_otccaBranch_true,
    ← evalDist_cipher_branch_true cipher B]
  have htri1 := Measure.boolDist_triangle
    𝒟[cipher.branch true (redCipher B)]
    𝒟[cipher.branch false (redCipher B)]
    𝒟[otccaBranch cipher mac false B]
  have htri2 := Measure.boolDist_triangle
    𝒟[mac.branch true (redMACChall cipher B)]
    𝒟[mac.branch false (redMACChall cipher B)]
    𝒟[otccaBranch cipher mac false B]
  rw [evalDist_mac_branch_true_chall] at htri2
  have hreal : 𝒟[mac.branch false (redMACChall cipher B)].boolDist
      𝒟[otccaBranch cipher mac false B] ≤
      ∑ j ∈ Finset.range qd, mac.prfAdvantage (redMACForge cipher j B) +
      qd / Fintype.card T := by
    rw [Measure.boolDist_comm]
    refine Measure.boolDist_le_of_apply_le _ _ fun x => ?_
    rw [← evalDist_nf_fst_eq_chall cipher mac B,
      apply_eq_beq (otccaBranch cipher mac false B) x,
      apply_eq_beq _ x]
    unfold otccaBranch
    simp only [StateT.run'_eq, map_bind, Functor.map_map]
    have hstep1 := le_trans
      (evalDist_bind_apply_le_add_of_support ($ᵗ (KE × KM)) _ _ _ (measurableSet_singleton _)
        fun key _ => real_le cipher mac B { key, b := false } rfl x)
      (add_le_add le_rfl (nf_flag_le_sum_branch_false cipher mac B hqd))
    refine hstep1.trans (add_le_add le_rfl ?_)
    calc ∑ j ∈ Finset.range qd, 𝒟[mac.branch false (redMACForge cipher j B)] {true}
        ≤ ∑ j ∈ Finset.range qd, (mac.prfAdvantage (redMACForge cipher j B) +
            (Fintype.card T : ℝ≥0∞)⁻¹) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [MACScheme.prfAdvantage_eq_boolDist, Measure.boolDist_comm, add_comm]
          exact (Measure.apply_true_le_add_boolDist
            𝒟[mac.branch false (redMACForge cipher j B)]
            𝒟[mac.branch true (redMACForge cipher j B)]).trans
            (add_le_add (mac_branch_true_forge_le cipher mac j B) le_rfl)
      _ = ∑ j ∈ Finset.range qd, mac.prfAdvantage (redMACForge cipher j B) +
            qd / Fintype.card T := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            div_eq_mul_inv]
  calc 𝒟[cipher.branch true (redCipher B)].boolDist 𝒟[otccaBranch cipher mac false B]
      ≤ 𝒟[cipher.branch true (redCipher B)].boolDist 𝒟[cipher.branch false (redCipher B)] +
          (𝒟[cipher.branch false (redCipher B)].boolDist
            𝒟[mac.branch false (redMACChall cipher B)] +
          𝒟[mac.branch false (redMACChall cipher B)].boolDist
            𝒟[otccaBranch cipher mac false B]) :=
        htri1.trans (add_le_add le_rfl htri2)
    _ ≤ cipher.indcpaAdvantage (redCipher B) +
        (mac.prfAdvantage (redMACChall cipher B) +
        (∑ j ∈ Finset.range qd, mac.prfAdvantage (redMACForge cipher j B) +
          qd / Fintype.card T)) := by
        rw [CipherScheme.indcpaAdvantage_eq_boolDist, MACScheme.prfAdvantage_eq_boolDist,
          evalDist_mac_branch_true_chall]
        exact add_le_add le_rfl (add_le_add le_rfl hreal)
    _ = cipher.indcpaAdvantage (redCipher B) +
        mac.prfAdvantage (redMACChall cipher B) +
        ∑ j ∈ Finset.range qd, mac.prfAdvantage (redMACForge cipher j B) +
        qd / Fintype.card T := by
        rw [← add_assoc, ← add_assoc]

/-- Specialization of `etm_otcca` to `τ`-bit tags (`BitVec τ`), with guessing term `qd / 2 ^ τ`. -/
theorem etm_otcca_bitvec {τ : ℕ} [DecidableEq AD] [DecidableEq C]
    [SampleableType KE] [SampleableType KM] [SampleableType C]
    (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) (BitVec τ))
    (B : OTCCAAdversary AD M (C × BitVec τ)) (qd : ℕ)
    (hqd : MakesAtMostDecQueries B qd) :
    (etm cipher mac).otccaAdvantage B ≤
      cipher.indcpaAdvantage (redCipher B) +
      mac.prfAdvantage (redMACChall cipher B) +
      ∑ j ∈ Finset.range qd, mac.prfAdvantage (redMACForge cipher j B) +
      qd / 2 ^ τ := by
  simpa [Fintype.card_bitVec] using etm_otcca cipher mac B qd hqd

end EtM

end AEADScheme

end CryptoGames
