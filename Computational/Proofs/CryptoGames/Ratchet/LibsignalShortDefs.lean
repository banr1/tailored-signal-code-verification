/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance

/-!
# Short public-part and wire-length predicates

**Checked by Lean.**

Query-bound and guarded-execution predicates restricting encryption public parts to `< 2^29` bytes
(`LibsignalMsgPublicPart.shortB`) and decryption or injection wires to `< 2^32` bytes.
-/

@[expose] public section

open OracleComp OracleSpec

namespace CryptoGames

namespace AEADScheme

variable {K AD M C : Type}

/-- The OT-CCA query `t` is an encryption query whose AD fails `ok`. -/
def otEncBad (ok : AD → Bool) : (unifSpec + otccaSpec AD M C).Domain → Bool
  | .inr (.inl ⟨a, _⟩) => !ok a
  | _ => false

/-- Every encryption query of `B` has an AD with `ok` (decryption queries are unrestricted). -/
def OTEncADsOk (ok : AD → Bool) (B : OTCCAAdversary AD M C) : Prop :=
  B.IsQueryBoundP (fun t => otEncBad (M := M) (C := C) ok t = true) 0

end AEADScheme

namespace FSAEAD

variable {SS RS AD Msg C : Type}

/-- The FS-AEAD query `t` is a `transmit` or `challenge` with a message failing `ok`. -/
def encBadMsg (ok : Msg → Bool) : (unifSpec + spec SS RS AD Msg C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inl (.inl ⟨_, m⟩))))) => !ok m
  | .inr (.inl (.inl (.inl (.inl (.inr ⟨_, m₀, m₁⟩))))) => !ok m₀ || !ok m₁
  | _ => false

/-- Every message of a `transmit` / `challenge` query of `A` satisfies `ok`. -/
def EncMsgsOk (ok : Msg → Bool) (A : Adversary SS RS AD Msg C) : Prop :=
  A.IsQueryBoundP (fun t => encBadMsg (SS := SS) (RS := RS) (AD := AD) (C := C) ok t = true) 0

end FSAEAD

namespace GuardedSafe

section Combinators

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}
  {RespOk : (t : ι) → spec.Range t → Prop} {Q : ι → Prop} {σ α β : Type}

/-- `GuardedSafePost RespOk Q P oa` states that along every execution path of `oa` whose oracle
responses satisfy `RespOk`, no query satisfies `Q` and every pure return value satisfies `P`. -/
inductive GuardedSafePost (RespOk : (t : ι) → spec.Range t → Prop) (Q : ι → Prop)
    {α : Type} (P : α → Prop) : OracleComp spec α → Prop
  | pure {x : α} (h : P x) : GuardedSafePost RespOk Q P (pure x)
  | query_bind {t : ι} {mx : spec.Range t → OracleComp spec α}
      (hQt : ¬ Q t) (h : ∀ u, RespOk t u → GuardedSafePost RespOk Q P (mx u)) :
      GuardedSafePost RespOk Q P (liftM (OracleSpec.query t) >>= mx)

theorem GuardedSafePost.true_of_false (oa : OracleComp spec α) :
    GuardedSafePost (fun _ _ => True) (fun _ => False) (fun _ => True) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => exact GuardedSafePost.pure trivial
  | query_bind _ _ ih => exact GuardedSafePost.query_bind not_false fun u _ => ih u

theorem GuardedSafePost.of_isQueryBoundP [DecidablePred Q] {oa : OracleComp spec α}
    (h : IsQueryBoundP oa Q 0) : GuardedSafePost RespOk Q (fun _ => True) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => exact GuardedSafePost.pure trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have hQt : ¬ Q t := h.1.resolve_right (Nat.not_lt_zero 0)
    exact GuardedSafePost.query_bind hQt fun u _ => ih u (by simpa [hQt] using h.2 u)

theorem GuardedSafePost.and_isQueryBoundP [DecidablePred Q]
    {Q₂ : ι → Prop} [DecidablePred Q₂] {P : α → Prop} {oa : OracleComp spec α}
    (h₁ : GuardedSafePost RespOk Q P oa) (h₂ : IsQueryBoundP oa Q₂ 0) :
    GuardedSafePost RespOk (fun t => Q t ∨ Q₂ t) P oa := by
  induction h₁ with
  | pure h => exact GuardedSafePost.pure h
  | @query_bind t mx hQt _ ih =>
    rw [isQueryBoundP_query_bind_iff] at h₂
    have hQt₂ : ¬ Q₂ t := h₂.1.resolve_right (Nat.not_lt_zero 0)
    exact GuardedSafePost.query_bind (by rintro (h | h); exact hQt h; exact hQt₂ h)
      fun u hu => ih u hu (by simpa [hQt₂] using h₂.2 u)

theorem GuardedSafePost.bind {P : α → Prop} {R : β → Prop} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} (hoa : GuardedSafePost RespOk Q P oa)
    (hob : ∀ a, P a → GuardedSafePost RespOk Q R (ob a)) :
    GuardedSafePost RespOk Q R (oa >>= ob) := by
  induction hoa with
  | pure h =>
    rw [pure_bind]
    exact hob _ h
  | query_bind hQt _ ih =>
    rw [bind_assoc]
    exact GuardedSafePost.query_bind hQt fun u hu => ih u hu

theorem GuardedSafePost.mono {P R : α → Prop} {oa : OracleComp spec α}
    (hoa : GuardedSafePost RespOk Q P oa) (hPR : ∀ a, P a → R a) :
    GuardedSafePost RespOk Q R oa := by
  induction hoa with
  | pure h => exact GuardedSafePost.pure (hPR _ h)
  | query_bind hQt _ ih => exact GuardedSafePost.query_bind hQt fun u hu => ih u hu

theorem GuardedSafePost.map {P : α → Prop} {R : β → Prop} (f : α → β) {oa : OracleComp spec α}
    (hoa : GuardedSafePost RespOk Q P oa) (hf : ∀ a, P a → R (f a)) :
    GuardedSafePost RespOk Q R (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact hoa.bind fun a ha => GuardedSafePost.pure (hf a ha)

theorem GuardedSafePost.query {t : spec.Domain} (hQt : ¬ Q t) :
    GuardedSafePost RespOk Q (RespOk t)
      (query (spec := spec) t : OracleComp spec (spec.Range t)) := by
  change GuardedSafePost RespOk Q (RespOk t) (liftM (spec.query t))
  rw [← bind_pure (liftM (spec.query t))]
  exact GuardedSafePost.query_bind hQt fun u hu => GuardedSafePost.pure hu

theorem GuardedSafePost.liftComp_unif {τ : Type} {tspec : OracleSpec.{0, 0} τ}
    {RespOk' : (t : (unifSpec + tspec).Domain) → (unifSpec + tspec).Range t → Prop}
    {Q' : (unifSpec + tspec).Domain → Prop} (hQu : ∀ u, ¬ Q' (.inl u))
    (mx : ProbComp α) :
    GuardedSafePost RespOk' Q' (fun _ => True)
      (liftM mx : OracleComp (unifSpec + tspec) α) := by
  change GuardedSafePost RespOk' Q' (fun _ => True) (liftComp mx (unifSpec + tspec))
  induction mx using OracleComp.inductionOn with
  | pure _ => exact GuardedSafePost.pure trivial
  | query_bind t mx ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query]
    exact GuardedSafePost.query_bind (hQu t) fun u _ => ih u

/-- `GuardedSafeS RespOk Q I P x` states that from any state satisfying `I`, running `x` under
responses satisfying `RespOk` makes no `Q`-queries and every `(a, s')` returned satisfies `P a s'`. -/
def GuardedSafeS (RespOk : (t : ι) → spec.Range t → Prop) (Q : ι → Prop)
    {σ α : Type} (I : σ → Prop) (P : α → σ → Prop)
    (x : StateT σ (OracleComp spec) α) : Prop :=
  ∀ s, I s → GuardedSafePost RespOk Q (fun r => P r.1 r.2) (x.run s)

theorem guardedSafeS_pure {I : σ → Prop} {P : α → σ → Prop} (a : α) (h : ∀ s, I s → P a s) :
    GuardedSafeS RespOk Q I P (pure a) := fun s hs => by
  rw [StateT.run_pure]
  exact GuardedSafePost.pure (h s hs)

theorem guardedSafeS_pure_true {I : σ → Prop} (a : α) :
    GuardedSafeS RespOk Q I (fun _ s => I s) (pure a) :=
  guardedSafeS_pure a fun _ hs => hs

theorem guardedSafeS_bind {I : σ → Prop} {P : α → σ → Prop} {R : β → σ → Prop}
    {x : StateT σ (OracleComp spec) α} {f : α → StateT σ (OracleComp spec) β}
    (hx : GuardedSafeS RespOk Q I P x) (hf : ∀ a, GuardedSafeS RespOk Q (P a) R (f a)) :
    GuardedSafeS RespOk Q I R (x >>= f) := fun s hs => by
  rw [StateT.run_bind]
  exact (hx s hs).bind fun p hp => hf p.1 p.2 hp

theorem guardedSafeS_bind_true {I : σ → Prop} {R : β → σ → Prop}
    {x : StateT σ (OracleComp spec) α} {f : α → StateT σ (OracleComp spec) β}
    (hx : GuardedSafeS RespOk Q I (fun _ s => I s) x)
    (hf : ∀ a, GuardedSafeS RespOk Q I R (f a)) :
    GuardedSafeS RespOk Q I R (x >>= f) :=
  guardedSafeS_bind hx hf

theorem guardedSafeS_bind_and {I : σ → Prop} {C : α → Prop} {R : β → σ → Prop}
    {x : StateT σ (OracleComp spec) α} {f : α → StateT σ (OracleComp spec) β}
    (hx : GuardedSafeS RespOk Q I (fun a s => C a ∧ I s) x)
    (hf : ∀ a, C a → GuardedSafeS RespOk Q I R (f a)) :
    GuardedSafeS RespOk Q I R (x >>= f) := fun s hs => by
  rw [StateT.run_bind]
  exact (hx s hs).bind fun p hp => hf p.1 hp.1 p.2 hp.2

theorem guardedSafeS_get_bind {I : σ → Prop} {R : α → σ → Prop}
    {f : σ → StateT σ (OracleComp spec) α}
    (hf : ∀ s, I s → GuardedSafeS RespOk Q I R (f s)) :
    GuardedSafeS RespOk Q I R (get >>= f) := fun s hs => by
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  exact hf s hs s hs

theorem guardedSafeS_set {I : σ → Prop} {P : PUnit → σ → Prop} (s' : σ)
    (h : ∀ s, I s → P () s') :
    GuardedSafeS RespOk Q I P (set s') := fun s hs => by
  rw [StateT.run_set]
  exact GuardedSafePost.pure (h s hs)

theorem guardedSafeS_set_true {I : σ → Prop} (s' : σ) (h : ∀ s, I s → I s') :
    GuardedSafeS RespOk Q I (fun _ s => I s) (set s') :=
  guardedSafeS_set s' h

theorem guardedSafeS_modify {I : σ → Prop} {P : PUnit → σ → Prop} (g : σ → σ)
    (h : ∀ s, I s → P () (g s)) :
    GuardedSafeS RespOk Q I P (modify g) := fun s hs => by
  rw [StateT.run_modify]
  exact GuardedSafePost.pure (h s hs)

theorem guardedSafeS_modify_true {I : σ → Prop} (g : σ → σ)
    (h : ∀ s, I s → I (g s)) :
    GuardedSafeS RespOk Q I (fun _ s => I s) (modify g) :=
  guardedSafeS_modify g h

theorem guardedSafeS_lift_true {I : σ → Prop} {x : OracleComp spec α}
    (hx : GuardedSafePost RespOk Q (fun _ => True) x) :
    GuardedSafeS RespOk Q I (fun _ s => I s) (StateT.lift x) := fun _s hs =>
  hx.bind fun _ _ => GuardedSafePost.pure hs

theorem guardedSafeS_lift_query {I : σ → Prop} {t : spec.Domain} (hQt : ¬ Q t) :
    GuardedSafeS RespOk Q I (fun a s => RespOk t a ∧ I s)
      (StateT.lift (query (spec := spec) t : OracleComp spec (spec.Range t))) := fun _s hs =>
  (GuardedSafePost.query hQt).bind fun _a ha => GuardedSafePost.pure ⟨ha, hs⟩

theorem guardedSafeS_bind_query {I : σ → Prop} {R : β → σ → Prop}
    {t : spec.Domain} {f : spec.Range t → StateT σ (OracleComp spec) β}
    (hQt : ¬ Q t) (hf : ∀ a, RespOk t a → GuardedSafeS RespOk Q I R (f a)) :
    GuardedSafeS RespOk Q I R
      (StateT.lift (query (spec := spec) t : OracleComp spec (spec.Range t)) >>= f) :=
  guardedSafeS_bind_and (guardedSafeS_lift_query hQt) hf

theorem GuardedSafePost.simulateQ_run
    {RespOk : (t : ι) → spec.Range t → Prop} {p : ι → Prop}
    {RespOk' : (t : ι') → spec'.Range t → Prop} {Q : ι' → Prop} {I : σ → Prop}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {oa : OracleComp spec α}
    (hoa : GuardedSafePost RespOk p (fun _ => True) oa)
    (hstep : ∀ t, ¬ p t → GuardedSafeS RespOk' Q I (fun a s => RespOk t a ∧ I s) (impl t))
    {s : σ} (hs : I s) :
    GuardedSafePost RespOk' Q (fun r => I r.2) ((simulateQ impl oa).run s) := by
  induction hoa generalizing s with
  | pure _ =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact GuardedSafePost.pure hs
  | @query_bind t mx hpt _ ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    have hlift : GuardedSafePost RespOk' Q (fun r => RespOk t r.1 ∧ I r.2)
        ((liftM (impl t) : StateT σ (OracleComp spec') (spec.Range t)).run s) := by
      simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t hpt s hs
    exact hlift.bind fun pu hpu => ih pu.1 hpu.1 hpu.2

end Combinators

end GuardedSafe

namespace Ratchet.LibsignalInst

open LibsignalSession LibsignalAead GuardedSafe

/-- `pqmsg` and every entry of `addrs` have byte length `< 2 ^ 29`. -/
def LibsignalMsgPublicPart.shortB (p : LibsignalMsgPublicPart) : Bool :=
  decide (p.pqmsg.length < 2 ^ 29) && p.addrs.all fun a => decide (a.length < 2 ^ 29)

/-- Every OT-CCA encryption response `some e` has `e.1.1.length + 8 < 2 ^ 32`. -/
def otRespShort {AD M : Type} :
    (t : (unifSpec + AEADScheme.otccaSpec AD M LibsignalCiphertextWithSalt32).Domain) →
      (unifSpec + AEADScheme.otccaSpec AD M LibsignalCiphertextWithSalt32).Range t → Prop
  | .inr (.inl _), r => ∀ e, r = some e → e.1.1.length + 8 < 2 ^ 32
  | _, _ => True

/-- OT-CCA decryption query whose serialized wire `e.1.1` has length `≥ 2 ^ 32`. -/
def otDecLong {AD M : Type} :
    (unifSpec + AEADScheme.otccaSpec AD M LibsignalCiphertextWithSalt32).Domain → Prop
  | .inr (.inr ⟨_, e⟩) => ¬ e.1.1.length < 2 ^ 32
  | _ => False

/-- Under `otRespShort`, `B` never queries decryption on a serialized wire of length `≥ 2 ^ 32`. -/
def GuardedOTDecShort {AD M : Type}
    (B : AEADScheme.OTCCAAdversary AD M LibsignalCiphertextWithSalt32) : Prop :=
  GuardedSafePost otRespShort otDecLong (fun _ => True) B

/-- Every FS-AEAD `transmit` or `challenge` response `some (_, e)` has `e.1.1.length + 8 < 2 ^ 32`. -/
def fsRespShort {SS RS AD Msg : Type} :
    (t : (unifSpec + FSAEAD.spec SS RS AD Msg (ℕ × LibsignalCiphertextWithSalt32)).Domain) →
      (unifSpec + FSAEAD.spec SS RS AD Msg (ℕ × LibsignalCiphertextWithSalt32)).Range t → Prop
  | .inr (.inl (.inl (.inl (.inl (.inl _))))), r =>
      ∀ ie : ℕ × LibsignalCiphertextWithSalt32, r = some ie → ie.2.1.1.length + 8 < 2 ^ 32
  | .inr (.inl (.inl (.inl (.inl (.inr _))))), r =>
      ∀ ie : ℕ × LibsignalCiphertextWithSalt32, r = some ie → ie.2.1.1.length + 8 < 2 ^ 32
  | _, _ => True

/-- FS-AEAD `inject` query whose serialized wire `e.1.1` has length `≥ 2 ^ 32`. -/
def fsInjectLong {SS RS AD Msg : Type} :
    (unifSpec + FSAEAD.spec SS RS AD Msg (ℕ × LibsignalCiphertextWithSalt32)).Domain → Prop
  | .inr (.inr ⟨_, _, e⟩) => ¬ e.1.1.length < 2 ^ 32
  | _ => False

/-- Under `fsRespShort`, `A` never queries `inject` on a serialized wire of length `≥ 2 ^ 32`. -/
def GuardedFSInjectShort {SS RS AD Msg : Type}
    (A : FSAEAD.Adversary SS RS AD Msg (ℕ × LibsignalCiphertextWithSalt32)) : Prop :=
  GuardedSafePost fsRespShort fsInjectLong (fun _ => True) A

end Ratchet.LibsignalInst

end CryptoGames
