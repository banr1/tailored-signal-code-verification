/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHA
import Computational.Proofs.SignalPqxdh.Security.AeadMacInputInj
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH authentication: hybrid (A0) under semantic MAC-input discipline

Establishes Hybrid (A0) under semantic MAC-input discipline (`MacInputDisciplined'`) when primitive
queries are answered deterministically by `P`, and proves that `aeadMuIntReductionAuth` satisfies
this discipline over `goodFirstMsgAD`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

/-! ## Deterministic primitive answers -/

def primAns (P : Primitives) : (op : PrimQuery) → primSpec.Range op
  | .x25519 sk pk          => P.x25519 sk pk
  | .x25519Base sk         => P.x25519Base sk
  | .isCanonical pk        => P.isCanonical pk
  | .pow8 pk               => P.pow8 pk
  | .sigPkGen sk           => P.sigPkGen sk
  | .sigSign sk m r        => P.sigSign sk m r
  | .sigVerify pk m sg     => P.sigVerify pk m sg
  | .kemKeyGen seed        => P.kemKeyGen seed
  | .kemEncaps pk r        => P.kemEncaps pk r
  | .kemDecaps sk ct       => P.kemDecaps sk ct
  | .hkdfDerive96 ikm      => P.hkdfDerive96 ikm
  | .rootCreateChain rk dh => P.rootCreateChain rk dh
  | .chainKdfSeed ck       => P.chainKdfSeed ck
  | .chainKdfNext ck       => P.chainKdfNext ck
  | .spqrInitSend p r      => P.spqrInitSend p r
  | .spqrInitRecv p m      => P.spqrInitRecv p m
  | .deriveMsgKeys m s     => P.deriveMsgKeys m s
  | .aeadEnc mk ad pt      => P.aeadEnc mk ad pt
  | .aeadDec mk ad ct      => P.aeadDec mk ad ct

theorem primImpl_eq_pure (P : Primitives) (op : PrimQuery) :
    primImpl P op = pure (primAns P op) := by
  cases op <;> rfl

/-- Answer primitive queries by `P`; re-issue uniform and AEAD-game queries. -/
def primDetImpl (P : Primitives) : QueryImpl AeadMuIntSimSpec (OracleComp AeadMuIntSimSpec) :=
  fun t => match t with
  | .inl (.inl n) => liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (.inl (.inl n)))
  | .inl (.inr op) => pure (primAns P op)
  | .inr q => liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (.inr q))

/-- Semantic MAC-input discipline: with primitives answered by `P`, `B` never issues a bad-AD
    query. -/
def MacInputDisciplined' (P : Primitives) (Good : Bytes → Bool) (B : AeadMuIntCtxtAdv) : Prop :=
  OracleComp.IsQueryBoundP (simulateQ (primDetImpl P) B.run) (badAdQuery Good) 0

/-- `simulateQ impl` factors through `primDetImpl P` when `impl` answers primitive queries by `P`
    without touching the state. -/
theorem simulateQ_primDet_run {σ : Type} (P : Primitives)
    (impl : QueryImpl AeadMuIntSimSpec (StateT σ ProbComp))
    (hp : ∀ op s, (impl (.inl (.inr op))).run s = pure (primAns P op, s))
    {α : Type} (oa : OracleComp AeadMuIntSimSpec α) :
    ∀ s, (simulateQ impl (simulateQ (primDetImpl P) oa)).run s = (simulateQ impl oa).run s := by
  have hstep : ∀ t s, (simulateQ impl (primDetImpl P t)).run s = (impl t).run s := by
    intro t s
    rcases t with (n | op) | q
    · simp [primDetImpl]
    · simp [primDetImpl, hp]
    · simp [primDetImpl]
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; simp
  | query_bind t k ih =>
    intro s
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, hstep, ih]

/-! ## Hybrid (A0) under the semantic discipline -/

def primDetAdv (P : Primitives) (B : AeadMuIntCtxtAdv) : AeadMuIntCtxtAdv :=
  { B with run := simulateQ (primDetImpl P) B.run }

theorem aeadMuIntCtxt_primDetAdv (P : Primitives) (B : AeadMuIntCtxtAdv) :
    AeadMuIntCtxt P (primDetAdv P B) = AeadMuIntCtxt P B := by
  unfold AeadMuIntCtxt
  rw [ha_exp_eq, ha_exp_eq]
  simp only [primDetAdv]
  rw [simulateQ_primDet_run P (haMuFull P)
    (fun op s => by simp [haMuFull, primBaseImpl, primImpl_eq_pure]) B.run _]

theorem gProb_congr_run (P : Primitives) (b : Bool) (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (B B' : AeadMuIntCtxtAdv)
    (h : ∀ k s, (simulateQ (gOuter P (prfEvalImpl P b k) defer tag) B'.run).run s =
      (simulateQ (gOuter P (prfEvalImpl P b k) defer tag) B.run).run s) :
    gProb P b defer tag B' = gProb P b defer tag B := by
  unfold gProb
  congr 3
  refine bind_congr fun k => ?_
  have hfull : prfFullImpl P b k = gFull P (prfEvalImpl P b k) := rfl
  unfold gAfter
  rw [hfull, simulateQ_bind, StateT.run_bind, simulateQ_gRun, h, simulateQ_bind,
    StateT.run_bind, simulateQ_gRun]

theorem gProb_primDetAdv (P : Primitives) (b : Bool) (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) (B : AeadMuIntCtxtAdv) :
    gProb P b defer tag (primDetAdv P B) = gProb P b defer tag B :=
  gProb_congr_run P b defer tag B _ (fun k s =>
    simulateQ_primDet_run P _ (fun op s => by simp [gOuter, primBaseImpl, primImpl_eq_pure])
      B.run s)

/-- Bounds multi-key INT-CTXT advantage by the all-real hybrid under `MacInputDisciplined'`. -/
theorem aeadMuIntCtxt_le_gProb_allReal' (P : Primitives) (hP : WellFormedPrimitivesδ P)
    (B : AeadMuIntCtxtAdv) (Good : Bytes → Bool) (hGood : MacAdGood Good)
    (hGG : ∀ ad, Good ad = true → goodFirstMsgAD ad = true)
    (hDisc : MacInputDisciplined' P Good B) :
    AeadMuIntCtxt P B ≤ gProb P false (fun _ => False) unifTag B := by
  rw [← aeadMuIntCtxt_primDetAdv, ← gProb_primDetAdv P false (fun _ => False) unifTag B]
  exact aeadMuIntCtxt_le_gProb_allReal P hP (primDetAdv P B) Good hGood hGG hDisc

/-! ## Good associated data: first-message ADs over 32-byte keys -/

theorem goodFirstMsgAD_of (a b e pq : Bytes) (ha : a.length = 32) (hb : b.length = 32)
    (he : e.length = 32) : goodFirstMsgAD (firstMsgAD a b e pq) = true :=
  (goodFirstMsgAD_iff _).2 ⟨a, b, e, pq, ha, hb, he, rfl⟩

theorem macAdGood_goodFirstMsgAD : MacAdGood goodFirstMsgAD := by
  intro ad ad' body body' h h' hx
  obtain ⟨a, b, e, pq, ha, hb, he, rfl⟩ := (goodFirstMsgAD_iff _).1 h
  obtain ⟨a', b', e', pq', ha', hb', he', rfl⟩ := (goodFirstMsgAD_iff _).1 h'
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    aeadMacInput_firstMsgAD_inj a b e pq body a' b' e' pq' body' ha hb he ha' hb' he' hx
  subst h1 h2 h3 h4 h5
  exact ⟨rfl, rfl⟩

/-! ## Support calculus for `PrimBaseSpec` computations under the real `P` -/

section PW

variable (P : Primitives)

def PW {α : Type} (oa : OracleComp PrimBaseSpec α) (Q : α → Prop) : Prop :=
  ∀ x ∈ support (simulateQ (primBaseImpl P) oa), Q x

theorem pw_pure {α : Type} (a : α) (Q : α → Prop) (h : Q a) : PW P (pure a) Q := by
  intro x hx
  simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hx
  subst hx; exact h

theorem pw_bind {α β : Type} (oa : OracleComp PrimBaseSpec α) (f : α → OracleComp PrimBaseSpec β)
    (R : α → Prop) (Q : β → Prop) (h1 : PW P oa R) (h2 : ∀ a, R a → PW P (f a) Q) :
    PW P (oa >>= f) Q := by
  intro x hx
  simp only [simulateQ_bind, mem_support_bind_iff] at hx
  obtain ⟨a, ha, hx⟩ := hx
  exact h2 a (h1 a ha) x hx

theorem pw_bind_any {α β : Type} (oa : OracleComp PrimBaseSpec α)
    (f : α → OracleComp PrimBaseSpec β) (Q : β → Prop) (h2 : ∀ a, PW P (f a) Q) :
    PW P (oa >>= f) Q :=
  pw_bind P oa f (fun _ => True) Q (fun _ _ => trivial) (fun a _ => h2 a)

theorem pw_primQ_bind {β : Type} (op : PrimQuery) (f : primSpec.Range op → OracleComp PrimBaseSpec β)
    (Q : β → Prop) (h : PW P (f (primAns P op)) Q) : PW P (primQ op >>= f) Q := by
  intro x hx
  simp only [simulateQ_bind, simulateQ_primQ, primImpl_eq_pure, pure_bind] at hx
  exact h x hx

theorem pw_mono {α : Type} (oa : OracleComp PrimBaseSpec α) (Q Q' : α → Prop)
    (h : PW P oa Q) (hQ : ∀ a, Q a → Q' a) : PW P oa Q' :=
  fun x hx => hQ x (h x hx)

theorem pw_ite {α : Type} (c : Prop) [Decidable c] (oa ob : OracleComp PrimBaseSpec α)
    (Q : α → Prop) (h1 : c → PW P oa Q) (h2 : ¬ c → PW P ob Q) :
    PW P (if c then oa else ob) Q := by
  split_ifs with hc
  · exact h1 hc
  · exact h2 hc

theorem pw_findMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (R : α → Prop)
    (hp : ∀ a, PW P (p a) (fun b => b = true → R a)) :
    ∀ L : List α, PW P (findMPrim p L) (fun r => ∀ a, r = some a → a ∈ L ∧ R a)
  | [] => by
    unfold findMPrim
    exact pw_pure P _ _ (fun a h => by cases h)
  | x :: xs => by
    unfold findMPrim
    refine pw_bind P _ _ _ _ (hp x) (fun b hb => ?_)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact pw_mono P _ _ _ (pw_findMPrim p R hp xs)
        (fun r h a ha => ⟨List.mem_cons_of_mem _ (h a ha).1, (h a ha).2⟩)
    · simp only [↓reduceIte]
      exact pw_pure P _ _ (fun a ha => by
        cases ha; exact ⟨List.mem_cons_self, hb rfl⟩)

theorem pw_findHonestPrincipalPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (ikB : Bytes) :
    PW P (findHonestPrincipalPrim S principals ikB) (fun r => ∀ a, r = some a →
      a ∈ principals ∧ P.pow8 ikB = P.pow8 a.2.ikAPk) := by
  unfold findHonestPrincipalPrim
  refine pw_mono P _ _ _ (pw_findMPrim P _ (fun a => P.pow8 ikB = P.pow8 a.2.ikAPk) ?_ _) ?_
  · intro a
    refine pw_primQ_bind P _ _ _ (pw_primQ_bind P _ _ _ (pw_pure P _ _ ?_))
    intro h
    simpa [primAns] using h
  · intro r h a ha
    exact ⟨List.mem_of_mem_take (h a ha).1, (h a ha).2⟩

end PW

/-! ## Discipline calculus for `AeadMuIntSimSpec` computations -/

section MuOK

variable (P : Primitives)

/-- No bad-AD (non-`goodFirstMsgAD`) game query once primitives are answered by `P`, and every
    output satisfies `Q`. -/
def MuOK {α : Type} (oa : OracleComp AeadMuIntSimSpec α) (Q : α → Prop) : Prop :=
  IsQueryBoundP (simulateQ (primDetImpl P) oa) (badAdQuery goodFirstMsgAD) 0 ∧
    ∀ x ∈ support (simulateQ (primDetImpl P) oa), Q x

theorem muOK_pure {α : Type} (a : α) (Q : α → Prop) (h : Q a) : MuOK P (pure a) Q := by
  refine ⟨by simp, fun x hx => ?_⟩
  simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hx
  subst hx; exact h

theorem muOK_bind {α β : Type} (oa : OracleComp AeadMuIntSimSpec α)
    (f : α → OracleComp AeadMuIntSimSpec β)
    (R : α → Prop) (Q : β → Prop) (h1 : MuOK P oa R) (h2 : ∀ a, R a → MuOK P (f a) Q) :
    MuOK P (oa >>= f) Q := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [simulateQ_bind]
    exact isQueryBoundP_bind h1.1 (fun a ha => (h2 a (h1.2 a ha)).1)
  · simp only [simulateQ_bind, mem_support_bind_iff] at hx
    obtain ⟨a, ha, hx⟩ := hx
    exact (h2 a (h1.2 a ha)).2 x hx

theorem muOK_embedPrimMu {α : Type} (oa : OracleComp PrimBaseSpec α) (Q : α → Prop)
    (h : PW P oa Q) : MuOK P (embedPrimMu oa) Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact muOK_pure P a Q (h a (by simp))
  | query_bind t k ih =>
    unfold embedPrimMu
    rw [embedPrim_query_bind]
    rcases t with n | op
    · have hk : ∀ u, PW P (k u) Q := fun u x hx => h x (by
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, mem_support_bind_iff]
        exact ⟨u, by simp [primBaseImpl], hx⟩)
      refine muOK_bind P _ _ (fun _ => True) Q ⟨?_, fun _ _ => trivial⟩ (fun u _ => ih u (hk u))
      simp [primDetImpl, badAdQuery]
    · have hk : PW P (k (primAns P op)) Q := fun x hx => h x (by
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map]
        simpa [primBaseImpl, primImpl_eq_pure] using hx)
      have := ih (primAns P op) hk
      unfold embedPrimMu at this
      refine ⟨?_, fun x hx => ?_⟩
      · simpa [simulateQ_bind, primDetImpl] using this.1
      · exact this.2 x (by simpa [simulateQ_bind, primDetImpl] using hx)

theorem muOK_bind_any {α β : Type} (oa : OracleComp AeadMuIntSimSpec α)
    (f : α → OracleComp AeadMuIntSimSpec β) (Q : β → Prop)
    (h1 : MuOK P oa (fun _ => True)) (h2 : ∀ a, MuOK P (f a) Q) : MuOK P (oa >>= f) Q :=
  muOK_bind P oa f _ Q h1 (fun a _ => h2 a)

theorem muOK_ite {α : Type} (c : Prop) [Decidable c] (oa ob : OracleComp AeadMuIntSimSpec α)
    (Q : α → Prop) (h1 : c → MuOK P oa Q) (h2 : ¬ c → MuOK P ob Q) :
    MuOK P (if c then oa else ob) Q := by
  split_ifs with hc
  · exact h1 hc
  · exact h2 hc

theorem muOK_encOnceMuQ (i : Nat) (ad pt : Bytes) (hg : goodFirstMsgAD ad = true) :
    MuOK P (encOnceMuQ i ad pt) (fun _ => True) := by
  refine ⟨?_, fun _ _ => trivial⟩
  simp [encOnceMuQ, primDetImpl, badAdQuery, hg]

theorem muOK_tryForgeMuQ (i : Nat) (ad ct : Bytes) (hg : goodFirstMsgAD ad = true) :
    MuOK P (tryForgeMuQ i ad ct) (fun _ => True) := by
  refine ⟨?_, fun _ _ => trivial⟩
  simp [tryForgeMuQ, primDetImpl, badAdQuery, hg]

theorem muOK_primMuQ (op : PrimQuery) : MuOK P (primMuQ op) (fun _ => True) :=
  muOK_embedPrimMu P _ _ (fun _ _ => trivial)

end MuOK

/-! ## The reduction is disciplined -/

section Reduction

variable (P : Primitives)

def PrinInv {S : Setup} (hst : AuthHybridStateFixed S) : Prop :=
  ∀ e ∈ hst.toAuthHybridState.base.principals, ∃ sk, e.2.ikAPk = P.x25519Base sk

theorem pw_prepAuthIntSendPrim (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (S : Setup) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hInv : PrinInv P hst) :
    PW P (prepAuthIntSendPrim S sid u bundle m0 m1 hst)
      (fun r => ∀ p, r = some p → p.isIdealSend = true → goodFirstMsgAD p.ad = true) := by
  unfold prepAuthIntSendPrim
  dsimp only
  refine pw_ite P _ _ _ _ (fun _ => pw_pure P _ _ (by simp)) (fun _ => ?_)
  refine pw_ite P _ _ _ _ (fun _ => pw_pure P _ _ (by simp)) (fun _ => ?_)
  split
  · rename_i uEntry hu
    have hA : uEntry.ikAPk.length = 32 := by
      obtain ⟨sk, hsk⟩ := hInv _ (List.mem_of_find?_eq_some hu)
      rw [hsk]; exact hP.x25519Base_len sk
    refine pw_bind P _ _ _ _ (pw_findHonestPrincipalPrim P S _ bundle.ikB) (fun peer hpeer => ?_)
    have hB : peer.isSome = true → bundle.ikB.length = 32 := by
      intro h
      obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨hm, hpw⟩ := hpeer a rfl
      obtain ⟨sk, hsk⟩ := hInv a hm
      exact hLaw _ sk (hsk ▸ hpw)
    repeat' (first
      | ((with_reducible refine pw_pure P _ _ ?_); simp; done)
      | ((with_reducible refine pw_pure P _ _ ?_); intro p hp hI; cases hp
         have hs : peer.isSome = true := by revert hI; cases peer <;> simp
         exact goodFirstMsgAD_of _ _ _ _ hA (hB hs) (hP.x25519Base_len _))
      | with_reducible refine pw_ite P _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      | (with_reducible refine pw_primQ_bind P _ _ _ ?_)
      | with_reducible refine pw_bind_any P _ _ _ (fun _ => ?_)
      | split)
  · exact pw_pure P _ _ (by simp)

def RecvPrepOK {S : Setup} (hst : AuthHybridStateFixed S) (msg : PreKeyMsg)
    (r : Option (AuthIntRecvPrep S)) : Prop :=
  ∀ prep, r = some prep →
    (∃ sk, prep.kEntry.ikAPk = P.x25519Base sk) ∧ msg.hdr.ikAPk.length = 32 ∧
      msg.ephAPk.length = 32 ∧
      ∀ res?, (prep.finish res?).2.base.principals = hst.toAuthHybridState.base.principals

theorem pw_finishPrepareAuthRecvPrim (S : Setup) (kVal jVal : Nat)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkSk? opkPk? : Option Bytes)
    (mkFinish : List (Nat × UInt32 × UInt32 × Bytes) → Bool → AuthHybridState S →
      Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) → AuthResponse × AuthHybridState S)
    (msg : PreKeyMsg) (hst : AuthHybridState S) (R : AuthIntRecvPrep S → Prop)
    (hR : ∀ prep : AuthIntRecvPrep S, prep.kEntry = kEntry → prep.hstDec.base = hst.base →
      (∃ (u : List (Nat × UInt32 × UInt32 × Bytes)) (b : Bool),
        prep.finish = mkFinish u b prep.hstDec) → R prep) :
    PW P (finishPrepareAuthRecvPrim S kVal jVal kEntry bEntry opkSk? opkPk? mkFinish msg hst)
      (fun r => ∀ prep, r = some prep → R prep) := by
  unfold finishPrepareAuthRecvPrim
  dsimp only
  repeat' (first
      | ((with_reducible refine pw_pure P _ _ ?_); simp; done)
      | ((with_reducible refine pw_pure P _ _ ?_); intro p hp; cases hp
         exact hR _ rfl rfl ⟨_, _, rfl⟩)
      | with_reducible refine pw_ite P _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      | (with_reducible refine pw_primQ_bind P _ _ _ ?_)
      | with_reducible refine pw_bind_any P _ _ _ (fun _ => ?_)
      | split)

theorem finishErasedRecvOPK_principals {S : Setup} (k : Fin S.N_id) (j : Fin S.N_recv)
    (o : Fin S.N_opk) (u : List (Nat × KeyId × KeyId × Bytes)) (b : Bool) (h : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes)
        × (Bytes × Bytes)))) :
    (finishErasedRecvOPK k j o u b h res?).2.base.principals = h.base.principals := by
  unfold finishErasedRecvOPK
  rcases res? with _ | ⟨_, _, _, _, _, _⟩
  · rfl
  · dsimp only; split_ifs <;> rfl

theorem finishErasedRecvNoOPK_principals {S : Setup} (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk) (u : List (Nat × KeyId × KeyId × Bytes)) (b : Bool)
    (h : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes)
        × (Bytes × Bytes)))) :
    (finishErasedRecvNoOPK k j l u b h res?).2.base.principals = h.base.principals := by
  unfold finishErasedRecvNoOPK
  rcases res? with _ | ⟨_, _, _, _, _, _⟩
  · rfl
  · dsimp only; split_ifs <;> rfl

theorem pw_prepareAuthRecvOPKPrim (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv)
    (o : Fin S.N_opk) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S) (hInv : PrinInv P hst) :
    PW P (prepareAuthRecvOPKPrim S k j o msg hst.toAuthHybridState) (RecvPrepOK P hst msg) := by
  unfold prepareAuthRecvOPKPrim
  dsimp only
  refine pw_ite P _ _ _ _ (fun _ => pw_pure P _ _ (by simp [RecvPrepOK])) (fun hc => ?_)
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hc
  refine pw_ite P _ _ _ _ (fun _ => pw_pure P _ _ (by simp [RecvPrepOK])) (fun _ => ?_)
  refine pw_bind_any P _ _ _ (fun _ => ?_)
  refine pw_ite P _ _ _ _ (fun _ => pw_pure P _ _ (by simp [RecvPrepOK])) (fun _ => ?_)
  split
  · rename_i kE _ _ hk _ _
    refine pw_ite P _ _ _ _ (fun _ => pw_pure P _ _ (by simp [RecvPrepOK])) (fun _ => ?_)
    refine pw_finishPrepareAuthRecvPrim P S _ _ _ _ _ _ _ msg _ _ ?_
    rintro prep hk' hb ⟨u, b, hf⟩
    refine ⟨?_, ?_, ?_, fun res? => ?_⟩
    · rw [hk']; exact hInv _ (List.mem_of_find?_eq_some hk)
    · exact hc.1.1.2
    · exact hc.2
    · rw [hf, finishErasedRecvOPK_principals, hb]
  · exact pw_pure P _ _ (by simp [RecvPrepOK])

theorem pw_prepareAuthRecvNoOPKPrim (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S) (hInv : PrinInv P hst) :
    PW P (prepareAuthRecvNoOPKPrim S k j l msg hst.toAuthHybridState) (RecvPrepOK P hst msg) := by
  unfold prepareAuthRecvNoOPKPrim
  dsimp only
  refine pw_ite P _ _ _ _ (fun _ => pw_pure P _ _ (by simp [RecvPrepOK])) (fun hc => ?_)
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hc
  refine pw_ite P _ _ _ _ (fun _ => pw_pure P _ _ (by simp [RecvPrepOK])) (fun _ => ?_)
  refine pw_bind_any P _ _ _ (fun _ => ?_)
  refine pw_ite P _ _ _ _ (fun _ => pw_pure P _ _ (by simp [RecvPrepOK])) (fun _ => ?_)
  split
  · rename_i kE _ hk _
    refine pw_finishPrepareAuthRecvPrim P S _ _ _ _ _ _ _ msg _ _ ?_
    rintro prep hk' hb ⟨u, b, hf⟩
    refine ⟨?_, ?_, ?_, fun res? => ?_⟩
    · rw [hk']; exact hInv _ (List.mem_of_find?_eq_some hk)
    · exact hc.1.1.2
    · exact hc.2
    · rw [hf, finishErasedRecvNoOPK_principals, hb]
  · exact pw_pure P _ _ (by simp [RecvPrepOK])

theorem pw_stepAuthOtherPrim (S : Setup) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hInv : PrinInv P hst) :
    PW P (stepAuthOtherPrim true S q hst) (fun p => PrinInv P p.2) := by
  unfold stepAuthOtherPrim
  dsimp only
  cases q
  all_goals
    repeat' (first
      | ((with_reducible refine pw_pure P _ _ ?_); exact hInv)
      | (with_reducible refine pw_pure P _ _ ?_)
      | with_reducible refine pw_ite P _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      | (with_reducible refine pw_primQ_bind P _ _ _ ?_)
      | with_reducible refine pw_bind_any P _ _ _ (fun _ => ?_)
      | split)
  all_goals
    intro e he
    simp only [List.mem_cons, List.mem_map] at he
    first
      | (rcases he with rfl | he
         · exact ⟨_, rfl⟩
         · exact hInv e he)
      | (obtain ⟨e0, he0, rfl⟩ := he
         obtain ⟨sk, hsk⟩ := hInv e0 he0
         exact ⟨sk, by split_ifs <;> exact hsk⟩)

theorem muOK_finishAuthRecvScheduleMuPrim {S : Setup} (kEntry : PrincipalEntry) (msg : PreKeyMsg)
    (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S) (sp : AuthIntRecvSchedPrep S)
    (hg : goodFirstMsgAD (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg)
      = true) :
    MuOK P (finishAuthRecvScheduleMuPrim kEntry msg recvCount mkSaltCache sp) (fun _ => True) := by
  unfold finishAuthRecvScheduleMuPrim
  dsimp only
  repeat' (first
    | ((with_reducible refine muOK_pure P _ _ ?_); trivial)
    | with_reducible refine muOK_ite P _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    | with_reducible refine muOK_bind_any P _ _ _ (muOK_tryForgeMuQ P _ _ _ hg) (fun _ => ?_)
    | with_reducible refine muOK_bind_any P _ _ _ (muOK_primMuQ P _) (fun _ => ?_)
    | split)

theorem muOK_evalAuthRecvScheduleMuPrim (S : Setup)
    (hstDec : AuthHybridState S) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes)
    (secrets : Bytes) (msg : PreKeyMsg)
    (hg : goodFirstMsgAD (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg)
      = true) :
    MuOK P (evalAuthRecvScheduleMuPrim S hstDec recvCount mkSaltCache kEntry bEntry opkPk? secrets
      msg) (fun _ => True) := by
  unfold evalAuthRecvScheduleMuPrim
  refine muOK_bind_any P _ _ _ (muOK_embedPrimMu P _ _ (fun _ _ => trivial)) (fun r => ?_)
  split
  · exact muOK_finishAuthRecvScheduleMuPrim P _ _ _ _ _ hg
  · exact muOK_pure P _ _ trivial

theorem muOK_runAuthSendMuPrim (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (S : Setup) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hInv : PrinInv P hst) :
    MuOK P (runAuthSendMuPrim S sid u bundle m0 m1 hst) (fun p => PrinInv P p.2) := by
  unfold runAuthSendMuPrim
  refine muOK_bind P _ _ _ _ (muOK_embedPrimMu P _ _
    (pw_prepAuthIntSendPrim P hP hLaw S sid u bundle m0 m1 hst hInv)) (fun r hr => ?_)
  split
  · rename_i p
    refine muOK_bind_any P _ _ _ ?_ (fun _ => muOK_pure P _ _ hInv)
    refine muOK_ite P _ _ _ _ (fun hI => ?_) (fun _ => ?_)
    · exact muOK_bind_any P _ _ _ (muOK_encOnceMuQ P _ _ _ (hr p rfl hI))
        (fun _ => muOK_pure P _ _ trivial)
    · exact muOK_bind_any P _ _ _ (muOK_primMuQ P _) (fun _ =>
        muOK_bind_any P _ _ _ (muOK_primMuQ P _) (fun _ => muOK_pure P _ _ trivial))
  · exact muOK_pure P _ _ hInv

theorem muOK_recv (S : Setup) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S)
    (hInv : PrinInv P hst) (prepC : OracleComp PrimBaseSpec (Option (AuthIntRecvPrep S)))
    (hprep : PW P prepC (RecvPrepOK P hst msg)) (hP : WellFormedPrimitivesδ P) :
    MuOK P (do
      let some prep ← embedPrimMu prepC
        | return (AuthResponse.noneResp, { hst with recvCount := hst.recvCount + 1 })
      let (res?, mkSaltCache') ←
        evalAuthRecvScheduleMuPrim S prep.hstDec
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
      let (resp, hst') := prep.finish res?
      return (resp, ({
        toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache := mkSaltCache' } :
          AuthHybridStateFixed S))) (fun p => PrinInv P p.2) := by
  refine muOK_bind P _ _ _ _ (muOK_embedPrimMu P _ _ hprep) (fun r hr => ?_)
  split
  · rename_i prep
    obtain ⟨⟨sk, hsk⟩, hA, hE, hfin⟩ := hr prep rfl
    have hg : goodFirstMsgAD (firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk
        msg.pqRatchetMsg) = true :=
      goodFirstMsgAD_of _ _ _ _ hA (by rw [hsk]; exact hP.x25519Base_len sk) hE
    refine muOK_bind_any P _ _ _ (muOK_evalAuthRecvScheduleMuPrim P _ _ _ _ _ _ _ _ _ hg)
      (fun z => ?_)
    rcases z with ⟨res?, c⟩
    dsimp only
    refine muOK_pure P _ _ ?_
    intro e he
    exact hInv e (by simpa [hfin res?] using he)
  · exact muOK_pure P _ _ hInv

theorem muOK_stepAuthMuPrim (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (S : Setup) (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hInv : PrinInv P hst) :
    MuOK P (stepAuthMuPrim S q hst) (fun p => PrinInv P p.2) := by
  unfold stepAuthMuPrim
  split
  · exact muOK_ite P _ _ _ _ (fun _ => muOK_pure P _ _ hInv)
      (fun _ => muOK_runAuthSendMuPrim P hP hLaw S _ _ _ _ _ hst hInv)
  · exact muOK_ite P _ _ _ _ (fun _ => muOK_pure P _ _ hInv)
      (fun _ => muOK_runAuthSendMuPrim P hP hLaw S _ _ _ _ _ hst hInv)
  · exact muOK_recv P S _ hst hInv _ (pw_prepareAuthRecvOPKPrim P S _ _ _ _ hst hInv) hP
  · exact muOK_recv P S _ hst hInv _ (pw_prepareAuthRecvNoOPKPrim P S _ _ _ _ hst hInv) hP
  · exact muOK_embedPrimMu P _ _ (pw_stepAuthOtherPrim P S _ hst hInv)

theorem muOK_runWithMuStep (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (S : Setup) {α : Type} (oa : OracleComp (unifSpec + authSpec S) α) :
    ∀ hst : AuthHybridStateFixed S, PrinInv P hst →
      MuOK P (runWithMuStep (stepAuthMuPrim S) oa hst) (fun _ => True) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro hst _; exact muOK_pure P _ _ trivial
  | query_bind t k ih =>
    intro hst hInv
    rcases t with n | gq
    · rw [runWithMuStep_query_inl]
      refine muOK_bind_any P _ _ _ ⟨?_, fun _ _ => trivial⟩ (fun u => ih u hst hInv)
      simp [primDetImpl, badAdQuery]
    · rw [runWithMuStep_query_inr]
      exact muOK_bind P _ _ _ _ (muOK_stepAuthMuPrim P hP hLaw S gq hst hInv)
        (fun p hp => ih p.1 p.2 hp)

end Reduction

/-- The `Auth` multi-key INT-CTXT reduction is semantically MAC-input disciplined under `P`. -/
theorem aeadMuIntReductionAuth_disciplined (S : Setup) (P : Primitives)
    (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    MacInputDisciplined' P goodFirstMsgAD (aeadMuIntReductionAuth S b A) := by
  unfold MacInputDisciplined' aeadMuIntReductionAuth aeadMuIntReductionAuthRun unifMu
  dsimp only
  have hInv : ∀ secb : Bool, PrinInv P (AuthHybridStateFixed.empty S secb) := by
    intro secb e he
    simp [AuthHybridStateFixed.empty, AuthHybridState.empty, AuthState.empty] at he
  have hstep : ∀ secb : Bool, MuOK P
      (runWithMuStep (stepAuthMuPrim S) A.1.run (AuthHybridStateFixed.empty S secb) >>=
        fun _ => (pure () : OracleComp AeadMuIntSimSpec Unit)) (fun _ => True) :=
    fun secb => muOK_bind_any P _ _ (fun _ => True)
      (muOK_runWithMuStep P hP hLaw S _ _ (hInv secb)) (fun _ => muOK_pure P _ _ trivial)
  exact (muOK_bind_any P _ _ (fun _ => True)
    (muOK_embedPrimMu P _ (fun _ => True) (fun _ _ => trivial)) hstep).1



end SignalPqxdh.Security
