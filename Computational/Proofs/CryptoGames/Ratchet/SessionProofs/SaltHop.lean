/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.WireHop
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.CryptoGames.FSAEAD.CellForgery
import Computational.Proofs.CryptoGames.FSAEAD.HybridOT
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Proof of the salt hop `lAeadR_otcca`

**Checked by Lean.** Proves `lAeadR_otcca` (DEV-LS25) by showing that the real-PRF branch of `lSaltRed` matches `otccaGameAdIdeal lIdeal` for `lAeadR`, together with multi-slot salt-PRF and MAC-forgery hybrid bounds.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.SaltHop

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD

variable {Pt : Type} [DecidableEq Pt]

abbrev AD (Pt : Type) := ℕ × (Header Pt × LibsignalMsgPublicPart)
abbrev Ct := LibsignalCiphertextWithSalt32
abbrev ChalState (Pt : Type) := Option (AD Pt × Ct)
abbrev AState (Pt : Type) := OTCCAState (BitVec 256) (AD Pt) Ct
abbrev PState := PRFState (BitVec 256) Salt32 DerivedMessageKeys

def aImpl (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :
    QueryImpl (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct) (StateT (AState Pt) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AState Pt) ProbComp)
    + ((lAeadR C codec ℓ encT idOf).otccaEncryptAdIdeal (lIdeal C codec ℓ encT)
      + (lAeadR C codec ℓ encT idOf).otccaDecrypt)

def pImpl (F : ShaState → List (BitVec 8) → ShaState) :
    QueryImpl (unifSpec + prfSpec Salt32 DerivedMessageKeys) (StateT PState ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT PState ProbComp)
    + prfEval (lSaltPRF32 F)

def saltRedImpl (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) :
    QueryImpl (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct)
      (StateT (ChalState Pt) (OracleComp (unifSpec + prfSpec Salt32 DerivedMessageKeys))) :=
  let ae := lAeadK C codec ℓ encT idOf
  fun q => match q with
  | .inl n => StateT.lift (query (spec := unifSpec + prfSpec Salt32 DerivedMessageKeys) (.inl n))
  | .inr (.inl ⟨a, m⟩) => do
    if (← get).isSome then return none
    let mk ← StateT.lift (evalQuery (Input := Salt32) (Tag := DerivedMessageKeys) a.2.2.salt)
    let e ← if b then StateT.lift (liftM (lIdeal C codec ℓ encT a))
      else pure (ae.enc mk ((a.1, a.2.1), a.2.2) m)
    set (some (a, e))
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if b || (← get) == some (a, e) || e.2 ≠ a.2.2.salt then return none
    let mk ← StateT.lift (evalQuery (Input := Salt32) (Tag := DerivedMessageKeys) a.2.2.salt)
    return ae.dec mk ((a.1, a.2.1), a.2.2) e

def runSaltRed (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    {α : Type} (oa : OracleComp (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct) α)
    (chal : ChalState Pt) (pst : PState) :
    ProbComp ((α × ChalState Pt) × PState) :=
  (simulateQ (pImpl C.F) ((simulateQ (saltRedImpl C codec ℓ encT idOf b) oa).run chal)).run pst

@[local simp] theorem simulateQ_pImpl_liftM_run (F : ShaState → List (BitVec 8) → ShaState)
    {α : Type} (oa : ProbComp α) (pst : PState) :
    (simulateQ (pImpl F)
      (liftM oa : OracleComp (unifSpec + prfSpec Salt32 DerivedMessageKeys) α)).run pst =
      oa >>= fun a => pure (a, pst) := by
  simp [pImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

@[local simp] theorem simulateQ_pImpl_evalQuery_false (F : ShaState → List (BitVec 8) → ShaState)
    (salt : Salt32) (key : BitVec 256) (tbl : List (Salt32 × DerivedMessageKeys)) :
    (simulateQ (pImpl F) (evalQuery (Input := Salt32) (Tag := DerivedMessageKeys) salt)).run
      { key := key, b := false, table := tbl } =
      pure (deriveMessageKeys F salt (keyToBytes32 key), { key := key, b := false, table := tbl }) := by
  simp [pImpl, evalQuery, prfEval, lSaltPRF32]

theorem runSaltRed_pure (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    {α : Type} (x : α) (chal : ChalState Pt) (pst : PState) :
    runSaltRed C codec ℓ encT idOf b (pure x) chal pst = pure ((x, chal), pst) := by
  simp [runSaltRed]

theorem runSaltRed_query_bind (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    {α : Type} (q : (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct).Domain)
    (k : (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct).Range q →
      OracleComp (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct) α)
    (chal : ChalState Pt) (pst : PState) :
    runSaltRed C codec ℓ encT idOf b (liftM (OracleSpec.query q) >>= k) chal pst =
      (simulateQ (pImpl C.F) ((saltRedImpl C codec ℓ encT idOf b q).run chal)).run pst >>= fun r =>
        runSaltRed C codec ℓ encT idOf b (k r.1.1) r.1.2 r.2 := by
  simp [runSaltRed, simulateQ_bind, simulateQ_query]

theorem aImpl_query_bind (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {α : Type} (q : (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct).Domain)
    (k : (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct).Range q →
      OracleComp (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct) α)
    (ast : AState Pt) :
    (simulateQ (aImpl C codec ℓ encT idOf) (liftM (OracleSpec.query q) >>= k)).run ast =
      (aImpl C codec ℓ encT idOf q).run ast >>= fun r =>
        (simulateQ (aImpl C codec ℓ encT idOf) (k r.1)).run r.2 := by
  simp [simulateQ_bind, simulateQ_query]

theorem step_inl (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    (n : ℕ) (chal : ChalState Pt) (pst : PState) :
    (simulateQ (pImpl C.F) ((saltRedImpl C codec ℓ encT idOf b (.inl n)).run chal)).run pst =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure ((u, chal), pst) := by
  simp [saltRedImpl, pImpl]

theorem aImpl_step_inl (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (n : ℕ) (ast : AState Pt) :
    (aImpl C codec ℓ encT idOf (.inl n)).run ast =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, ast) := by
  simp [aImpl]

theorem step_enc_some (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) (key : BitVec 256)
    (a a₀ : AD Pt) (m : Plain ℓ) (e₀ : Ct) :
    (simulateQ (pImpl C.F)
      ((saltRedImpl C codec ℓ encT idOf b (.inr (.inl (a, m)))).run (some (a₀, e₀)))).run
        { key := key, b := false, table := [] } =
      pure ((none, some (a₀, e₀)), { key := key, b := false, table := [] }) ∧
    (aImpl C codec ℓ encT idOf (.inr (.inl (a, m)))).run
      { key := key, b := b, chal := some (a₀, e₀) } =
      pure (none, { key := key, b := b, chal := some (a₀, e₀) }) := by
  refine ⟨?_, ?_⟩
  · simp [saltRedImpl]
  · simp [aImpl, otccaEncryptAdIdeal]

theorem step_enc_none_false (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (key : BitVec 256)
    (a : AD Pt) (m : Plain ℓ) :
    let e := (lAeadR C codec ℓ encT idOf).enc key a m
    (simulateQ (pImpl C.F)
      ((saltRedImpl C codec ℓ encT idOf false (.inr (.inl (a, m)))).run none)).run
        { key := key, b := false, table := [] } =
      pure ((some e, some (a, e)), { key := key, b := false, table := [] }) ∧
    (aImpl C codec ℓ encT idOf (.inr (.inl (a, m)))).run
      { key := key, b := false, chal := none } =
      pure (some e, { key := key, b := false, chal := some (a, e) }) := by
  refine ⟨?_, ?_⟩
  · simp [saltRedImpl, lAeadR, lAead]
  · simp [aImpl, otccaEncryptAdIdeal]

theorem step_enc_none_true (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (key : BitVec 256)
    (a : AD Pt) (m : Plain ℓ) :
    (simulateQ (pImpl C.F)
      ((saltRedImpl C codec ℓ encT idOf true (.inr (.inl (a, m)))).run none)).run
        { key := key, b := false, table := [] } =
      (lIdeal C codec ℓ encT a >>= fun e =>
        pure ((some e, some (a, e)), { key := key, b := false, table := [] })) ∧
    (aImpl C codec ℓ encT idOf (.inr (.inl (a, m)))).run
      { key := key, b := true, chal := none } =
      (lIdeal C codec ℓ encT a >>= fun e =>
        pure (some e, { key := key, b := true, chal := some (a, e) })) := by
  refine ⟨?_, ?_⟩
  · simp [saltRedImpl]
  · simp [aImpl, otccaEncryptAdIdeal]

theorem step_dec (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) (key : BitVec 256)
    (a : AD Pt) (e : Ct) (chal : ChalState Pt) :
    ∃ res : Option (Plain ℓ),
      (simulateQ (pImpl C.F)
        ((saltRedImpl C codec ℓ encT idOf b (.inr (.inr (a, e)))).run chal)).run
          { key := key, b := false, table := [] } =
        pure ((res, chal), { key := key, b := false, table := [] }) ∧
      (aImpl C codec ℓ encT idOf (.inr (.inr (a, e)))).run
        { key := key, b := b, chal := chal } =
        pure (res, { key := key, b := b, chal := chal }) := by
  cases b
  · by_cases hchal : chal = some (a, e)
    · refine ⟨none, ?_, ?_⟩
      · simp [saltRedImpl, hchal]
      · simp [aImpl, otccaDecrypt, hchal]
    · by_cases hsalt : e.2 = a.2.2.salt
      · refine ⟨(lAeadK C codec ℓ encT idOf).dec (deriveMessageKeys C.F a.2.2.salt (keyToBytes32 key))
            ((a.1, a.2.1), a.2.2) e, ?_, ?_⟩
        · simp [saltRedImpl, hchal, hsalt]
        · simp [aImpl, otccaDecrypt, hchal, lAeadR, lAead, hsalt]
      · refine ⟨none, ?_, ?_⟩
        · simp [saltRedImpl, hsalt]
        · simp [aImpl, otccaDecrypt, lAeadR, lAead, hsalt]
  · refine ⟨none, ?_, ?_⟩
    · simp [saltRedImpl]
    · simp [aImpl, otccaDecrypt]

theorem runSaltRed_eq (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) (key : BitVec 256)
    {α : Type} (oa : OracleComp (unifSpec + otccaSpec (AD Pt) (Plain ℓ) Ct) α) :
    ∀ (chal : ChalState Pt),
      (fun r => r.1.1) <$>
        runSaltRed C codec ℓ encT idOf b oa chal { key := key, b := false, table := [] } =
      Prod.fst <$> (simulateQ (aImpl C codec ℓ encT idOf) oa).run
        { key := key, b := b, chal := chal } := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro chal
    simp [runSaltRed_pure]
  | query_bind q k ih =>
    intro chal
    rw [runSaltRed_query_bind, aImpl_query_bind, map_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · rw [step_inl, aImpl_step_inl]
      simp only [bind_assoc, pure_bind]
      exact bind_congr fun u => ih u chal
    · rcases chal with _ | ⟨a₀, e₀⟩
      · cases b
        · obtain ⟨h1, h2⟩ := step_enc_none_false C codec ℓ encT idOf key a m
          rw [h1, h2, pure_bind, pure_bind]
          exact ih _ _
        · obtain ⟨h1, h2⟩ := step_enc_none_true C codec ℓ encT idOf key a m
          rw [h1, h2]
          simp only [bind_assoc, pure_bind]
          exact bind_congr fun e => ih (some e) (some (a, e))
      · obtain ⟨h1, h2⟩ := step_enc_some C codec ℓ encT idOf b key a a₀ m e₀
        rw [h1, h2, pure_bind, pure_bind]
        exact ih none (some (a₀, e₀))
    · obtain ⟨res, h1, h2⟩ := step_dec C codec ℓ encT idOf b key a e chal
      rw [h1, h2, pure_bind, pure_bind]
      exact ih res chal

theorem evalDist_otccaGameWith_eq_branch_false (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) :
    𝒟[(lAeadR C codec ℓ encT idOf).otccaGameAdIdeal (lIdeal C codec ℓ encT) B] =
      𝒟[MACScheme.branch (lSaltPRF32 C.F) false (lSaltRed C codec ℓ encT idOf B)] := by
  have hbranch : MACScheme.branch (lSaltPRF32 C.F) false (lSaltRed C codec ℓ encT idOf B) =
      (do
        let key ← $ᵗ (BitVec 256)
        let b ← $ᵗ Bool
        let b' ← (simulateQ (aImpl C codec ℓ encT idOf) B).run' { key := key, b := b }
        return b == b') := by
    unfold MACScheme.branch lSaltRed
    refine bind_congr fun key => ?_
    change (Prod.fst <$> (simulateQ (pImpl C.F) (do
        let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
          OracleComp (unifSpec + prfSpec Salt32 DerivedMessageKeys) Bool)
        let b' ← (simulateQ (saltRedImpl C codec ℓ encT idOf b) B).run' none
        return b == b')).run { key := key, b := false, table := [] }) = _
    simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind,
      simulateQ_pImpl_liftM_run, simulateQ_map, bind_assoc, pure_bind]
    refine bind_congr fun b => ?_
    have hrun := runSaltRed_eq C codec ℓ encT idOf b key B none
    have hrun' : (fun x : (Bool × ChalState Pt) × PState => b == x.1.1) <$>
        runSaltRed C codec ℓ encT idOf b B none { key := key, b := false, table := [] } =
      (fun x : Bool × AState Pt => b == x.1) <$>
        (simulateQ (aImpl C codec ℓ encT idOf) B).run { key := key, b := b, chal := none } := by
      have hmap := congrArg ((b == ·) <$> ·) hrun
      simpa [Functor.map_map] using hmap
    simpa [runSaltRed, map_eq_bind_pure_comp] using hrun'
  rw [hbranch]
  unfold otccaGameAdIdeal
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ Bool) ($ᵗ (BitVec 256)) _

/-! ## Multi-slot salt-PRF hop -/

open WireHop FSAEAD.Thm5 CryptoGames.Lazy

theorem slotSaltImpl_run_map (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α) (st : SaltSt Pt) :
    (simulateQ (slotSaltImpl C codec ℓ encT idOf b) oa).run { chal := st.chal, table := st.table } =
      Prod.map id (fun s : SaltSt Pt => ({ chal := s.chal, table := s.table } : SaltSlotSt Pt)) <$>
        (simulateQ (saltImpl C codec ℓ encT idOf b) oa).run st := by
  have := EtMProof.run_map (slotSaltImpl C codec ℓ encT idOf b) (saltImpl C codec ℓ encT idOf b)
    (fun s : SaltSt Pt => ({ chal := s.chal, table := s.table } : SaltSlotSt Pt))
    (fun _ => True) (fun t s _ => ?_) oa st trivial
  · simpa using this
  refine ⟨?_, fun _ _ => trivial⟩
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · simp [slotSaltImpl, saltImpl, EtMProof.coin]
  · by_cases hc : s.chal.isSome = true
    · simp [slotSaltImpl, saltImpl, hc]
    · simp only [slotSaltImpl, saltImpl, slotKeyOf, sKeyOf, sSlot, StateT.run_bind,
        StateT.run_get, StateT.run_mk, pure_bind, hc, Bool.false_eq_true, ↓reduceIte, map_bind]
      cases hlk : s.table.lookup a.2.2.salt with
      | some mk =>
        cases b <;> simp [StateT.run_lift, map_pure]
      | none =>
        cases b <;> simp [StateT.run_lift, bind_map_left, map_pure]
  · by_cases hs : e.2 ≠ a.2.2.salt
    · simp [slotSaltImpl, saltImpl, hs]
    · simp only [slotSaltImpl, saltImpl, slotKeyOf, sKeyOf, sSlot, hs, ↓reduceIte,
        StateT.run_bind, StateT.run_get, StateT.run_mk, pure_bind]
      by_cases hbc : (b || (s.chal == some (a, e))) = true
      · simp [hbc]
      · simp only [hbc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_mk,
          StateT.run_pure, map_bind]
        cases s.table.lookup a.2.2.salt <;> simp

theorem slotSaltImpl_fst_eq_saltRun (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) :
    Prod.fst <$> (simulateQ (slotSaltImpl C codec ℓ encT idOf b) B).run {} =
      saltRun C codec ℓ encT idOf b B := by
  rw [slotSaltImpl_run_map C codec ℓ encT idOf b B {}, Functor.map_map]
  rfl

theorem slotSaltImplNF_run_map (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α) (st : SaltSt Pt) :
    (simulateQ (slotSaltImplNF C codec ℓ encT idOf b) oa).run
        { chal := st.chal, table := st.table } =
      Prod.map id (fun s : SaltSt Pt => ({ chal := s.chal, table := s.table } : SaltSlotSt Pt)) <$>
        (simulateQ (saltImplNF C codec ℓ encT idOf b) oa).run st := by
  have := EtMProof.run_map (slotSaltImplNF C codec ℓ encT idOf b) (saltImplNF C codec ℓ encT idOf b)
    (fun s : SaltSt Pt => ({ chal := s.chal, table := s.table } : SaltSlotSt Pt))
    (fun _ => True) (fun t s _ => ?_) oa st trivial
  · simpa using this
  refine ⟨?_, fun _ _ => trivial⟩
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · simp [slotSaltImplNF, saltImplNF, EtMProof.coin]
  · by_cases hc : s.chal.isSome = true
    · simp [slotSaltImplNF, saltImplNF, hc]
    · simp only [slotSaltImplNF, saltImplNF, slotKeyOf, sKeyOf, StateT.run_bind,
        StateT.run_get, StateT.run_mk, pure_bind, hc, Bool.false_eq_true, ↓reduceIte, map_bind]
      cases hlk : s.table.lookup a.2.2.salt with
      | some mk =>
        cases b <;> simp [StateT.run_lift, map_pure]
      | none =>
        cases b <;> simp [StateT.run_lift, bind_map_left, map_pure]
  · by_cases hs : e.2 ≠ a.2.2.salt
    · simp [slotSaltImplNF, saltImplNF, hs]
    · have his : isSlotChalSalt s.chal a.2.2.salt = isChalSalt s.chal a.2.2.salt := rfl
      simp only [slotSaltImplNF, saltImplNF, slotKeyOf, sKeyOf, hs, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind, his]
      by_cases hbc : (b || !(isChalSalt s.chal a.2.2.salt) || (s.chal == some (a, e))) = true
      · simp [hbc]
      · simp only [hbc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_mk,
          StateT.run_pure, map_bind]
        cases s.table.lookup a.2.2.salt <;> simp

theorem slotSaltImplNF_fst_eq_saltRunNF (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) :
    Prod.fst <$> (simulateQ (slotSaltImplNF C codec ℓ encT idOf b) B).run {} =
      saltRunNF C codec ℓ encT idOf b B := by
  rw [slotSaltImplNF_run_map C codec ℓ encT idOf b B {}, Functor.map_map]
  rfl

theorem evalDist_aImpl_true_eq_slotSaltImpl_true (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (key : BitVec 256)
    (oa : OracleComp (QSpecS Pt ℓ) Bool) :
    ∀ (chal : ChalState Pt) (st : SaltSlotSt Pt),
      st.chal = chal →
      𝒟[Prod.fst <$> (simulateQ (aImpl C codec ℓ encT idOf) oa).run
          { key := key, b := true, chal := chal }] =
        𝒟[Prod.fst <$> (simulateQ (slotSaltImpl C codec ℓ encT idOf true) oa).run st] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro chal st _; simp
  | query_bind q k ih =>
    intro chal st hchal
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [aImpl_step_inl, slotSaltImpl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_monadLift, bind_assoc, pure_bind]
      exact evalDist_bind_congr _ _ _ fun u => ih u chal st hchal
    · rcases chal with _ | ⟨a₀, e₀⟩
      · have hc : st.chal.isSome = false := by simp [hchal]
        rw [(step_enc_none_true C codec ℓ encT idOf key a m).2]
        simp only [slotSaltImpl, StateT.run_bind, StateT.run_get, pure_bind, hc,
          Bool.false_eq_true, ↓reduceIte, StateT.run_lift, StateT.run_modify, StateT.run_pure,
          bind_assoc]
        symm
        refine (evalDist_bind_congr_support _ _
          (fun _ => do
            let e ← lIdeal C codec ℓ encT a
            Prod.fst <$> (simulateQ (aImpl C codec ℓ encT idOf) (k (some e))).run
              { key := key, b := true, chal := some (a, e) })
          fun p _ => ?_).trans (OracleComp.evalDist_bind_const _ _)
        rcases p with ⟨mk, st₁⟩
        refine evalDist_bind_congr _ _ _ fun e => ?_
        exact (ih (some e) (some (a, e)) { st₁ with chal := some (a, e) } rfl).symm
      · have hc : st.chal.isSome = true := by simp [hchal]
        rw [(step_enc_some C codec ℓ encT idOf true key a a₀ m e₀).2, pure_bind]
        simp only [slotSaltImpl, StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte,
          StateT.run_pure]
        exact ih none (some (a₀, e₀)) st hchal
    · have hdec : (aImpl C codec ℓ encT idOf (.inr (.inr (a, e)))).run
          { key := key, b := true, chal := chal } =
          pure (none, { key := key, b := true, chal := chal }) := by
        simp [aImpl, otccaDecrypt]
      rw [hdec, pure_bind]
      by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [slotSaltImpl, hs, ne_eq, not_false_eq_true, ↓reduceIte, StateT.run_pure,
          pure_bind]
        exact ih none chal st hchal
      · simp only [slotSaltImpl, hs, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          Bool.true_or, StateT.run_pure]
        exact ih none chal st hchal

theorem evalDist_aImpl_true_eq_saltRun_true (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (key : BitVec 256)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) :
    𝒟[Prod.fst <$> (simulateQ (aImpl C codec ℓ encT idOf) B).run
        { key := key, b := true, chal := none }] =
      𝒟[saltRun C codec ℓ encT idOf true B] := by
  rw [evalDist_aImpl_true_eq_slotSaltImpl_true C codec ℓ encT idOf key B none {} rfl,
    slotSaltImpl_fst_eq_saltRun]

theorem otImpl_eq_aImpl (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :
    otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) =
      aImpl C codec ℓ encT idOf := rfl

theorem evalDist_slotLift_otImpl_true_eq_slotLift_slotSaltImpl_true
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (oa : OracleComp (QSpecS Pt ℓ) Bool) :
    ∀ (st₁ : ℕ → IndexedOtccaState (BitVec 256) (Header Pt × LibsignalMsgPublicPart) Ct) (st₂ : ℕ → SaltSlotSt Pt),
      (∀ i, (st₁ i).b = true) →
      (∀ i, (st₁ i).chal = (st₂ i).chal) →
      𝒟[Prod.fst <$> (simulateQ
          (slotLift (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))) oa).run st₁] =
        𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf true)) oa).run st₂] := by
  rw [otImpl_eq_aImpl]
  induction oa using OracleComp.inductionOn with
  | pure a => intro st₁ st₂ _ _; simp
  | query_bind q k ih =>
    intro st₁ st₂ hb hchal
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [slotLift_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_monadLift, bind_assoc, pure_bind]
      exact evalDist_bind_congr _ _ _ fun u => ih u st₁ st₂ hb hchal
    · simp only [slotLift_inr, slotLiftOtcca, StateT.run_mk, bind_assoc]
      have hst₁ : st₁ a.1 = { key := (st₁ a.1).key, b := true, chal := (st₂ a.1).chal } := by
        rw [← hb a.1, ← hchal a.1]
      rw [hst₁]
      rcases hc : (st₂ a.1).chal with _ | ⟨a₀, e₀⟩
      · have hcf : (st₂ a.1).chal.isSome = false := by simp [hc]
        rw [(step_enc_none_true C codec ℓ encT idOf (st₁ a.1).key a m).2]
        simp only [slotSaltImpl, StateT.run_bind, StateT.run_get, pure_bind, hcf,
          Bool.false_eq_true, ↓reduceIte, StateT.run_lift, StateT.run_modify, StateT.run_pure,
          bind_assoc]
        symm
        refine (evalDist_bind_congr_support _ _
          (fun _ => do
            let e ← lIdeal C codec ℓ encT a
            Prod.fst <$> (simulateQ
              (slotLift (aImpl C codec ℓ encT idOf))
              (k (some e))).run
              (Function.update st₁ a.1 { key := (st₁ a.1).key, b := true, chal := some (a, e) }))
          fun p _ => ?_).trans (OracleComp.evalDist_bind_const _ _)
        rcases p with ⟨mk, s₂'⟩
        refine evalDist_bind_congr _ _ _ fun e => (ih (some e) _ _ ?_ ?_).symm
        · intro i
          by_cases hi : i = a.1
          · subst hi; simp
          · simp [Function.update_of_ne hi, hb i]
        · intro i
          by_cases hi : i = a.1
          · subst hi; simp
          · simp [Function.update_of_ne hi, hchal i]
      · have hct : (st₂ a.1).chal.isSome = true := by simp [hc]
        rw [(step_enc_some C codec ℓ encT idOf true (st₁ a.1).key a a₀ m e₀).2, pure_bind]
        simp only [slotSaltImpl, StateT.run_bind, StateT.run_get, pure_bind, hct, ↓reduceIte,
          StateT.run_pure]
        have hup₁ : Function.update st₁ a.1
            { key := (st₁ a.1).key, b := true, chal := some (a₀, e₀) } = st₁ := by
          rw [← hc, ← hst₁, Function.update_eq_self]
        rw [hup₁, Function.update_eq_self]
        exact ih none st₁ st₂ hb hchal
    · simp only [slotLift_inr, slotLiftOtcca, StateT.run_mk, bind_assoc]
      have hdec : (aImpl C codec ℓ encT idOf (.inr (.inr (a, e)))).run (st₁ a.1) =
          pure (none, st₁ a.1) := by
        simp [aImpl, otccaDecrypt, hb a.1]
      rw [hdec, pure_bind, Function.update_eq_self]
      by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [slotSaltImpl, hs, ne_eq, not_false_eq_true, ↓reduceIte, StateT.run_pure,
          pure_bind, Function.update_eq_self]
        exact ih none st₁ st₂ hb hchal
      · simp only [slotSaltImpl, hs, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          Bool.true_or, StateT.run_pure, Function.update_eq_self]
        exact ih none st₁ st₂ hb hchal

theorem evalDist_multiOtBranch_true_eq_slotLift_slotSaltImpl_true
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) :
    𝒟[multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) true N B] =
      𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf true)) B).run
        (fun _ => {})] := by
  unfold multiOtBranch
  have h : ∀ (K₀ : BitVec 256) (ks : List (BitVec 256)),
      𝒟[Prod.fst <$> (simulateQ
          (slotLift (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))) B).run
          (initOStM true K₀ ks)] =
        𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf true)) B).run
          (fun _ => {})] := fun K₀ ks =>
    evalDist_slotLift_otImpl_true_eq_slotLift_slotSaltImpl_true C codec ℓ encT idOf B
      (initOStM true K₀ ks) (fun _ => {}) (fun _ => rfl) (fun _ => rfl)
  refine (evalDist_bind_congr ($ᵗ (BitVec 256)) _
    (fun _ => Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf true)) B).run
      (fun _ => {}))
    fun K₀ => ?_).trans (OracleComp.evalDist_bind_const _ _)
  exact (evalDist_bind_congr (sampleKeys N) _ _ fun ks => h K₀ ks).trans
    (OracleComp.evalDist_bind_const _ _)

theorem boolDist_bind_coin_false (μ ν₁ ν₂ : ProbComp Bool) :
    𝒟[ν₁].boolDist 𝒟[ν₂] =
      2 * 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => (if b then μ else ν₁) >>= fun z => pure (b == z)].boolDist
        𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => (if b then μ else ν₂) >>= fun z => pure (b == z)] := by
  have hgame : ∀ (ν : ProbComp Bool),
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => (if b then μ else ν) >>= fun z => pure (b == z)] {true} =
        (𝒟[μ] {true} + 𝒟[ν] {false}) / 2 := by
    intro ν
    rw [CryptoGames.CellForgery.bind_apply_fin, Fintype.sum_bool]
    have htrue : 𝒟[(if true then μ else ν) >>= fun z => pure (true == z)] {true} = 𝒟[μ] {true} := by
      simp
    have hfalse : 𝒟[(if false then μ else ν) >>= fun z => pure (false == z)] {true} = 𝒟[ν] {false} := by
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [CryptoGames.CellForgery.bind_apply_fin, Fintype.sum_bool]
      simp
    have hcoin : ∀ b : Bool, 𝒟[($ᵗ Bool : ProbComp Bool)] {b} = 2⁻¹ := fun _ => by simp
    rw [htrue, hfalse, hcoin true, hcoin false, ← add_mul, div_eq_mul_inv]
  rw [← ENNReal.toReal_eq_toReal_iff' (Measure.boolDist_ne_top _ _)
      (mul_ne_top ofNat_ne_top (Measure.boolDist_ne_top _ _)),
    Measure.toReal_boolDist, ENNReal.toReal_mul, Measure.toReal_boolDist, hgame ν₁, hgame ν₂]
  have h1 := congrArg ENNReal.toReal (Measure.apply_true_add_apply_false_eq_one 𝒟[ν₁])
  have h2 := congrArg ENNReal.toReal (Measure.apply_true_add_apply_false_eq_one 𝒟[ν₂])
  simp only [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_ofNat] at h1 h2 ⊢
  rw [show (𝒟[ν₁] {true}).toReal - (𝒟[ν₂] {true}).toReal =
      -(2 * (((𝒟[μ] {true}).toReal + (𝒟[ν₁] {false}).toReal) / 2 -
        ((𝒟[μ] {true}).toReal + (𝒟[ν₂] {false}).toReal) / 2)) by linarith,
    abs_neg, abs_mul, abs_two]

theorem otccaBranch_false_boolDist_saltRun_false (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) :
    𝒟[do
      let key ← $ᵗ (BitVec 256)
      Prod.fst <$> (simulateQ (aImpl C codec ℓ encT idOf) B).run
        { key := key, b := false, chal := none }].boolDist
      𝒟[saltRun C codec ℓ encT idOf false B] =
      2 * (lSaltPRF32 C.F).prfAdvantage (lSaltRed C codec ℓ encT idOf B) := by
  let μ := saltRun C codec ℓ encT idOf true B
  let ν₁ := do
    let key ← $ᵗ (BitVec 256)
    Prod.fst <$> (simulateQ (aImpl C codec ℓ encT idOf) B).run
      { key := key, b := false, chal := none }
  let ν₂ := saltRun C codec ℓ encT idOf false B
  have hbrF : 𝒟[MACScheme.branch (lSaltPRF32 C.F) false (lSaltRed C codec ℓ encT idOf B)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => (if b then μ else ν₁) >>= fun z => pure (b == z)] := by
    rw [← evalDist_otccaGameWith_eq_branch_false]
    unfold otccaGameAdIdeal
    refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, ν₁, StateT.run'_eq, map_eq_bind_pure_comp,
        bind_assoc]
      rfl
    · simp only [↓reduceIte, μ, StateT.run'_eq, Bool.true_beq, bind_pure]
      exact (evalDist_bind_congr ($ᵗ (BitVec 256)) _ _ fun key =>
        evalDist_aImpl_true_eq_saltRun_true C codec ℓ encT idOf key B).trans
        (OracleComp.evalDist_bind_const _ _)
  have hbrT : 𝒟[MACScheme.branch (lSaltPRF32 C.F) true (lSaltRed C codec ℓ encT idOf B)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => (if b then μ else ν₂) >>= fun z => pure (b == z)] := by
    unfold MACScheme.branch
    have hkey : ∀ key : BitVec 256,
        (simulateQ (prfImpl C.F) (lSaltRed C codec ℓ encT idOf B)).run'
            { key, b := true } =
          (($ᵗ Bool : ProbComp Bool) >>= fun b =>
            (if b then μ else ν₂) >>= fun z => pure (b == z)) := by
      intro key
      change (simulateQ (prfImpl C.F) (do
          let b ← $ᵗ Bool
          let b' ← (simulateQ (lSaltRedImpl C codec ℓ encT idOf b) B).run' none
          return b == b')).run' { key, b := true } = _
      simp only [StateT.run'_eq, simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
        map_bind, simulateQ_prfImpl_liftM, StateT.run_monadLift, bind_assoc,
        pure_bind, simulateQ_pure, StateT.run_pure]
      refine bind_congr fun b => ?_
      have hsim := congrArg (fun m : ProbComp Bool => m >>= fun b' => pure (b == b'))
        (lSaltRed_simulateQ_eq C codec ℓ encT idOf b key B {})
      cases b <;>
        simpa [saltRun, saltFull, map_eq_bind_pure_comp, bind_assoc, μ, ν₂] using hsim
    change 𝒟[do let key ← $ᵗ (BitVec 256)
                (simulateQ (prfImpl C.F) (lSaltRed C codec ℓ encT idOf B)).run'
                  { key, b := true }] = _
    simp only [hkey, OracleComp.evalDist_bind_const]
  rw [boolDist_bind_coin_false μ ν₁ ν₂, ← hbrF, ← hbrT,
    MACScheme.prfAdvantage_eq_boolDist, Measure.boolDist_comm]

/-- Multi-slot hybrid between `otImpl false` and `slotSaltImpl false` at step `k`. -/
def saltHyb (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N k : ℕ)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) : ProbComp Bool := do
  let K₀ ← $ᵗ (BitVec 256)
  let ks ← sampleKeys (MK := BitVec 256) N
  Prod.fst <$> (simulateQ
    (hybSlot (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
      (slotSaltImpl C codec ℓ encT idOf false) k) B).run
    (initOStM false K₀ ks, fun _ => {})

theorem saltHyb_zero (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) :
    saltHyb C codec ℓ encT idOf N 0 B =
      multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) false N B := by
  unfold saltHyb multiOtBranch
  refine bind_congr fun K₀ => bind_congr fun ks => ?_
  rw [hybSlot_zero, Functor.map_map]

theorem evalDist_saltHyb_self (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct)
    (hoff : B.IsQueryBoundP (fun t => multiOffRange N t = true) 0) :
    𝒟[saltHyb C codec ℓ encT idOf N N B] =
      𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf false)) B).run
        (fun _ => {})] := by
  unfold saltHyb
  have h : ∀ (K₀ : BitVec 256) (ks : List (BitVec 256)),
      Prod.fst <$> (simulateQ
        (hybSlot (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
          (slotSaltImpl C codec ℓ encT idOf false) N) B).run
        (initOStM false K₀ ks, fun _ => {}) =
      Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf false)) B).run
        (fun _ => {}) := fun K₀ ks => by
    have h1 := congrArg (Prod.fst <$> ·)
      (hybSlot_eq_slotLift_of_offRange
        (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
        (slotSaltImpl C codec ℓ encT idOf false) N B hoff (initOStM false K₀ ks) (fun _ => {}))
    simpa only [Functor.map_map] using h1
  simp only [h, OracleComp.evalDist_bind_const]

theorem evalDist_saltHyb_step_left (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) {N k : ℕ} (hk : k < N)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) :
    𝒟[saltHyb C codec ℓ encT idOf N k B] =
      𝒟[do
        let key ← $ᵗ (BitVec 256)
        Prod.fst <$> (simulateQ (aImpl C codec ℓ encT idOf)
          (slotSaltRed C codec ℓ encT idOf N k B)).run
          { key := key, b := false, chal := none }] := by
  have hinl : ∀ n (s : IndexedOtccaState (BitVec 256) (Header Pt × LibsignalMsgPublicPart) Ct),
      (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) (.inl n)).run s =
        (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
          fun u => pure (u, s) := fun n s => by simp [otImpl]
  have hstep : ∀ (key K₀ : BitVec 256) (ks : List (BitVec 256)),
      ks ∈ support (sampleKeys (MK := BitVec 256) N) →
      Prod.fst <$> (simulateQ
        (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
        (Prod.fst <$> (simulateQ
          (slotRedImpl
            (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
            (slotSaltImpl C codec ℓ encT idOf false) k) B).run
          (initOStM false K₀ ks, fun _ => {}))).run
        { key := key, b := false, chal := none } =
      Prod.fst <$> (simulateQ
        (hybSlot (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
          (slotSaltImpl C codec ℓ encT idOf false) k) B).run
        (initOStM false K₀ (ks.set k key), fun _ => {}) := by
    intro key K₀ ks hks
    have hlen : k < ks.length := by rw [length_mem_support_sampleKeys hks]; exact hk
    have h := congrArg (Prod.fst <$> ·)
      (hybSlot_step_left
        (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
        (slotSaltImpl C codec ℓ encT idOf false) hinl k B
        (initOStM false K₀ ks) (fun _ => {}) { key := key, b := false, chal := none })
    rw [update_initOStM false K₀ ks k key hlen] at h
    simpa only [simulateQ_map, StateT.run_map, Functor.map_map] using h
  have hred : ∀ key : BitVec 256,
      DEq
        (Prod.fst <$> (simulateQ (aImpl C codec ℓ encT idOf)
          (slotSaltRed C codec ℓ encT idOf N k B)).run
          { key := key, b := false, chal := none })
        (do
          let K₀ ← $ᵗ (BitVec 256)
          let ks ← sampleKeys (MK := BitVec 256) N
          Prod.fst <$> (simulateQ
            (hybSlot (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
              (slotSaltImpl C codec ℓ encT idOf false) k) B).run
            (initOStM false K₀ (ks.set k key), fun _ => {})) := by
    intro key
    have hlift : ∀ {β : Type} (p : ProbComp β),
        (simulateQ (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
          (liftM p : OracleComp (IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) Ct) β)).run
          { key := key, b := false, chal := none } =
          (fun a => (a, ({ key := key, b := false, chal := none } :
            IndexedOtccaState (BitVec 256) (Header Pt × LibsignalMsgPublicPart) Ct))) <$> p :=
      fun p => simulateQ_liftM_run_of_inl
        (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := Ct)
        (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)) hinl p
        { key := key, b := false, chal := none }
    rw [← otImpl_eq_aImpl]
    unfold slotSaltRed
    simp only [simulateQ_bind, StateT.run_bind, map_bind, hlift, bind_map_left]
    exact DEq.bind_right ($ᵗ (BitVec 256)) fun K₀ =>
      DEq.bind_right_supp (sampleKeys N) fun ks hks => DEq.of_eq (hstep key K₀ ks hks)
  refine DEq.evalDist_eq (DEq.symm ?_)
  refine (DEq.bind_right ($ᵗ (BitVec 256)) hred).trans ?_
  unfold saltHyb
  refine (DEq.swap ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256))
    (fun key K₀ => do
      let ks ← sampleKeys (MK := BitVec 256) N
      Prod.fst <$> (simulateQ
        (hybSlot (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
          (slotSaltImpl C codec ℓ encT idOf false) k) B).run
        (initOStM false K₀ (ks.set k key), fun _ => {}))).trans ?_
  refine DEq.bind_right ($ᵗ (BitVec 256)) fun K₀ => ?_
  exact sampleKeys_set_deq hk fun ks =>
    Prod.fst <$> (simulateQ
      (hybSlot (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
        (slotSaltImpl C codec ℓ encT idOf false) k) B).run
      (initOStM false K₀ ks, fun _ => {})

theorem saltHyb_step_right (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N k : ℕ)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) :
    saltHyb C codec ℓ encT idOf N (k + 1) B =
      saltRun C codec ℓ encT idOf false (slotSaltRed C codec ℓ encT idOf N k B) := by
  rw [← slotSaltImpl_fst_eq_saltRun]
  have hinl : ∀ n (s : SaltSlotSt Pt),
      (slotSaltImpl C codec ℓ encT idOf false (.inl n)).run s =
        (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
          fun u => pure (u, s) := fun n s => by simp [slotSaltImpl]
  have hlift : ∀ {β : Type} (p : ProbComp β),
      (simulateQ (slotSaltImpl C codec ℓ encT idOf false)
        (liftM p : OracleComp (IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) Ct) β)).run {} =
        (fun a => (a, ({} : SaltSlotSt Pt))) <$> p :=
    fun p => simulateQ_liftM_run_of_inl
      (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := Ct)
      (slotSaltImpl C codec ℓ encT idOf false) hinl p {}
  unfold saltHyb slotSaltRed
  simp only [simulateQ_bind, StateT.run_bind, map_bind, hlift, bind_map_left]
  refine bind_congr fun K₀ => bind_congr fun ks => ?_
  have hstep := congrArg (Prod.fst <$> ·)
    (hybSlot_step_right
      (otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
      (slotSaltImpl C codec ℓ encT idOf false) hinl k B
      (initOStM false K₀ ks) (fun _ => {}) {})
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map, Function.update_eq_self] using
    hstep.symm

theorem multiOtBranch_false_boolDist_multiSalt_false (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct)
    (hoff : B.IsQueryBoundP (fun t => multiOffRange N t = true) 0) :
    𝒟[multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) false N B].boolDist
      𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf false)) B).run
        (fun _ => {})] ≤
      ∑ k ∈ Finset.range N,
        2 * (lSaltPRF32 C.F).prfAdvantage
          (lSaltRed C codec ℓ encT idOf (slotSaltRed C codec ℓ encT idOf N k B)) := by
  rw [← saltHyb_zero C codec ℓ encT idOf N B,
    ← evalDist_saltHyb_self C codec ℓ encT idOf N B hoff]
  refine (Measure.boolDist_le_sum_range
    (fun k => 𝒟[saltHyb C codec ℓ encT idOf N k B]) N).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k < N := Finset.mem_range.mp hk
  rw [evalDist_saltHyb_step_left C codec ℓ encT idOf hk' B,
    saltHyb_step_right C codec ℓ encT idOf N k B,
    otccaBranch_false_boolDist_saltRun_false]

/-! ## Global multi-slot MAC forgery hop -/

abbrev MSaltSt (Pt : Type) := ℕ → SaltSlotSt Pt

def mKeyOfF (i : ℕ) (salt : Salt32) : StateT (MSaltSt Pt × Bool) ProbComp DerivedMessageKeys :=
  StateT.mk fun (st, f) =>
    (fun p : DerivedMessageKeys × SaltSlotSt Pt => (p.1, (Function.update st i p.2, f))) <$>
      (slotKeyOf salt).run (st i)

/-- Multi-slot flag game returning `none` and raising a global flag when a non-challenge-salt decryption passes the HMAC tag check. -/
def multiSaltFlagNF (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :
    QueryImpl (QSpecS Pt ℓ) (StateT (MSaltSt Pt × Bool) ProbComp)
  | .inl n => EtMProof.coin n
  | .inr (.inl ⟨a, m⟩) => do
    let s ← get
    if (s.1 a.1).chal.isSome then return none
    let mk ← mKeyOfF a.1 a.2.2.salt
    let e := (lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m
    modify fun (st, f) =>
      (Function.update st a.1 { (st a.1) with chal := some (a, e) }, f)
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if e.2 ≠ a.2.2.salt then return none
    let s ← get
    if (s.1 a.1).chal == some (a, e) then return none
    let mk ← mKeyOfF a.1 a.2.2.salt
    if isChalSalt (s.1 a.1).chal a.2.2.salt then
      return (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e
    else
      modify fun (st, f) =>
        (st, f || ((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2))
      return none

theorem multiSaltFlagNF_flag (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (st : MSaltSt Pt) (fl : Bool) :
    (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, fl) =
      Prod.map id (fun z : MSaltSt Pt × Bool => (z.1, fl || z.2)) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, false) := by
  have := EtMProof.run_map (multiSaltFlagNF C codec ℓ encT idOf)
    (multiSaltFlagNF C codec ℓ encT idOf)
    (fun z : MSaltSt Pt × Bool => (z.1, fl || z.2)) (fun _ => True)
    (fun t z _ => ?_) oa (st, false) trivial
  · simpa using this
  refine ⟨?_, fun _ _ => trivial⟩
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · simp [multiSaltFlagNF, EtMProof.coin]
  · by_cases hc : (z.1 a.1).chal.isSome = true
    · simp only [multiSaltFlagNF, StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte,
        StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    · simp only [multiSaltFlagNF, mKeyOfF, StateT.run_bind, StateT.run_get, pure_bind, hc,
        Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_modify, StateT.run_pure,
        bind_map_left, map_bind, map_pure, Prod.map_apply, id_eq]
  · by_cases hs : e.2 ≠ a.2.2.salt
    · simp only [multiSaltFlagNF, hs, ne_eq, not_false_eq_true, ↓reduceIte, StateT.run_pure,
        map_pure, Prod.map_apply, id_eq]
    · by_cases hch : ((z.1 a.1).chal == some (a, e)) = true
      · simp only [multiSaltFlagNF, hs, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          hch, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
      · by_cases hcs : isChalSalt (z.1 a.1).chal a.2.2.salt = true
        · simp only [multiSaltFlagNF, mKeyOfF, hs, ↓reduceIte, StateT.run_bind, StateT.run_get,
            pure_bind, hch, Bool.false_eq_true, StateT.run_mk, hcs, StateT.run_pure,
            bind_map_left, map_bind, map_pure, Prod.map_apply, id_eq]
        · simp only [multiSaltFlagNF, mKeyOfF, hs, ↓reduceIte, StateT.run_bind, StateT.run_get,
            pure_bind, hch, Bool.false_eq_true, StateT.run_mk, hcs, StateT.run_modify,
            StateT.run_pure, bind_map_left, map_bind, map_pure,
            Prod.map_apply, id_eq, Bool.or_assoc]

theorem multiSaltFlagNF_flag_or (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (st : MSaltSt Pt) (fl : Bool) :
    (fun z : α × MSaltSt Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, fl) =
      (fl || ·) <$> ((fun z : α × MSaltSt Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, false)) := by
  rw [multiSaltFlagNF_flag C codec ℓ encT idOf oa st fl, Functor.map_map, Functor.map_map]
  rfl

theorem multiSaltFlagNF_out_fl (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (st : MSaltSt Pt) (fl : Bool) :
    (fun z : α × MSaltSt Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, fl) =
      (fun z : α × MSaltSt Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, false) := by
  rw [multiSaltFlagNF_flag C codec ℓ encT idOf oa st fl, Functor.map_map]
  rfl

theorem slotLift_slotSaltImpl_false_le_multiSaltFlagNF (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (post : α → ProbComp Bool) (x : Bool) :
    ∀ (st : MSaltSt Pt),
      𝒟[(simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf false)) oa).run st >>=
        fun z => post z.1] {x} ≤
        𝒟[(simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, false) >>=
          fun z => post z.1] {x} +
        𝒟[(fun z => z.2.2) <$>
          (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, false)] {true} := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st; simp
  | query_bind q k ih =>
    intro st
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [slotLift_inl, multiSaltFlagNF, EtMProof.coin, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, bind_assoc, pure_bind]
      exact WireHop.bind_apply_le_add_true _ _ _ _ x fun u => ih u st
    · by_cases hc : (st a.1).chal.isSome = true
      · simp only [slotLift_inr, slotLiftOtcca, slotSaltImpl, multiSaltFlagNF, StateT.run_mk,
          StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte, StateT.run_pure,
          Function.update_eq_self]
        exact ih none st
      · simp only [slotLift_inr, slotLiftOtcca, slotSaltImpl, multiSaltFlagNF, mKeyOfF, slotKeyOf,
          StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, hc, Bool.false_eq_true,
          ↓reduceIte, StateT.run_modify, StateT.run_pure, bind_map_left, bind_assoc,
          Function.update_self, Function.update_idem]
        cases hlk : (st a.1).table.lookup a.2.2.salt with
        | some mk =>
          simp only [pure_bind]
          exact ih _ _
        | none =>
          simp only [bind_map_left]
          exact WireHop.bind_apply_le_add_true _ _ _ _ x fun mk => ih _ _
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [slotLift_inr, slotLiftOtcca, slotSaltImpl, multiSaltFlagNF, hs, ne_eq,
          not_false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_pure, pure_bind,
          Function.update_eq_self]
        exact ih none st
      · simp only [ne_eq, Decidable.not_not] at hs
        by_cases hch : ((st a.1).chal == some (a, e)) = true
        · simp only [slotLift_inr, slotLiftOtcca, slotSaltImpl, multiSaltFlagNF, hs, ne_eq,
            not_true_eq_false, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get,
            pure_bind, Bool.false_or, hch, StateT.run_pure, Function.update_eq_self]
          exact ih none st
        · by_cases hcs : isChalSalt (st a.1).chal a.2.2.salt = true
          · simp only [slotLift_inr, slotLiftOtcca, slotSaltImpl, multiSaltFlagNF, mKeyOfF,
              slotKeyOf, hs, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_mk,
              StateT.run_bind, StateT.run_get, pure_bind, Bool.false_or, hch, Bool.false_eq_true,
              hcs, StateT.run_pure, bind_map_left, bind_assoc]
            cases hlk : (st a.1).table.lookup a.2.2.salt with
            | some mk =>
              simp only [pure_bind]
              exact ih _ _
            | none =>
              simp only [bind_map_left]
              exact WireHop.bind_apply_le_add_true _ _ _ _ x fun mk => ih _ _
          · simp only [slotLift_inr, slotLiftOtcca, slotSaltImpl, multiSaltFlagNF, mKeyOfF,
              slotKeyOf, hs, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_mk,
              StateT.run_bind, StateT.run_get, pure_bind, Bool.false_or, hch, Bool.false_eq_true,
              hcs, StateT.run_modify, StateT.run_pure, bind_map_left, bind_assoc]
            have hstep : ∀ (mk : DerivedMessageKeys) (st' : MSaltSt Pt),
                𝒟[(simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf false))
                    (k ((lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e))).run st' >>=
                  fun z => post z.1] {x} ≤
                𝒟[(simulateQ (multiSaltFlagNF C codec ℓ encT idOf) (k none)).run
                    (st', (hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2) >>=
                  fun z => post z.1] {x} +
                𝒟[(fun z => z.2.2) <$>
                  (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) (k none)).run
                    (st', (hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)]
                  {true} := by
              intro mk st'
              rcases htag :
                ((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)
              · rw [lAeadK_dec_eq_none_of_tag_false C codec ℓ encT idOf mk a e htag]
                exact ih none st'
              · refine le_trans (EtMProof.apply_le_one _ _) (le_trans (le_of_eq ?_) le_add_self)
                have hf := multiSaltFlagNF_flag_or C codec ℓ encT idOf (k none) st' true
                rw [hf, Functor.map_map, map_eq_bind_pure_comp]
                exact (EtMProof.const_true_eq_one _).symm
            cases hlk : (st a.1).table.lookup a.2.2.salt with
            | some mk =>
              simp only [pure_bind]
              exact hstep mk _
            | none =>
              simp only [bind_map_left]
              exact WireHop.bind_apply_le_add_true _ _ _ _ x fun mk => hstep mk _

def mKeyOfLazy (i₀ : ℕ) (s₀ : Salt32) (i : ℕ) (salt : Salt32) :
    StateT ((MSaltSt Pt × Bool) × Option DerivedMessageKeys) ProbComp DerivedMessageKeys :=
  if i = i₀ ∧ salt = s₀ then getSlotKey else WireHop.onH (mKeyOfF i salt)

omit [DecidableEq Pt] in
theorem rc_mKeyOfLazy (i₀ : ℕ) (s₀ : Salt32) (i : ℕ) (salt : Salt32) :
    RC (fillKey (H := MSaltSt Pt × Bool))
      (mKeyOfLazy i₀ s₀ i salt) (mKeyOfLazy i₀ s₀ i salt) := by
  unfold mKeyOfLazy
  split_ifs
  · exact rc_getSlotKey_self
  · exact rc_onH _

/-- Variant of `multiSaltFlagNF` storing the key for a distinguished `(i₀, s₀)` in a separate lazy slot. -/
def multiSaltLazy (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (i₀ : ℕ) (s₀ : Salt32) :
    QueryImpl (QSpecS Pt ℓ) (StateT ((MSaltSt Pt × Bool) × Option DerivedMessageKeys) ProbComp)
  | .inl n => WireHop.onH (EtMProof.coin n)
  | .inr (.inl ⟨a, m⟩) => do
    let s ← WireHop.onH get
    if (s.1 a.1).chal.isSome then return none
    let mk ← mKeyOfLazy i₀ s₀ a.1 a.2.2.salt
    let e := (lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m
    WireHop.onH (modify fun (st, f) =>
      (Function.update st a.1 { (st a.1) with chal := some (a, e) }, f))
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if e.2 ≠ a.2.2.salt then return none
    let s ← WireHop.onH get
    if (s.1 a.1).chal == some (a, e) then return none
    let mk ← mKeyOfLazy i₀ s₀ a.1 a.2.2.salt
    if isChalSalt (s.1 a.1).chal a.2.2.salt then
      return (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e
    else
      WireHop.onH (modify fun (st, f) =>
        (st, f || ((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)))
      return none

theorem multiSaltLazy_rc (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (i₀ : ℕ) (s₀ : Salt32)
    (t : (QSpecS Pt ℓ).Domain) :
    RC (fillKey (H := MSaltSt Pt × Bool))
      (multiSaltLazy C codec ℓ encT idOf i₀ s₀ t)
      (multiSaltLazy C codec ℓ encT idOf i₀ s₀ t) := by
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · exact rc_onH _
  · refine (rc_onH _).bind fun s => ?_
    by_cases hc : (s.1 a.1).chal.isSome = true
    · simp only [hc, ↓reduceIte]
      exact RC.pure (idem_fillKey (H := MSaltSt Pt × Bool)) none
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact (rc_mKeyOfLazy i₀ s₀ a.1 a.2.2.salt).bind fun _ =>
        (rc_onH _).bind fun _ => RC.pure (idem_fillKey (H := MSaltSt Pt × Bool)) _
  · by_cases hs : e.2 ≠ a.2.2.salt
    · simp only [multiSaltLazy, hs, ne_eq, not_false_eq_true, ↓reduceIte]
      exact RC.pure (idem_fillKey (H := MSaltSt Pt × Bool)) none
    · simp only [multiSaltLazy, hs, ↓reduceIte]
      refine (rc_onH _).bind fun s => ?_
      by_cases hch : ((s.1 a.1).chal == some (a, e)) = true
      · simp only [hch, ↓reduceIte]
        exact RC.pure (idem_fillKey (H := MSaltSt Pt × Bool)) none
      · simp only [hch, Bool.false_eq_true, ↓reduceIte]
        refine (rc_mKeyOfLazy i₀ s₀ a.1 a.2.2.salt).bind fun _ => ?_
        by_cases hcs : isChalSalt (s.1 a.1).chal a.2.2.salt = true
        · simp only [hcs, ↓reduceIte]
          exact RC.pure (idem_fillKey (H := MSaltSt Pt × Bool)) _
        · simp only [hcs, Bool.false_eq_true, ↓reduceIte]
          exact (rc_onH _).bind fun _ => RC.pure (idem_fillKey (H := MSaltSt Pt × Bool)) none

/-- Synchronization invariant between `multiSaltFlagNF` and `multiSaltLazy i₀ s₀`. -/
structure MSaltLazySync (i₀ : ℕ) (s₀ : Salt32) (st₁ st₂ : MSaltSt Pt) (sl : Option DerivedMessageKeys) :
    Prop where
  other_slot : ∀ i, i ≠ i₀ → st₁ i = st₂ i
  chal_self : (st₁ i₀).chal = (st₂ i₀).chal
  lk_self : (st₁ i₀).table.lookup s₀ = sl
  lk_other : ∀ s, s ≠ s₀ → (st₁ i₀).table.lookup s = (st₂ i₀).table.lookup s

omit [DecidableEq Pt] in
theorem MSaltLazySync.chal_eq {i₀ : ℕ} {s₀ : Salt32} {st₁ st₂ : MSaltSt Pt} {sl : Option DerivedMessageKeys}
    (h : MSaltLazySync i₀ s₀ st₁ st₂ sl) (i : ℕ) :
    (st₁ i).chal = (st₂ i).chal := by
  by_cases hi : i = i₀
  · subst hi; exact h.chal_self
  · rw [h.other_slot i hi]

omit [DecidableEq Pt] in
theorem MSaltLazySync.upd_chal {i₀ : ℕ} {s₀ : Salt32} {st₁ st₂ : MSaltSt Pt} {sl : Option DerivedMessageKeys}
    (h : MSaltLazySync i₀ s₀ st₁ st₂ sl) (i : ℕ) (ch : ChalState Pt) :
    MSaltLazySync i₀ s₀
      (Function.update st₁ i { (st₁ i) with chal := ch })
      (Function.update st₂ i { (st₂ i) with chal := ch }) sl := by
  refine ⟨fun j hj => ?_, ?_, ?_, fun s hs => ?_⟩
  · by_cases hij : j = i
    · subst hij; simp [h.other_slot j hj]
    · simp [Function.update_of_ne hij, h.other_slot j hj]
  · by_cases hi : i = i₀
    · subst hi; simp
    · simp [Function.update_of_ne (Ne.symm hi), h.chal_self]
  · by_cases hi : i = i₀
    · subst hi; simp [h.lk_self]
    · simp [Function.update_of_ne (Ne.symm hi), h.lk_self]
  · by_cases hi : i = i₀
    · subst hi; simp [h.lk_other s hs]
    · simp [Function.update_of_ne (Ne.symm hi), h.lk_other s hs]

omit [DecidableEq Pt] in
theorem mKeyOfF_run_bind_eq (i₀ : ℕ) (s₀ : Salt32) (i : ℕ) (salt : Salt32) {β : Type}
    (st₁ st₂ : MSaltSt Pt) (fl : Bool) (sl : Option DerivedMessageKeys)
    (hsync : MSaltLazySync i₀ s₀ st₁ st₂ sl)
    (k₁ : DerivedMessageKeys × (MSaltSt Pt × Bool) → ProbComp β)
    (k₂ : DerivedMessageKeys × ((MSaltSt Pt × Bool) × Option DerivedMessageKeys) → ProbComp β)
    (hk : ∀ mk st₁' st₂' sl',
      MSaltLazySync i₀ s₀ st₁' st₂' sl' →
      k₁ (mk, (st₁', fl)) = k₂ (mk, ((st₂', fl), sl'))) :
    ((mKeyOfF i salt).run (st₁, fl) >>= k₁) =
      ((mKeyOfLazy i₀ s₀ i salt).run ((st₂, fl), sl) >>= k₂) := by
  unfold mKeyOfLazy mKeyOfF slotKeyOf
  by_cases hi : i = i₀
  · subst hi
    by_cases hs : salt = s₀
    · subst hs
      simp only [and_self, ↓reduceIte, getSlotKey, StateT.run_mk, hsync.lk_self, bind_map_left]
      cases sl with
      | some mk =>
        simp only [pure_bind, Function.update_eq_self]
        exact hk mk st₁ st₂ (some mk) hsync
      | none =>
        simp only [bind_map_left]
        refine congrArg (Bind.bind (m := ProbComp) _) (funext fun mk => ?_)
        refine hk mk
          (Function.update st₁ i { (st₁ i) with table := (salt, mk) :: (st₁ i).table })
          st₂ (some mk) ⟨fun j hj => ?_, by simp [hsync.chal_self], by simp, fun s hs_ne => ?_⟩
        · simp [Function.update_of_ne hj, hsync.other_slot j hj]
        · simp [List.lookup, beq_eq_false_iff_ne.mpr hs_ne, hsync.lk_other s hs_ne]
    · have hlk_eq : (st₁ i).table.lookup salt = (st₂ i).table.lookup salt := hsync.lk_other salt hs
      simp only [hs, and_false, ↓reduceIte, WireHop.onH, StateT.run_mk, hlk_eq, bind_map_left]
      cases hlk : (st₂ i).table.lookup salt with
      | some mk =>
        simp only [pure_bind, Function.update_eq_self]
        exact hk mk st₁ st₂ sl hsync
      | none =>
        simp only [bind_map_left]
        refine congrArg (Bind.bind (m := ProbComp) _) (funext fun mk => ?_)
        refine hk mk
          (Function.update st₁ i { (st₁ i) with table := (salt, mk) :: (st₁ i).table })
          (Function.update st₂ i { (st₂ i) with table := (salt, mk) :: (st₂ i).table })
          sl ⟨fun j hj => ?_, by simp [hsync.chal_self], ?_, fun s hs_ne => ?_⟩
        · simp [Function.update_of_ne hj, hsync.other_slot j hj]
        · simp [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm hs), hsync.lk_self]
        · simp only [Function.update_self, List.lookup]
          by_cases hs' : (s == salt) = true
          · simp [hs']
          · simp [hs', hsync.lk_other s hs_ne]
  · have hst_i : st₁ i = st₂ i := hsync.other_slot i hi
    simp only [hi, false_and, ↓reduceIte, WireHop.onH, StateT.run_mk, hst_i, bind_map_left]
    cases hlk : (st₂ i).table.lookup salt with
    | some mk =>
      simp only [pure_bind, Function.update_eq_self]
      rw [← hst_i, Function.update_eq_self]
      exact hk mk st₁ st₂ sl hsync
    | none =>
      simp only [bind_map_left]
      refine congrArg (Bind.bind (m := ProbComp) _) (funext fun mk => ?_)
      refine hk mk
        (Function.update st₁ i { (st₂ i) with table := (salt, mk) :: (st₂ i).table })
        (Function.update st₂ i { (st₂ i) with table := (salt, mk) :: (st₂ i).table })
        sl ⟨fun j hj => ?_, ?_, ?_, fun s hs_ne => ?_⟩
      · by_cases hij : j = i
        · subst hij; simp
        · simp [Function.update_of_ne hij, hsync.other_slot j hj]
      · simp [Function.update_of_ne (Ne.symm hi), hsync.chal_self]
      · simp [Function.update_of_ne (Ne.symm hi), hsync.lk_self]
      · simp [Function.update_of_ne (Ne.symm hi), hsync.lk_other s hs_ne]

theorem multiSaltFlagNF_eq_multiSaltLazy (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (i₀ : ℕ) (s₀ : Salt32)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α) :
    ∀ (st₁ st₂ : MSaltSt Pt) (fl : Bool) (sl : Option DerivedMessageKeys),
      MSaltLazySync i₀ s₀ st₁ st₂ sl →
      (fun z : α × MSaltSt Pt × Bool => (z.1, z.2.2)) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st₁, fl) =
      (fun z : α × (MSaltSt Pt × Bool) × Option DerivedMessageKeys => (z.1, z.2.1.2)) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf i₀ s₀) oa).run ((st₂, fl), sl) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st₁ st₂ fl sl _; simp
  | query_bind q k ih =>
    intro st₁ st₂ fl sl hsync
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, EtMProof.coin,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_mk, StateT.run_monadLift,
        bind_map_left, bind_assoc, pure_bind]
      exact congrArg (Bind.bind (m := ProbComp) _) (funext fun u => ih u st₁ st₂ fl sl hsync)
    · by_cases hc : (st₂ a.1).chal.isSome = true
      · have hc₁ : (st₁ a.1).chal.isSome = true := hsync.chal_eq a.1 ▸ hc
        simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, StateT.run_mk, StateT.run_bind,
          StateT.run_get, pure_bind, hc, hc₁, ↓reduceIte, StateT.run_pure, map_pure]
        exact ih none st₁ st₂ fl sl hsync
      · have hc₁ : (st₁ a.1).chal.isSome = false :=
          hsync.chal_eq a.1 ▸ Bool.eq_false_iff.mpr hc
        simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, StateT.run_mk, StateT.run_bind,
          StateT.run_get, pure_bind, hc, hc₁, Bool.false_eq_true, ↓reduceIte, StateT.run_modify,
          StateT.run_pure, map_pure, bind_assoc]
        refine mKeyOfF_run_bind_eq i₀ s₀ a.1 a.2.2.salt st₁ st₂ fl sl hsync _ _
          fun mk st₁' st₂' sl' hsync' => ?_
        exact ih _ _ _ fl sl' (hsync'.upd_chal a.1 _)
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [multiSaltLazy, multiSaltFlagNF, hs, ne_eq, not_false_eq_true, ↓reduceIte,
          StateT.run_pure, pure_bind]
        exact ih none st₁ st₂ fl sl hsync
      · by_cases hch : ((st₂ a.1).chal == some (a, e)) = true
        · have hch₁ : ((st₁ a.1).chal == some (a, e)) = true := hsync.chal_eq a.1 ▸ hch
          simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, hs, ↓reduceIte, StateT.run_mk,
            StateT.run_bind, StateT.run_get, pure_bind, hch, hch₁, StateT.run_pure, map_pure]
          exact ih none st₁ st₂ fl sl hsync
        · have hch₁ : ((st₁ a.1).chal == some (a, e)) = false :=
            hsync.chal_eq a.1 ▸ Bool.eq_false_iff.mpr hch
          simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, hs, ↓reduceIte, StateT.run_mk,
            StateT.run_bind, StateT.run_get, map_pure, pure_bind, hch, hch₁, Bool.false_eq_true,
            bind_assoc]
          refine mKeyOfF_run_bind_eq i₀ s₀ a.1 a.2.2.salt st₁ st₂ fl sl hsync _ _
            fun mk st₁' st₂' sl' hsync' => ?_
          by_cases hcs : isChalSalt (st₂ a.1).chal a.2.2.salt = true
          · have hcs₁ : isChalSalt (st₁ a.1).chal a.2.2.salt = true := hsync.chal_eq a.1 ▸ hcs
            simp only [hcs, hcs₁, ↓reduceIte, StateT.run_pure, pure_bind]
            exact ih _ st₁' st₂' fl sl' hsync'
          · have hcs₁ : isChalSalt (st₁ a.1).chal a.2.2.salt = false :=
              hsync.chal_eq a.1 ▸ Bool.eq_false_iff.mpr hcs
            simp only [hcs, hcs₁, Bool.false_eq_true, ↓reduceIte, StateT.run_modify, map_pure]
            exact ih none st₁' st₂' _ sl' hsync'

theorem multiSaltFlagNF_prepopulate_flag (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (i₀ : ℕ) (s₀ : Salt32)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (st : MSaltSt Pt) (fl : Bool) (hlk : (st i₀).table.lookup s₀ = none) :
    𝒟[do
      let k₀ ← $ᵗ DerivedMessageKeys
      (fun z : α × MSaltSt Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run
          (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table }, fl)] =
    𝒟[(fun z : α × MSaltSt Pt × Bool => z.2.2) <$>
      (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, fl)] := by
  have h1 : ∀ k₀ : DerivedMessageKeys,
      (fun z : α × MSaltSt Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run
          (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table }, fl) =
      (fun z : α × (MSaltSt Pt × Bool) × Option DerivedMessageKeys => z.2.1.2) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf i₀ s₀) oa).run ((st, fl), some k₀) := by
    intro k₀
    have h := congrArg (Prod.snd <$> ·)
      (multiSaltFlagNF_eq_multiSaltLazy C codec ℓ encT idOf i₀ s₀ oa
        (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table })
        st fl (some k₀)
        ⟨fun i hi => by simp [Function.update_of_ne hi], by simp, by simp,
          fun s hs => by simp [List.lookup, beq_eq_false_iff_ne.mpr hs]⟩)
    simpa only [Functor.map_map] using h
  have h2 :
      (fun z : α × MSaltSt Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, fl) =
      (fun z : α × (MSaltSt Pt × Bool) × Option DerivedMessageKeys => z.2.1.2) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf i₀ s₀) oa).run ((st, fl), none) := by
    have h := congrArg (Prod.snd <$> ·)
      (multiSaltFlagNF_eq_multiSaltLazy C codec ℓ encT idOf i₀ s₀ oa st st fl none
        ⟨fun _ _ => rfl, rfl, hlk, fun _ _ => rfl⟩)
    simpa only [Functor.map_map] using h
  simp only [h1, h2]
  have hlz := evalDist_eager_eq_lazy
    (multiSaltLazy C codec ℓ encT idOf i₀ s₀)
    (multiSaltLazy C codec ℓ encT idOf i₀ s₀)
    (multiSaltLazy_rc C codec ℓ encT idOf i₀ s₀) oa (st, fl) (fun _ h => pure h.2)
  simpa [map_eq_bind_pure_comp] using hlz

theorem multiSaltFlagNF_prepopulate_out (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (i₀ : ℕ) (s₀ : Salt32)
    (oa : OracleComp (QSpecS Pt ℓ) Bool)
    (st : MSaltSt Pt) (fl : Bool) (hlk : (st i₀).table.lookup s₀ = none) :
    𝒟[do
      let k₀ ← $ᵗ DerivedMessageKeys
      (fun z : Bool × MSaltSt Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run
          (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table }, fl)] =
    𝒟[(fun z : Bool × MSaltSt Pt × Bool => z.1) <$>
      (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, fl)] := by
  have h1 : ∀ k₀ : DerivedMessageKeys,
      (fun z : Bool × MSaltSt Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run
          (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table }, fl) =
      (fun z : Bool × (MSaltSt Pt × Bool) × Option DerivedMessageKeys => z.1) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf i₀ s₀) oa).run ((st, fl), some k₀) := by
    intro k₀
    have h := congrArg (Prod.fst <$> ·)
      (multiSaltFlagNF_eq_multiSaltLazy C codec ℓ encT idOf i₀ s₀ oa
        (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table })
        st fl (some k₀)
        ⟨fun i hi => by simp [Function.update_of_ne hi], by simp, by simp,
          fun s hs => by simp [List.lookup, beq_eq_false_iff_ne.mpr hs]⟩)
    simpa only [Functor.map_map] using h
  have h2 :
      (fun z : Bool × MSaltSt Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, fl) =
      (fun z : Bool × (MSaltSt Pt × Bool) × Option DerivedMessageKeys => z.1) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf i₀ s₀) oa).run ((st, fl), none) := by
    have h := congrArg (Prod.fst <$> ·)
      (multiSaltFlagNF_eq_multiSaltLazy C codec ℓ encT idOf i₀ s₀ oa st st fl none
        ⟨fun _ _ => rfl, rfl, hlk, fun _ _ => rfl⟩)
    simpa only [Functor.map_map] using h
  rw [h2]
  simp only [h1]
  have hlz := evalDist_eager_eq_lazy
    (multiSaltLazy C codec ℓ encT idOf i₀ s₀)
    (multiSaltLazy C codec ℓ encT idOf i₀ s₀)
    (multiSaltLazy_rc C codec ℓ encT idOf i₀ s₀) oa (st, fl) (fun b' _ => pure b')
  simpa [map_eq_bind_pure_comp] using hlz

/-- Invariant on `SaltSlotSt`: `table` is empty before the challenge query and restricted to `a₀.2.2.salt` afterwards. -/
def SaltSlotTableInv (sst : SaltSlotSt Pt) : Prop :=
  match sst.chal with
  | none => sst.table = []
  | some (a₀, _) => ∀ s, s ≠ a₀.2.2.salt → sst.table.lookup s = none

def MSaltTableInv (st : MSaltSt Pt) : Prop :=
  ∀ i, SaltSlotTableInv (st i)

omit [DecidableEq Pt] in
theorem MSaltTableInv.init : MSaltTableInv (fun _ : ℕ => ({} : SaltSlotSt Pt)) :=
  fun _ => rfl

omit [DecidableEq Pt] in
theorem MSaltTableInv.lookup_eq_none_of_isChalSalt_false {st : MSaltSt Pt}
    (hinv : MSaltTableInv st) (i : ℕ) {s : Salt32}
    (hcs : isChalSalt (st i).chal s = false) :
    (st i).table.lookup s = none := by
  have hi := hinv i
  unfold SaltSlotTableInv at hi
  unfold isChalSalt at hcs
  cases hch : (st i).chal with
  | none => rw [hch] at hi; simp [hi]
  | some p =>
    rcases p with ⟨a₀, e₀⟩
    rw [hch] at hi hcs
    exact hi s (beq_eq_false_iff_ne.mp hcs)

omit [DecidableEq Pt] in
theorem MSaltTableInv.lookup_eq_none_of_isSome_false {st : MSaltSt Pt}
    (hinv : MSaltTableInv st) {i : ℕ} (hc : (st i).chal.isSome = false) (s : Salt32) :
    (st i).table.lookup s = none := by
  have hi := hinv i
  unfold SaltSlotTableInv at hi
  cases hch : (st i).chal with
  | none => rw [hch] at hi; simp [hi]
  | some _ => rw [hch] at hc; cases hc

omit [DecidableEq Pt] in
theorem MSaltTableInv.enc_step {st : MSaltSt Pt} (a : AD Pt) (e : Ct) (mk : DerivedMessageKeys)
    (hinv : MSaltTableInv st) (hc : (st a.1).chal.isSome = false) :
    MSaltTableInv (Function.update st a.1
      { chal := some (a, e), table := (a.2.2.salt, mk) :: (st a.1).table }) := by
  intro i
  by_cases hi : i = a.1
  · subst hi
    have ha := hinv a.1
    unfold SaltSlotTableInv at ha ⊢
    simp only [Function.update_self]
    cases hch : (st a.1).chal with
    | none =>
      rw [hch] at ha
      intro s hs
      simp [ha, List.lookup, beq_eq_false_iff_ne.mpr hs]
    | some _ => rw [hch] at hc; cases hc
  · simpa [Function.update_of_ne hi] using hinv i

omit [DecidableEq Pt] in
theorem MSaltTableInv.dec_chal_step {st : MSaltSt Pt} (i : ℕ) {salt : Salt32} (mk : DerivedMessageKeys)
    (hinv : MSaltTableInv st) (hcs : isChalSalt (st i).chal salt = true) :
    MSaltTableInv (Function.update st i { (st i) with table := (salt, mk) :: (st i).table }) := by
  intro j
  by_cases hj : j = i
  · subst hj
    have hi := hinv j
    unfold SaltSlotTableInv at hi ⊢
    unfold isChalSalt at hcs
    simp only [Function.update_self]
    cases hch : (st j).chal with
    | none => rw [hch] at hcs; cases hcs
    | some p =>
      rcases p with ⟨a₀, e₀⟩
      rw [hch] at hi hcs
      have hsalt : salt = a₀.2.2.salt := beq_iff_eq.mp hcs
      subst hsalt
      intro s hs
      simp [List.lookup, beq_eq_false_iff_ne.mpr hs, hi s hs]
  · simpa [Function.update_of_ne hj] using hinv j

theorem multiSaltFlagNF_flag_le_aux (C : Crypto) (codec : SignalMessageProtoCodec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {oa : OracleComp (QSpecS Pt ℓ) Bool}
    (hdec : GuardedSafe.GuardedSafePost otRespShort otDecLong (fun _ => True) oa) :
    ∀ (qd : ℕ) (st : MSaltSt Pt),
      MSaltTableInv st →
      AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) oa →
      oa.IsQueryBoundP (fun q => isDecQuery q = true) qd →
      𝒟[(fun z : Bool × MSaltSt Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, false)] {true} ≤
        (qd : ℝ≥0∞) * macForgeryProb C.F := by
  induction hdec with
  | pure _ =>
    intro qd st _ _ _
    simp
  | @query_bind q k hnotlong _ ih =>
    intro qd st hinv hshort hq
    rw [AEADScheme.OTEncADsOk, isQueryBoundP_query_bind_iff] at hshort
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [multiSaltFlagNF, EtMProof.coin, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_monadLift, bind_assoc, pure_bind]
      refine EtMProof.bind_le_of_support ($ᵗ (Fin (n + 1))) _ (measurableSet_singleton true)
        fun u _ => ?_
      have hk := hq.2 u
      simp only [isDecQuery, Bool.false_eq_true, ↓reduceIte] at hk
      have hnb : ¬ (AEADScheme.otEncBad (M := Plain ℓ) (C := Ct) (fun a : AD Pt => a.2.2.shortB) (.inl n) = true) := by
        simp [AEADScheme.otEncBad]
      have hsh_u : AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) (k u) := by
        simpa only [AEADScheme.OTEncADsOk, hnb, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using hshort.2 u
      exact ih u trivial qd st hinv hsh_u hk
    · have ha_ok : a.2.2.shortB = true := by
        have := hshort.1.resolve_right (Nat.not_lt_zero 0)
        simpa [AEADScheme.otEncBad] using this
      have hnb : ¬ (AEADScheme.otEncBad (M := Plain ℓ) (C := Ct) (fun a : AD Pt => a.2.2.shortB) (.inr (.inl ⟨a, m⟩)) = true) := by
        simp [AEADScheme.otEncBad, ha_ok]
      by_cases hc : (st a.1).chal.isSome = true
      · have hk_none := hq.2 none
        simp only [isDecQuery, Bool.false_eq_true, ↓reduceIte] at hk_none
        have hsh_none : AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) (k none) := by
          simpa only [AEADScheme.OTEncADsOk, hnb, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using hshort.2 none
        simp only [multiSaltFlagNF, StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte,
          StateT.run_pure]
        exact ih none (by rintro _ ⟨⟩) qd st hinv hsh_none hk_none
      · have hcf : (st a.1).chal.isSome = false := Bool.eq_false_iff.mpr hc
        have hlk : (st a.1).table.lookup a.2.2.salt = none :=
          hinv.lookup_eq_none_of_isSome_false hcf a.2.2.salt
        simp only [multiSaltFlagNF, mKeyOfF, slotKeyOf, StateT.run_bind, StateT.run_get,
          StateT.run_mk, pure_bind, hcf, Bool.false_eq_true, ↓reduceIte, hlk, StateT.run_modify,
          StateT.run_pure, Functor.map_map, bind_map_left, bind_assoc,
          Function.update_self, Function.update_idem]
        refine EtMProof.bind_le_of_support ($ᵗ DerivedMessageKeys) _ (measurableSet_singleton true)
          fun mk _ => ?_
        have hk_some := hq.2 (some ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m))
        simp only [isDecQuery, Bool.false_eq_true, ↓reduceIte] at hk_some
        have hsh_some : AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB)
            (k (some ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m))) := by
          simpa only [AEADScheme.OTEncADsOk, hnb, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using
            hshort.2 (some ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m))
        have hresp : otRespShort (AD := AD Pt) (M := Plain ℓ) (.inr (.inl ⟨a, m⟩))
            (some ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m)) := by
          rintro _ ⟨rfl⟩
          exact ProstMsgAeadCorrect.lAeadK_enc_length_lt C codec hfit ℓ hℓ encT idOf mk
            ((a.1, a.2.1), a.2.2) m ha_ok
        exact ih _ hresp qd _ (hinv.enc_step a _ mk hcf) hsh_some hk_some
    · have he_lt : e.1.1.length < 2 ^ 32 := Classical.not_not.mp hnotlong
      have hpos : 0 < qd := hq.1.resolve_left (by simp [isDecQuery])
      have hk_none := hq.2 none
      simp only [isDecQuery, ↓reduceIte] at hk_none
      have hnb : ¬ (AEADScheme.otEncBad (M := Plain ℓ) (C := Ct) (fun a : AD Pt => a.2.2.shortB) (.inr (.inr ⟨a, e⟩)) = true) := by
        simp [AEADScheme.otEncBad]
      have hsh_r : ∀ r, AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) (k r) := fun r => by
        simpa only [AEADScheme.OTEncADsOk, hnb, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using hshort.2 r
      have hle_cast : ((qd - 1 : ℕ) : ℝ≥0∞) * macForgeryProb C.F ≤
          (qd : ℝ≥0∞) * macForgeryProb C.F := by
        gcongr
        exact Nat.sub_le qd 1
      by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [multiSaltFlagNF, hs, ne_eq, not_false_eq_true, ↓reduceIte, StateT.run_pure,
          pure_bind]
        exact (ih none trivial (qd - 1) st hinv (hsh_r none) hk_none).trans hle_cast
      · by_cases hch : ((st a.1).chal == some (a, e)) = true
        · simp only [multiSaltFlagNF, hs, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
            hch, StateT.run_pure]
          exact (ih none trivial (qd - 1) st hinv (hsh_r none) hk_none).trans hle_cast
        · by_cases hcs : isChalSalt (st a.1).chal a.2.2.salt = true
          · simp only [multiSaltFlagNF, mKeyOfF, slotKeyOf, hs, ↓reduceIte, StateT.run_bind,
              StateT.run_get, StateT.run_mk, pure_bind, hch, Bool.false_eq_true, hcs,
              StateT.run_pure, bind_map_left, bind_assoc]
            cases hlk : (st a.1).table.lookup a.2.2.salt with
            | some mk =>
              simp only [pure_bind, Function.update_eq_self]
              have hk_dec := hq.2 ((lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e)
              simp only [isDecQuery, ↓reduceIte] at hk_dec
              exact (ih _ trivial (qd - 1) st hinv (hsh_r _) hk_dec).trans hle_cast
            | none =>
              simp only [bind_map_left]
              refine (EtMProof.bind_le_of_support ($ᵗ DerivedMessageKeys) _ (measurableSet_singleton true)
                fun mk _ => ?_).trans hle_cast
              have hk_dec := hq.2 ((lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e)
              simp only [isDecQuery, ↓reduceIte] at hk_dec
              exact ih _ trivial (qd - 1) _ (hinv.dec_chal_step a.1 mk hcs) (hsh_r _) hk_dec
          · have hcsf : isChalSalt (st a.1).chal a.2.2.salt = false := Bool.eq_false_iff.mpr hcs
            have hlk : (st a.1).table.lookup a.2.2.salt = none :=
              hinv.lookup_eq_none_of_isChalSalt_false a.1 hcsf
            simp only [multiSaltFlagNF, mKeyOfF, slotKeyOf, hs, ↓reduceIte, StateT.run_bind,
              StateT.run_get, StateT.run_mk, pure_bind, hch, Bool.false_eq_true, hcsf, hlk,
              StateT.run_modify, StateT.run_pure, Functor.map_map, bind_map_left, bind_assoc,
              Bool.false_or]
            have hstep : 𝒟[do
                let mk ← $ᵗ DerivedMessageKeys
                (fun z : Bool × MSaltSt Pt × Bool => z.2.2) <$>
                  (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) (k none)).run
                    (Function.update st a.1 { (st a.1) with table := (a.2.2.salt, mk) :: (st a.1).table },
                      (hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)]
                {true} ≤
                macForgeryProb C.F + ((qd - 1 : ℕ) : ℝ≥0∞) * macForgeryProb C.F := by
              have hor : (do
                  let mk ← $ᵗ DerivedMessageKeys
                  (fun z : Bool × MSaltSt Pt × Bool => z.2.2) <$>
                    (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) (k none)).run
                      (Function.update st a.1 { (st a.1) with table := (a.2.2.salt, mk) :: (st a.1).table },
                        (hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)) =
                (do
                  let mk ← $ᵗ DerivedMessageKeys
                  (((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2) || ·) <$>
                    ((fun z : Bool × MSaltSt Pt × Bool => z.2.2) <$>
                      (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) (k none)).run
                        (Function.update st a.1 { (st a.1) with table := (a.2.2.salt, mk) :: (st a.1).table },
                          false))) :=
                congrArg (Bind.bind (m := ProbComp) _) (funext fun mk =>
                  multiSaltFlagNF_flag_or C codec ℓ encT idOf (k none) _ _)
              rw [hor]
              refine (EtMProof.union_step ($ᵗ DerivedMessageKeys) _ _).trans (add_le_add
                (lForge_step_le C.F (lIds idOf a.2.1.1) e.1.1 he_lt e.1.2) ?_)
              have hprep := congrArg (fun μ => μ {true})
                (multiSaltFlagNF_prepopulate_flag C codec ℓ encT idOf a.1 a.2.2.salt (k none)
                  st false hlk)
              rw [hprep]
              exact ih none trivial (qd - 1) st hinv (hsh_r none) hk_none
            have hqd_eq : (qd : ℝ≥0∞) * macForgeryProb C.F =
                macForgeryProb C.F + ((qd - 1 : ℕ) : ℝ≥0∞) * macForgeryProb C.F := by
              have : qd = 1 + (qd - 1) := by omega
              conv_lhs => rw [this, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
            exact hqd_eq ▸ hstep

theorem evalDist_multiSaltFlagNF_out_eq_slotLift_slotSaltImplNF_aux (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (oa : OracleComp (QSpecS Pt ℓ) Bool) :
    ∀ (st : MSaltSt Pt) (fl : Bool),
      MSaltTableInv st →
      𝒟[(fun z : Bool × MSaltSt Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) oa).run (st, fl)] =
      𝒟[Prod.fst <$>
        (simulateQ (slotLift (slotSaltImplNF C codec ℓ encT idOf false)) oa).run st] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st fl _; simp
  | query_bind q k ih =>
    intro st fl hinv
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [multiSaltFlagNF, slotLift_inl, EtMProof.coin, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, bind_assoc, pure_bind]
      exact evalDist_bind_congr _ _ _ fun u => ih u st fl hinv
    · by_cases hc : (st a.1).chal.isSome = true
      · simp only [multiSaltFlagNF, slotLift_inr, slotLiftOtcca, slotSaltImplNF, StateT.run_mk,
          StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte, StateT.run_pure,
          Function.update_eq_self]
        exact ih none st fl hinv
      · have hcf : (st a.1).chal.isSome = false := Bool.eq_false_iff.mpr hc
        have hlk : (st a.1).table.lookup a.2.2.salt = none :=
          hinv.lookup_eq_none_of_isSome_false hcf a.2.2.salt
        simp only [multiSaltFlagNF, slotLift_inr, slotLiftOtcca, slotSaltImplNF, mKeyOfF,
          slotKeyOf, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, hcf,
          Bool.false_eq_true, ↓reduceIte, hlk, StateT.run_modify, StateT.run_pure,
          Functor.map_map, bind_map_left, bind_assoc, Function.update_self, Function.update_idem]
        exact evalDist_bind_congr ($ᵗ DerivedMessageKeys) _ _ fun mk =>
          ih _ _ fl (hinv.enc_step a _ mk hcf)
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [multiSaltFlagNF, slotLift_inr, slotLiftOtcca, slotSaltImplNF, hs, ne_eq,
          not_false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_pure, pure_bind,
          Function.update_eq_self]
        exact ih none st fl hinv
      · simp only [ne_eq, Decidable.not_not] at hs
        have his : isSlotChalSalt (st a.1).chal a.2.2.salt =
            isChalSalt (st a.1).chal a.2.2.salt := rfl
        by_cases hcs : isChalSalt (st a.1).chal a.2.2.salt = true
        · by_cases hch : ((st a.1).chal == some (a, e)) = true
          · simp only [multiSaltFlagNF, slotLift_inr, slotLiftOtcca, slotSaltImplNF, hs, ne_eq,
              not_true_eq_false, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get,
              pure_bind, his, hcs, Bool.not_true, Bool.false_or, hch, StateT.run_pure,
              Function.update_eq_self]
            exact ih none st fl hinv
          · simp only [multiSaltFlagNF, slotLift_inr, slotLiftOtcca, slotSaltImplNF, mKeyOfF,
              slotKeyOf, hs, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_mk, StateT.run_bind,
              StateT.run_get, pure_bind, his, hcs, Bool.not_true, Bool.false_or, hch,
              Bool.false_eq_true, StateT.run_pure, bind_map_left, bind_assoc]
            cases hlk : (st a.1).table.lookup a.2.2.salt with
            | some mk =>
              simp only [pure_bind, Function.update_eq_self]
              exact ih _ st fl hinv
            | none =>
              simp only [bind_map_left]
              exact evalDist_bind_congr ($ᵗ DerivedMessageKeys) _ _ fun mk =>
                ih _ _ fl (hinv.dec_chal_step a.1 mk hcs)
        · have hcsf : isChalSalt (st a.1).chal a.2.2.salt = false := Bool.eq_false_iff.mpr hcs
          have hchf : ((st a.1).chal == some (a, e)) = false :=
            chal_beq_false_of_isChalSalt_false hcsf
          have hlk : (st a.1).table.lookup a.2.2.salt = none :=
            hinv.lookup_eq_none_of_isChalSalt_false a.1 hcsf
          simp only [multiSaltFlagNF, slotLift_inr, slotLiftOtcca, slotSaltImplNF, mKeyOfF,
            slotKeyOf, hs, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_mk, StateT.run_bind,
            StateT.run_get, pure_bind, his, hcsf, Bool.not_false, Bool.false_or, Bool.true_or,
            hchf, Bool.false_eq_true, hlk, StateT.run_modify, StateT.run_pure, Functor.map_map,
            bind_map_left, bind_assoc, Function.update_eq_self]
          have hfl : (do
              let mk ← $ᵗ DerivedMessageKeys
              (fun z : Bool × MSaltSt Pt × Bool => z.1) <$>
                (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) (k none)).run
                  (Function.update st a.1 { (st a.1) with table := (a.2.2.salt, mk) :: (st a.1).table },
                    fl || ((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2))) =
            (do
              let mk ← $ᵗ DerivedMessageKeys
              (fun z : Bool × MSaltSt Pt × Bool => z.1) <$>
                (simulateQ (multiSaltFlagNF C codec ℓ encT idOf) (k none)).run
                  (Function.update st a.1 { (st a.1) with table := (a.2.2.salt, mk) :: (st a.1).table },
                    fl)) :=
            congrArg (Bind.bind (m := ProbComp) _) (funext fun mk =>
              (multiSaltFlagNF_out_fl C codec ℓ encT idOf (k none) _ _).trans
                (multiSaltFlagNF_out_fl C codec ℓ encT idOf (k none) _ fl).symm)
          rw [hfl, multiSaltFlagNF_prepopulate_out C codec ℓ encT idOf a.1 a.2.2.salt (k none)
            st fl hlk]
          exact ih none st fl hinv

/-- Bounds the `boolDist` between `slotLift (slotSaltImpl false)` and `slotLift (slotSaltImplNF false)` by `qd * macForgeryProb C.F`. -/
theorem multiSalt_false_boolDist_multiSaltNF_false (C : Crypto) (codec : SignalMessageProtoCodec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) {qd : ℕ}
    (hB : MakesAtMostDecQueries B qd)
    (hshort : AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) B)
    (hdec : GuardedOTDecShort B) :
    𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf false)) B).run
        (fun _ => {})].boolDist
      𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImplNF C codec ℓ encT idOf false)) B).run
        (fun _ => {})] ≤
      (qd : ℝ≥0∞) * macForgeryProb C.F := by
  rw [← evalDist_multiSaltFlagNF_out_eq_slotLift_slotSaltImplNF_aux C codec ℓ encT idOf B
    (fun _ => {}) false MSaltTableInv.init]
  refine Measure.boolDist_le_of_apply_le _ _ fun x => ?_
  simp only [map_eq_bind_pure_comp]
  exact (slotLift_slotSaltImpl_false_le_multiSaltFlagNF C codec ℓ encT idOf B pure x
    (fun _ => {})).trans
    (add_le_add le_rfl
      (multiSaltFlagNF_flag_le_aux C codec hfit ℓ hℓ encT idOf hdec qd (fun _ => {})
        MSaltTableInv.init hshort hB))

end CryptoGames.LibsignalSM.Proofs.SaltHop
