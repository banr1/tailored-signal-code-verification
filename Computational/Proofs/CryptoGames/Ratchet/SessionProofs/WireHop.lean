/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtM
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs

/-!
# Proofs of the wire hop (`lRandSaltBias_le` and `lWireRed_queries`)

**Checked by Lean.** Bounds the query count of `lWireRed` and proves `lRandSaltBias_le` by
coupling the multi-slot random-salt OT-CCA game with `wireOtccaGame` across the ideal and real
worlds.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.LibsignalSM.Proofs.WireHop

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD

variable {Pt : Type}

/-! ## Query bound `lWireRed_queries` -/

/-- State of `lWireRed`: seen salts, lazy key table, abort flag, and encryption-queried flag. -/
abbrev WRedSt := List Salt32 × List (Salt32 × DerivedMessageKeys) × Bool × Bool

def wSlot (ℓ : ℕ) (salt : Salt32) : StateT WRedSt (OracleComp (LibsignalWireOracleSpec ℓ)) ℕ := do
  let st ← get
  match st.1.idxOf? salt with
  | some n => return n
  | none => set (st.1 ++ [salt], st.2.1, st.2.2.1, st.2.2.2); return st.1.length

def wRedImpl [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ) :
    QueryImpl (unifSpec + otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT WRedSt (OracleComp (LibsignalWireOracleSpec ℓ))) := fun q =>
  let _ := (C, codec)
  match q with
  | .inl n => StateT.lift (query (spec := LibsignalWireOracleSpec ℓ) (.inl n))
  | .inr (.inl ⟨a, m⟩) => do
    if (← get).2.2.2 then return none
    let n ← wSlot ℓ a.2.2.salt
    modify fun st => (st.1, st.2.1, st.2.2.1, true)
    if n ≠ j then
      modify fun st => (st.1, st.2.1, true, st.2.2.2)
      return none
    let r ← StateT.lift (query (spec := LibsignalWireOracleSpec ℓ)
      (.inr (.inl (lIds idOf a.2.1.1, lHeader encT a.1 a.2.1 a.2.2, m))))
    return r.map fun w => (w, a.2.2.salt)
  | .inr (.inr ⟨a, e⟩) => do
    if !(← get).2.2.2 || e.2 ≠ a.2.2.salt then return none
    let n ← wSlot ℓ a.2.2.salt
    if n = j then
      let r ← StateT.lift (query (spec := LibsignalWireOracleSpec ℓ) (.inr (.inr (lIds idOf a.2.1.1, e.1))))
      return match r with
        | none => none
        | some (h, m) => if h = lHeader encT a.1 a.2.1 a.2.2 then some (padOrTruncatePlain ℓ m) else none
    else
      return none

theorem lWireRed_eq [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    (lWireRed C codec ℓ encT idOf j B : OracleComp (LibsignalWireOracleSpec ℓ) Bool) =
      ((simulateQ (wRedImpl C codec ℓ encT idOf j) B).run ([], [], false, false) >>= fun ⟨b', st⟩ =>
        if st.2.2.1 || (!st.2.2.2 && j ≠ 0) then
          (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (LibsignalWireOracleSpec ℓ) Bool)
        else pure b') := rfl

/-! ## Header injectivity and parse mismatch -/

/-- Under `hinj` and `hdum`, `lHeader` is injective on ADs sharing epoch `t` and salt `p.salt` with message index in `[1, 2 ^ 32]`. -/
theorem lHeader_inj {encT : Pt → PublicKey} (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) {a₁ a₂ : ℕ × (Header Pt × LibsignalMsgPublicPart)}
    (ht : a₁.2.1.1 = a₂.2.1.1) (hsalt : a₁.2.2.salt = a₂.2.2.salt)
    (hi₁ : 1 ≤ a₁.1 ∧ a₁.1 ≤ 2 ^ 32) (hi₂ : 1 ≤ a₂.1 ∧ a₂.1 ≤ 2 ^ 32)
    (hhdr : lHeader encT a₁.1 a₁.2.1 a₁.2.2 = lHeader encT a₂.1 a₂.2.1 a₂.2.2) :
    a₁ = a₂ := by
  rcases a₁ with ⟨i₁, ⟨t₁, T₁⟩, ⟨pn₁, pq₁, salt₁, addrs₁⟩⟩
  rcases a₂ with ⟨i₂, ⟨t₂, T₂⟩, ⟨pn₂, pq₂, salt₂, addrs₂⟩⟩
  dsimp only at ht hsalt hi₁ hi₂
  subst ht; subst hsalt
  simp only [lHeader, SignalHeader.mk.injEq] at hhdr
  rcases hhdr with ⟨_, hT, hcnt, rfl, rfl, rfl⟩
  have hTeq : T₁ = T₂ := by
    cases T₁ with
    | none =>
      cases T₂ with
      | none => rfl
      | some P₂ => exact absurd hT.symm (hdum P₂)
    | some P₁ =>
      cases T₂ with
      | none => exact absurd hT (hdum P₁)
      | some P₂ => exact congrArg some (hinj hT)
  subst hTeq
  have hieq : i₁ = i₂ := by
    have hbv := congrArg BitVec.toNat hcnt
    simp only [BitVec.toNat_ofNat] at hbv
    omega
  subst hieq
  rfl

/-- If `e.1` parses to `(h₀, body)` with `h₀ ≠ lHeader encT a.1 a.2.1 a.2.2`, then `lAeadK.dec` returns `none`. -/
theorem lAeadK_dec_eq_none_of_parse (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : DerivedMessageKeys)
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) (e : LibsignalCiphertextWithSalt32)
    (h₀ : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec codec).parse e.1.1 = some (h₀, body))
    (hne : h₀ ≠ lHeader encT a.1 a.2.1 a.2.2) :
    (lAeadK C codec ℓ encT idOf).dec k ((a.1, a.2.1), a.2.2) e = none := by
  simp only [lAeadK, lWire, libsignalWireAead, libsignalReceiveWire, hparse]
  cases cbcDecRaw C.D k.1.1 k.1.2 body with
  | none => split_ifs <;> rfl
  | some m =>
    simp only [addressCheckPasses]
    split_ifs <;> simp [hne]

/-! ## Lazy-slot combinators and branch decompositions -/

def fillKey {H : Type} (_ : H) : Option DerivedMessageKeys → ProbComp (Option DerivedMessageKeys)
  | some k => pure (some k)
  | none => some <$> ($ᵗ DerivedMessageKeys)

theorem idem_fillKey {H : Type} : Idem (fillKey (H := H)) := by
  intro h sl
  cases sl with
  | some k => exact DEq.of_eq (by simp [fillKey])
  | none => exact DEq.of_eq (by simp [fillKey, map_eq_bind_pure_comp, bind_assoc])

def onH {H α : Type} (m : StateT H ProbComp α) : StateT (H × Option DerivedMessageKeys) ProbComp α :=
  StateT.mk fun ⟨h, sl⟩ => (fun ⟨a, h'⟩ => (a, (h', sl))) <$> m.run h

def getSlotKey {H : Type} : StateT (H × Option DerivedMessageKeys) ProbComp DerivedMessageKeys :=
  StateT.mk fun ⟨h, sl⟩ =>
    match sl with
    | some k => pure (k, (h, some k))
    | none => (fun k => (k, (h, some k))) <$> ($ᵗ DerivedMessageKeys)

def readSlotKey {H : Type} : StateT (H × Option DerivedMessageKeys) ProbComp DerivedMessageKeys :=
  StateT.mk fun ⟨h, sl⟩ => pure (sl.getD default, (h, sl))

theorem rel_onH {H α : Type} (m : StateT H ProbComp α) :
    Rel (fillKey (H := H)) (onH m) (onH m) := by
  rintro ⟨h, sl⟩
  cases sl with
  | some k =>
    exact DEq.of_eq (by
      simp [fillSt, fillOut, fillKey, onH, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc])
  | none =>
    exact DEq.of_eq (by
      simp [fillSt, fillOut, fillKey, onH, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc])

theorem comm_onH {H α : Type} (m : StateT H ProbComp α) :
    Comm (fillKey (H := H)) (onH m) := by
  rintro ⟨h, sl⟩
  cases sl with
  | some k =>
    exact DEq.of_eq (by
      simp [fillSt, fillOut, fillKey, onH, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc])
  | none =>
    simp only [fillSt, fillOut, fillKey, onH, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_apply, bind_assoc, pure_bind]
    exact DEq.swap ($ᵗ DerivedMessageKeys) (m.run h) fun k z => pure (z.1, (z.2, some k))

theorem rc_onH {H α : Type} (m : StateT H ProbComp α) :
    RC (fillKey (H := H)) (onH m) (onH m) :=
  ⟨rel_onH m, comm_onH m⟩

theorem rc_getSlotKey {H : Type} :
    RC (fillKey (H := H)) getSlotKey readSlotKey := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h, sl⟩
    cases sl with
    | some k =>
      exact DEq.of_eq (by
        simp [fillSt, fillOut, fillKey, getSlotKey, readSlotKey, StateT.run_mk,
          map_eq_bind_pure_comp])
    | none =>
      exact DEq.of_eq (by
        simp [fillSt, fillOut, fillKey, getSlotKey, readSlotKey, StateT.run_mk,
          map_eq_bind_pure_comp, bind_assoc])
  · rintro ⟨h, sl⟩
    cases sl with
    | some k =>
      exact DEq.of_eq (by
        simp [fillSt, fillOut, fillKey, getSlotKey, StateT.run_mk,
          map_eq_bind_pure_comp])
    | none =>
      exact DEq.of_eq (by
        simp [fillSt, fillOut, fillKey, getSlotKey, StateT.run_mk,
          map_eq_bind_pure_comp, bind_assoc])

theorem bind_fillOut_post {H S α : Type} (fill : H → S → ProbComp S)
    (y : ProbComp (α × (H × S))) (post : α → H → ProbComp Bool) :
    DEq (y >>= fillOut fill >>= fun z => post z.1 z.2.1)
      (y >>= fun z => post z.1 z.2.1) := by
  rw [bind_assoc]
  refine DEq.bind_right y fun z => ?_
  simp only [fillOut, fillSt, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact DEq.bind_const _ _

theorem evalDist_eager_eq_lazy {ι H α : Type} {spec : OracleSpec ι}
    (implLazy implEager : QueryImpl spec (StateT (H × Option DerivedMessageKeys) ProbComp))
    (hrc : ∀ t, RC (fillKey (H := H)) (implLazy t) (implEager t))
    (oa : OracleComp spec α) (h₀ : H) (post : α → H → ProbComp Bool) :
    𝒟[($ᵗ DerivedMessageKeys) >>= fun k =>
        (simulateQ implEager oa).run (h₀, some k) >>= fun z => post z.1 z.2.1] =
      𝒟[(simulateQ implLazy oa).run (h₀, none) >>= fun z => post z.1 z.2.1] := by
  have hrel := Rel.simulateQ idem_fillKey (fun t => (hrc t).1) (fun t => (hrc t).2) oa (h₀, none)
  have hcomm := Comm.simulateQ idem_fillKey (fun t => (hrc t).2) oa (h₀, none)
  have h1 := (DEq.bind_left (hrel.trans hcomm) (fun z => post z.1 z.2.1)).trans
    (bind_fillOut_post fillKey ((simulateQ implLazy oa).run (h₀, none)) post)
  have h2 : (fillSt fillKey (h₀, none) >>= (simulateQ implEager oa).run >>=
      fun z => post z.1 z.2.1) =
    (($ᵗ DerivedMessageKeys) >>= fun k =>
      (simulateQ implEager oa).run (h₀, some k) >>= fun z => post z.1 z.2.1) := by
    simp [fillSt, fillKey, map_eq_bind_pure_comp, bind_assoc]
  rw [← h2]
  exact DEq.evalDist_eq h1

theorem idxOf?_append_singleton_self {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (a : α)
    (h : xs.idxOf? a = none) :
    (xs ++ [a]).idxOf? a = some xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.idxOf?_cons] at h
    split_ifs at h with hx
    simp only [Option.map_eq_none_iff] at h
    simp [List.cons_append, List.idxOf?_cons, hx, ih h]

theorem idxOf?_append_singleton_of_ne {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {a b : α}
    (hne : b ≠ a) :
    (xs ++ [a]).idxOf? b = xs.idxOf? b := by
  induction xs with
  | nil => simp [List.idxOf?_cons, hne.symm]
  | cons x xs ih =>
    simp only [List.cons_append, List.idxOf?_cons]
    split_ifs <;> simp [ih]

def stepSlot (salts : List Salt32) (salt : Salt32) : ℕ × List Salt32 :=
  match salts.idxOf? salt with
  | some n => (n, salts)
  | none => (salts.length, salts ++ [salt])

theorem stepSlot_idxOf?_self (salts : List Salt32) (salt : Salt32) :
    (stepSlot salts salt).2.idxOf? salt = some (stepSlot salts salt).1 := by
  unfold stepSlot
  cases h : salts.idxOf? salt with
  | none => exact idxOf?_append_singleton_self salts salt h
  | some n => exact h

theorem stepSlot_idxOf?_of_ne (salts : List Salt32) {salt s : Salt32} (hne : s ≠ salt) :
    (stepSlot salts salt).2.idxOf? s = salts.idxOf? s := by
  unfold stepSlot
  cases salts.idxOf? salt with
  | none => exact idxOf?_append_singleton_of_ne salts hne
  | some _ => rfl

abbrev ADType (Pt : Type) := ℕ × (Header Pt × LibsignalMsgPublicPart)
abbrev CtType := LibsignalCiphertextWithSalt32
abbrev QSpecS (Pt : Type) (ℓ : ℕ) := unifSpec + otccaSpec (ADType Pt) (Plain ℓ) CtType

structure SaltSt (Pt : Type) where
  chal : Option (ADType Pt × CtType) := none
  table : List (Salt32 × DerivedMessageKeys) := []
  salts : List Salt32 := []
  chalSlot : Option ℕ := none

def sSlot (salt : Salt32) : StateT (SaltSt Pt) ProbComp ℕ :=
  StateT.mk fun st =>
    let (n, salts') := stepSlot st.salts salt
    pure (n, { st with salts := salts' })

def sKeyOf (salt : Salt32) : StateT (SaltSt Pt) ProbComp DerivedMessageKeys :=
  StateT.mk fun st =>
    match st.table.lookup salt with
    | some k => pure (k, st)
    | none => (fun k => (k, { st with table := (salt, k) :: st.table })) <$> ($ᵗ DerivedMessageKeys)

def saltImpl [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) :
    QueryImpl (QSpecS Pt ℓ) (StateT (SaltSt Pt) ProbComp)
  | .inl n => EtMProof.coin n
  | .inr (.inl ⟨a, m⟩) => do
    if (← get).chal.isSome then return none
    let n ← sSlot a.2.2.salt
    let mk ← sKeyOf a.2.2.salt
    let e ← if b then StateT.lift (lIdeal C codec ℓ encT a)
      else pure ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m)
    modify fun st => { st with chal := some (a, e), chalSlot := some n }
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if e.2 ≠ a.2.2.salt then return none
    let _ ← sSlot a.2.2.salt
    if b || (← get).chal == some (a, e) then return none
    let mk ← sKeyOf a.2.2.salt
    return (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e

def saltFull [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) : ProbComp (Bool × SaltSt Pt) :=
  (simulateQ (saltImpl C codec ℓ encT idOf b) B).run {}

def saltRun [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) : ProbComp Bool :=
  Prod.fst <$> saltFull C codec ℓ encT idOf b B

def isChalSalt (chal : Option (ADType Pt × CtType)) (salt : Salt32) : Bool :=
  match chal with
  | none => false
  | some (a₀, _) => salt == a₀.2.2.salt

/-- Variant of `saltImpl` returning `none` on all decryptions at non-challenge salts. -/
def saltImplNF [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) :
    QueryImpl (QSpecS Pt ℓ) (StateT (SaltSt Pt) ProbComp)
  | .inl n => EtMProof.coin n
  | .inr (.inl ⟨a, m⟩) => do
    if (← get).chal.isSome then return none
    let mk ← sKeyOf a.2.2.salt
    let e ← if b then StateT.lift (lIdeal C codec ℓ encT a)
      else pure ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m)
    modify fun st => { st with chal := some (a, e) }
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if e.2 ≠ a.2.2.salt then return none
    if b || !(isChalSalt (← get).chal a.2.2.salt) || (← get).chal == some (a, e) then return none
    let mk ← sKeyOf a.2.2.salt
    return (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e

def saltFullNF [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) : ProbComp (Bool × SaltSt Pt) :=
  (simulateQ (saltImplNF C codec ℓ encT idOf b) B).run {}

def saltRunNF [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) : ProbComp Bool :=
  Prod.fst <$> saltFullNF C codec ℓ encT idOf b B

def prfImpl (F : ShaState → List (BitVec 8) → ShaState) :
    QueryImpl (unifSpec + prfSpec Salt32 DerivedMessageKeys)
      (StateT (PRFState (BitVec 256) Salt32 DerivedMessageKeys) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (PRFState (BitVec 256) Salt32 DerivedMessageKeys) ProbComp) + (lSaltPRF32 F).prfEval

def lSaltRedImpl [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) :
    QueryImpl (QSpecS Pt ℓ)
      (StateT (Option (ADType Pt × CtType)) (OracleComp (unifSpec + prfSpec Salt32 DerivedMessageKeys))) :=
  fun q =>
    let ae := lAeadK C codec ℓ encT idOf
    match q with
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

theorem simulateQ_prfImpl_liftM (F : ShaState → List (BitVec 8) → ShaState)
    {α : Type} (oa : ProbComp α) :
    simulateQ (prfImpl F) (liftM oa : OracleComp (unifSpec + prfSpec Salt32 DerivedMessageKeys) α) =
      liftM oa := by
  simp [prfImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

@[local simp] theorem lookup_instBEqOfDecidableEq {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (a : α) (l : List (α × β)) :
    @List.lookup α β (@instBEqOfDecidableEq α ‹_›) a l = l.lookup a := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨k, v⟩
    simp only [List.lookup]
    have hbeq : (@BEq.beq α (@instBEqOfDecidableEq α ‹_›) a k) = (a == k) := by
      by_cases h : a = k <;> simp [h]
    rw [hbeq, ih]

theorem prfImpl_evalQuery (F : ShaState → List (BitVec 8) → ShaState) (s : Salt32)
    (pst : PRFState (BitVec 256) Salt32 DerivedMessageKeys) (hb : pst.b = true) :
    (simulateQ (prfImpl F) (evalQuery (Input := Salt32) (Tag := DerivedMessageKeys) s)).run pst =
      match pst.table.lookup s with
      | some k => pure (k, pst)
      | none => (fun k => (k, { pst with table := (s, k) :: pst.table })) <$> ($ᵗ DerivedMessageKeys) := by
  cases hlk : pst.table.lookup s <;>
    simp [prfImpl, evalQuery, prfEval, hb, hlk, map_eq_bind_pure_comp]

@[local simp] theorem sSlot_run (salt : Salt32) (st : SaltSt Pt) :
    (sSlot salt).run st =
      pure ((stepSlot st.salts salt).1, { st with salts := (stepSlot st.salts salt).2 }) :=
  rfl

theorem lSaltRed_simulateQ_eq [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) (key : BitVec 256)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α) :
    ∀ (st : SaltSt Pt),
      (fun z : (α × Option (ADType Pt × CtType)) × PRFState (BitVec 256) Salt32 DerivedMessageKeys => z.1.1) <$>
        (simulateQ (prfImpl C.F)
          ((simulateQ (lSaltRedImpl C codec ℓ encT idOf b) oa).run st.chal)).run
          { key, b := true, table := st.table } =
      Prod.fst <$> (simulateQ (saltImpl C codec ℓ encT idOf b) oa).run st := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st; simp
  | query_bind q k ih =>
    intro st
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp [lSaltRedImpl, saltImpl, prfImpl, EtMProof.coin]
      exact bind_congr fun u => ih u st
    · by_cases hc : st.chal.isSome = true
      · simp [lSaltRedImpl, saltImpl, hc, ih none st]
      · have hev := prfImpl_evalQuery C.F a.2.2.salt { key, b := true, table := st.table } rfl
        simp only [lSaltRedImpl, saltImpl, sSlot_run, sKeyOf, StateT.run_bind, StateT.run_get,
          StateT.run_mk, StateT.run_lift, pure_bind, hc, Bool.false_eq_true, ↓reduceIte,
          simulateQ_bind, bind_assoc, hev]
        cases hlk : st.table.lookup a.2.2.salt with
        | some mk =>
          cases b <;> simp [StateT.run_monadLift, simulateQ_prfImpl_liftM]
          · exact ih _ ⟨some (a, (lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m),
              st.table, (stepSlot st.salts a.2.2.salt).2, some (stepSlot st.salts a.2.2.salt).1⟩
          · refine bind_congr fun e' => ?_
            exact ih (some e') ⟨some (a, e'), st.table, (stepSlot st.salts a.2.2.salt).2,
              some (stepSlot st.salts a.2.2.salt).1⟩
        | none =>
          cases b <;> simp [StateT.run_monadLift, simulateQ_prfImpl_liftM]
          · refine bind_congr fun mk => ?_
            exact ih _ ⟨some (a, (lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m),
              (a.2.2.salt, mk) :: st.table, (stepSlot st.salts a.2.2.salt).2,
              some (stepSlot st.salts a.2.2.salt).1⟩
          · refine bind_congr fun mk => bind_congr fun e' => ?_
            exact ih (some e') ⟨some (a, e'), (a.2.2.salt, mk) :: st.table,
              (stepSlot st.salts a.2.2.salt).2, some (stepSlot st.salts a.2.2.salt).1⟩
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp [lSaltRedImpl, saltImpl, hs, ih none st]
      · simp only [ne_eq, Decidable.not_not] at hs
        by_cases hbc : (b || (st.chal == some (a, e))) = true
        · simp only [lSaltRedImpl, saltImpl, StateT.run_bind, StateT.run_get, sSlot_run,
            pure_bind, hs, ne_eq, not_true_eq_false, decide_false, Bool.or_false, hbc,
            ↓reduceIte, StateT.run_pure, simulateQ_pure]
          exact ih none ⟨st.chal, st.table, (stepSlot st.salts a.2.2.salt).2, st.chalSlot⟩
        · have hev := prfImpl_evalQuery C.F a.2.2.salt { key, b := true, table := st.table } rfl
          simp only [lSaltRedImpl, saltImpl, sSlot_run, sKeyOf, StateT.run_bind,
            StateT.run_get, StateT.run_mk, StateT.run_lift, StateT.run_pure, pure_bind, hs, ne_eq,
            not_true_eq_false, decide_false, Bool.or_false, hbc, Bool.false_eq_true, ↓reduceIte,
            simulateQ_bind, simulateQ_pure, bind_assoc, hev]
          cases hlk : st.table.lookup a.2.2.salt with
          | some mk =>
            simp only [pure_bind]
            exact ih _ ⟨st.chal, st.table, (stepSlot st.salts a.2.2.salt).2, st.chalSlot⟩
          | none =>
            simp
            refine bind_congr fun mk => ?_
            exact ih _ ⟨st.chal, (a.2.2.salt, mk) :: st.table,
              (stepSlot st.salts a.2.2.salt).2, st.chalSlot⟩

def wImpl (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) :
    QueryImpl (LibsignalWireOracleSpec ℓ)
      (StateT (WireState DerivedMessageKeys SerializedIdentityKeys (BitVec 64)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (WireState DerivedMessageKeys SerializedIdentityKeys (BitVec 64)) ProbComp) +
    ((lWire C codec ℓ).wireEncrypt + (lWire C codec ℓ).wireDecrypt)

def wireBranch [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool) (j : ℕ)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) : ProbComp Bool := do
  let key ← $ᵗ DerivedMessageKeys
  (simulateQ (wImpl C codec ℓ)
    (lWireRed C codec ℓ encT idOf j B)).run' { key, b, chal := none }

theorem wireOtccaAdvantage_eq_boolDist [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) :
    (lWire C codec ℓ).wireOtccaAdvantage (lWireRed C codec ℓ encT idOf j B) =
      𝒟[wireBranch C codec ℓ encT idOf true j B].boolDist
        𝒟[wireBranch C codec ℓ encT idOf false j B] := by
  unfold wireOtccaAdvantage wireOtccaGame
  have hcoin : ∀ x : Bool, 𝒟[($ᵗ Bool : ProbComp Bool)] {x} = 1 / 2 := fun _ => by simp
  rw [← evalDist_boolBias_bind_coin ($ᵗ Bool)
    (wireBranch C codec ℓ encT idOf true j B)
    (wireBranch C codec ℓ encT idOf false j B)
    (hcoin true) (hcoin false)]
  congr 2
  refine bind_congr fun b => ?_
  cases b <;> rfl

/-! ## Ideal world (`b = true`) -/

theorem rc_getSlotKey_self {H : Type} :
    RC (fillKey (H := H)) getSlotKey getSlotKey := by
  refine ⟨?_, (rc_getSlotKey (H := H)).2⟩
  rintro ⟨h, sl⟩
  cases sl with
  | some k =>
    exact DEq.of_eq (by
      simp [fillSt, fillOut, fillKey, getSlotKey, StateT.run_mk, map_eq_bind_pure_comp])
  | none =>
    exact DEq.of_eq (by
      simp [fillSt, fillOut, fillKey, getSlotKey, StateT.run_mk,
        map_eq_bind_pure_comp, bind_assoc])

theorem evalDist_bind_congr_support {α : Type}
    (mx : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    exact evalDist_bind_congr _ _ _ fun u =>
      ih u fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

theorem bind_apply_le_add_true {α : Type} (mx : ProbComp α)
    (f g : α → ProbComp Bool) (fl : α → ProbComp Bool) (x : Bool)
    (h : ∀ a, 𝒟[f a] {x} ≤ 𝒟[g a] {x} + 𝒟[fl a] {true}) :
    𝒟[mx >>= f] {x} ≤ 𝒟[mx >>= g] {x} + 𝒟[mx >>= fl] {true} := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a
  | query_bind t k ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable,
      ← MeasureTheory.lintegral_add_right _ Measurable.of_discrete]
    exact lintegral_mono ih

@[local simp] theorem simulateQ_wImpl_liftM (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    {α : Type} (oa : ProbComp α) :
    simulateQ (wImpl C codec ℓ) (liftM oa : OracleComp (LibsignalWireOracleSpec ℓ) α) =
      liftM oa := by
  simp [wImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

@[local simp] theorem wImpl_enc_ideal (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (ids : SerializedIdentityKeys) (hdr : SignalHeader) (m : Plain ℓ)
    (wst : WireState DerivedMessageKeys SerializedIdentityKeys (BitVec 64))
    (hwb : wst.b = true) (hwchal : wst.chal.isSome = false) :
    (simulateQ (wImpl C codec ℓ)
      (query (spec := LibsignalWireOracleSpec ℓ) (Sum.inr (Sum.inl (ids, hdr, m))))).run wst =
      (fun wc => (some wc, { wst with chal := some (ids, wc) })) <$>
        (lWire C codec ℓ).idealEnc hdr := by
  simp [wImpl, wireEncrypt, hwb, hwchal, map_eq_bind_pure_comp]

@[local simp] theorem wImpl_dec_ideal (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (ids : SerializedIdentityKeys) (wc : List (BitVec 8) × BitVec 64)
    (wst : WireState DerivedMessageKeys SerializedIdentityKeys (BitVec 64))
    (hwb : wst.b = true) :
    (simulateQ (wImpl C codec ℓ)
      (query (spec := LibsignalWireOracleSpec ℓ) (Sum.inr (Sum.inr (ids, wc))))).run wst =
      pure (none, wst) := by
  simp [wImpl, wireDecrypt, hwb]

def wIdealImpl [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ) :
    QueryImpl (QSpecS Pt ℓ) (StateT WRedSt ProbComp) := fun q =>
  let _ := idOf
  match q with
  | .inl n => EtMProof.coin n
  | .inr (.inl ⟨a, _m⟩) => do
    let st ← get
    if st.2.2.2 then return none
    let (n, salts') := stepSlot st.1 a.2.2.salt
    if n ≠ j then
      set (salts', st.2.1, true, true)
      return none
    set (salts', st.2.1, st.2.2.1, true)
    let e ← StateT.lift (lIdeal C codec ℓ encT a)
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    let st ← get
    if !st.2.2.2 || e.2 ≠ a.2.2.salt then return none
    let (_, salts') := stepSlot st.1 a.2.2.salt
    set (salts', st.2.1, st.2.2.1, st.2.2.2)
    return none

def wireIdeal [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) : ProbComp Bool :=
  (simulateQ (wIdealImpl C codec ℓ encT idOf j) B).run ([], [], false, false) >>= fun z =>
    if z.2.2.2.1 || (!z.2.2.2.2 && j ≠ 0) then $ᵗ Bool else pure z.1

@[local simp] theorem wSlot_run (ℓ : ℕ) (salt : Salt32) (st : WRedSt) :
    (wSlot ℓ salt).run st =
      pure ((stepSlot st.1 salt).1, ((stepSlot st.1 salt).2, st.2.1, st.2.2.1, st.2.2.2)) := by
  unfold wSlot stepSlot
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases st.1.idxOf? salt <;> simp

theorem wRedImpl_ideal_eq [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α) :
    ∀ (st : WRedSt) (wst : WireState DerivedMessageKeys SerializedIdentityKeys (BitVec 64)),
      wst.b = true →
      (st.2.2.2 = false → wst.chal.isSome = false) →
      Prod.fst <$> (simulateQ (wImpl C codec ℓ)
        ((simulateQ (wRedImpl C codec ℓ encT idOf j) oa).run st)).run wst =
        (simulateQ (wIdealImpl C codec ℓ encT idOf j) oa).run st := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st wst _ _; simp
  | query_bind q k ih =>
    intro st wst hwb hchal
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp [wRedImpl, wIdealImpl, wImpl, EtMProof.coin]
      exact bind_congr fun u => ih u st wst hwb hchal
    · by_cases heq : st.2.2.2 = true
      · simp only [wRedImpl, wIdealImpl, StateT.run_bind, StateT.run_get, pure_bind, heq,
          ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact ih none st wst hwb hchal
      · have heqf : st.2.2.2 = false := Bool.eq_false_iff.mpr heq
        have hwchal : wst.chal.isSome = false := hchal heqf
        by_cases hnj : (stepSlot st.1 a.2.2.salt).1 ≠ j
        · simp only [wRedImpl, wIdealImpl, StateT.run_bind, StateT.run_get, pure_bind, heqf,
            Bool.false_eq_true, ↓reduceIte, wSlot_run, StateT.run_modify, ne_eq, hnj,
            not_false_eq_true, StateT.run_set, StateT.run_pure, simulateQ_pure]
          exact ih none ((stepSlot st.1 a.2.2.salt).2, st.2.1, true, true) wst hwb
            (fun h => by cases h)
        · simp only [ne_eq, Decidable.not_not] at hnj
          simp only [wRedImpl, wIdealImpl, StateT.run_bind, StateT.run_get, pure_bind, heqf,
            Bool.false_eq_true, ↓reduceIte, wSlot_run, StateT.run_modify, ne_eq, hnj,
            not_true_eq_false, StateT.run_set, StateT.run_lift, StateT.run_pure,
            simulateQ_bind, simulateQ_pure, wImpl_enc_ideal C codec ℓ _ _ _ wst hwb hwchal,
            lIdeal, bind_map_left, bind_assoc]
          exact congrArg (Bind.bind (m := ProbComp) _) (funext fun wc =>
            ih (some (wc, a.2.2.salt))
              ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true)
              { wst with chal := some (lIds idOf a.2.1.1, wc) } hwb (fun h => by cases h))
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [wRedImpl, wIdealImpl, StateT.run_bind, StateT.run_get, pure_bind, hs,
          ne_eq, not_false_eq_true, decide_true, Bool.or_true, ↓reduceIte, StateT.run_pure,
          simulateQ_pure]
        exact ih none st wst hwb hchal
      · simp only [ne_eq, Decidable.not_not] at hs
        by_cases heq : st.2.2.2 = true
        · by_cases hnj : (stepSlot st.1 a.2.2.salt).1 = j
          · simp only [wRedImpl, wIdealImpl, StateT.run_bind, StateT.run_get, pure_bind, heq,
              Bool.not_true, hs, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
              Bool.false_eq_true, ↓reduceIte, wSlot_run, StateT.run_set, hnj, StateT.run_lift,
              StateT.run_pure, simulateQ_bind, simulateQ_pure, wImpl_dec_ideal C codec ℓ _ _ wst hwb]
            exact ih none ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true) wst hwb
              (fun h => by cases h)
          · simp only [wRedImpl, wIdealImpl, StateT.run_bind, StateT.run_get, pure_bind, heq,
              Bool.not_true, hs, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
              Bool.false_eq_true, ↓reduceIte, wSlot_run, StateT.run_set, hnj, StateT.run_pure,
              simulateQ_pure]
            exact ih none ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true) wst hwb
              (fun h => by cases h)
        · have heqf : st.2.2.2 = false := Bool.eq_false_iff.mpr heq
          simp only [wRedImpl, wIdealImpl, StateT.run_bind, StateT.run_get, pure_bind, heqf,
            Bool.not_false, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure]
          exact ih none st wst hwb hchal

theorem evalDist_wireBranch_true [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) :
    𝒟[wireBranch C codec ℓ encT idOf true j B] =
      𝒟[wireIdeal C codec ℓ encT idOf j B] := by
  unfold wireBranch wireIdeal
  rw [lWireRed_eq]
  have hkey : ∀ key : DerivedMessageKeys,
      (simulateQ (wImpl C codec ℓ)
        ((simulateQ (wRedImpl C codec ℓ encT idOf j) B).run ([], [], false, false) >>=
          fun ⟨b', st⟩ =>
            if st.2.2.1 || (!st.2.2.2 && j ≠ 0) then
              (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (LibsignalWireOracleSpec ℓ) Bool)
            else pure b')).run' { key, b := true, chal := none } =
      ((simulateQ (wIdealImpl C codec ℓ encT idOf j) B).run ([], [], false, false) >>= fun z =>
        if z.2.2.2.1 || (!z.2.2.2.2 && j ≠ 0) then $ᵗ Bool else pure z.1) := by
    intro key
    have hsim := wRedImpl_ideal_eq C codec ℓ encT idOf j B ([], [], false, false)
      { key, b := true, chal := none } rfl (fun _ => rfl)
    rw [← hsim]
    simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]
    refine congrArg (Bind.bind (m := ProbComp) _) (funext fun p => ?_)
    rcases p with ⟨⟨b', st⟩, wst⟩
    dsimp only
    by_cases hcond : (st.2.2.1 || (!st.2.2.2 && decide (j ≠ 0))) = true
    · simp only [hcond, ↓reduceIte, simulateQ_wImpl_liftM, StateT.run_monadLift,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, bind_pure]
      rfl
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure, map_pure]
  simp only [hkey, OracleComp.evalDist_bind_const]

/-- Synchronization invariant between `wIdealImpl 0` and `saltImpl true`. -/
structure IdealSync0 (st : WRedSt) (sst : SaltSt Pt) : Prop where
  ab_false : st.2.2.1 = false
  eq_chal : st.2.2.2 = sst.chal.isSome
  salts_nil : st.2.2.2 = false → st.1 = []

theorem evalDist_wireIdeal_zero_eq_saltRun_true_aux [DecidableEq Pt] (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (oa : OracleComp (QSpecS Pt ℓ) Bool) :
    ∀ (st : WRedSt) (sst : SaltSt Pt),
      IdealSync0 st sst →
      𝒟[(simulateQ (wIdealImpl C codec ℓ encT idOf 0) oa).run st >>= fun z =>
        if z.2.2.2.1 || (!z.2.2.2.2 && (0 : ℕ) ≠ 0) then $ᵗ Bool else pure z.1] =
      𝒟[(simulateQ (saltImpl C codec ℓ encT idOf true) oa).run sst >>= fun z => pure z.1] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st sst hsync
    simp [hsync.ab_false]
  | query_bind q k ih =>
    intro st sst hsync
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [wIdealImpl, saltImpl, EtMProof.coin, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, bind_assoc, pure_bind]
      exact evalDist_bind_congr _ _ _ fun u => ih u st sst hsync
    · by_cases heq : st.2.2.2 = true
      · have hc : sst.chal.isSome = true := hsync.eq_chal.symm.trans heq
        simp only [wIdealImpl, saltImpl, StateT.run_bind, StateT.run_get, pure_bind, heq,
          ↓reduceIte, hc, StateT.run_pure]
        exact ih none st sst hsync
      · have heqf : st.2.2.2 = false := Bool.eq_false_iff.mpr heq
        have hcf : sst.chal.isSome = false := hsync.eq_chal.symm.trans heqf
        have hsalts : st.1 = [] := hsync.salts_nil heqf
        have hn0 : (stepSlot st.1 a.2.2.salt).1 = 0 := by simp [hsalts, stepSlot]
        simp only [wIdealImpl, saltImpl, StateT.run_bind, StateT.run_get, pure_bind, heqf,
          Bool.false_eq_true, ↓reduceIte, ne_eq, hn0, not_true_eq_false, StateT.run_set,
          StateT.run_lift, StateT.run_pure, hcf, sSlot_run, StateT.run_modify, bind_assoc]
        symm
        refine (evalDist_bind_congr_support _ _
          (fun _ => do
            let x ← lIdeal C codec ℓ encT a
            let z ← (simulateQ (wIdealImpl C codec ℓ encT idOf 0) (k (some x))).run
              ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true)
            if z.2.2.2.1 || (!z.2.2.2.2 && (0 : ℕ) ≠ 0) then $ᵗ Bool else pure z.1)
          fun p _ => ?_).trans (OracleComp.evalDist_bind_const _ _)
        rcases p with ⟨k', sst₁⟩
        refine evalDist_bind_congr _ _ _ fun e' => ?_
        symm
        exact ih (some e') ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true)
          { sst₁ with chal := some (a, e'), chalSlot := some (stepSlot sst.salts a.2.2.salt).1 }
          ⟨hsync.ab_false, rfl, fun h => by cases h⟩
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [wIdealImpl, saltImpl, StateT.run_bind, StateT.run_get, pure_bind, hs, ne_eq,
          not_false_eq_true, decide_true, Bool.or_true, ↓reduceIte, StateT.run_pure]
        exact ih none st sst hsync
      · simp only [ne_eq, Decidable.not_not] at hs
        by_cases heq : st.2.2.2 = true
        · simp only [wIdealImpl, saltImpl, StateT.run_bind, StateT.run_get, pure_bind, heq,
            Bool.not_true, hs, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure, sSlot_run,
            Bool.true_or]
          exact ih none ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true)
            { sst with salts := (stepSlot sst.salts a.2.2.salt).2 }
            ⟨hsync.ab_false, (hsync.eq_chal.symm.trans heq).symm, fun h => by cases h⟩
        · have heqf : st.2.2.2 = false := Bool.eq_false_iff.mpr heq
          simp only [wIdealImpl, saltImpl, StateT.run_bind, StateT.run_get, pure_bind, heqf,
            Bool.not_false, Bool.true_or, ↓reduceIte, StateT.run_pure, hs, ne_eq,
            not_true_eq_false, sSlot_run]
          exact ih none st { sst with salts := (stepSlot sst.salts a.2.2.salt).2 }
            ⟨hsync.ab_false, hsync.eq_chal, hsync.salts_nil⟩

theorem evalDist_wireBranch_true_zero [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) :
    𝒟[wireBranch C codec ℓ encT idOf true 0 B] =
      𝒟[saltRun C codec ℓ encT idOf true B] := by
  rw [evalDist_wireBranch_true, wireIdeal, saltRun, saltFull, map_eq_bind_pure_comp]
  exact evalDist_wireIdeal_zero_eq_saltRun_true_aux C codec ℓ encT idOf B
    ([], [], false, false) {} ⟨rfl, rfl, fun _ => rfl⟩

theorem lAeadK_dec_eq_none_of_tag_false (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : DerivedMessageKeys) (a : ADType Pt) (e : CtType)
    (htag : ((hmacScheme C.F).tag k.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2) = false) :
    (lAeadK C codec ℓ encT idOf).dec k ((a.1, a.2.1), a.2.2) e = none := by
  simp [lAeadK, lWire, libsignalWireAead, libsignalReceiveWire, beq_eq_false_iff_ne.mp htag]

theorem lForge_step_le (F : ShaState → List (BitVec 8) → ShaState)
    (ids : SerializedIdentityKeys) (ser : List (BitVec 8)) (hser : ser.length < 2 ^ 32)
    (tag : BitVec 64) :
    𝒟[(fun k : DerivedMessageKeys => (hmacScheme F).tag k.2 (ids.toList ++ ser) == tag) <$> ($ᵗ DerivedMessageKeys)] {true} ≤
      macForgeryProb F := by
  unfold macForgeryProb
  rw [map_eq_bind_pure_comp]
  exact le_iSup₂_of_le ids ser (le_iSup₂_of_le hser tag le_rfl)

theorem chal_beq_false_of_isChalSalt_false [DecidableEq Pt]
    {chal : Option (ADType Pt × CtType)} {a : ADType Pt} {e : CtType}
    (hcs : isChalSalt chal a.2.2.salt = false) :
    (chal == some (a, e)) = false := by
  cases chal with
  | none => rfl
  | some p =>
    rcases p with ⟨a₀, e₀⟩
    unfold isChalSalt at hcs
    simp only [beq_eq_false_iff_ne, ne_eq] at hcs ⊢
    rintro ⟨rfl, _⟩
    exact hcs rfl

/-! ## Real world (`b = false`) and final bound -/

def otBadIdx {ℓ : ℕ} : (unifSpec + otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain → Bool
  | .inr (.inl ⟨a, _⟩) => decide (a.1 = 0 ∨ 2 ^ 32 < a.1)
  | .inr (.inr ⟨a, _⟩) => decide (a.1 = 0 ∨ 2 ^ 32 < a.1)
  | _ => false

theorem idxOf?_inj {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {a b : α} {n : ℕ}
    (ha : xs.idxOf? a = some n) (hb : xs.idxOf? b = some n) : a = b := by
  induction xs generalizing n with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.idxOf?_cons] at ha hb
    split_ifs at ha hb with hxa hxb
    · rw [beq_iff_eq] at hxa hxb; exact hxa.symm.trans hxb
    · simp only [Option.some.injEq] at ha
      simp only [Option.map_eq_some_iff] at hb
      rcases hb with ⟨m, _, hm⟩; omega
    · simp only [Option.some.injEq] at hb
      simp only [Option.map_eq_some_iff] at ha
      rcases ha with ⟨m, _, hm⟩; omega
    · simp only [Option.map_eq_some_iff] at ha hb
      rcases ha with ⟨m₁, hm₁, rfl⟩
      rcases hb with ⟨m₂, hm₂, hm⟩
      exact ih hm₁ (Nat.succ.inj hm ▸ hm₂)

theorem stepSlot_idxOf?_pres (salts : List Salt32) (salt s : Salt32) {n : ℕ}
    (hs : salts.idxOf? s = some n) :
    (stepSlot salts salt).2.idxOf? s = some n := by
  by_cases h : s = salt
  · subst h; unfold stepSlot; rw [hs]; exact hs
  · rw [stepSlot_idxOf?_of_ne salts h, hs]

theorem stepSlot_fst_eq_iff_idxOf? (salts : List Salt32) (salt s : Salt32) {n : ℕ}
    (hs : salts.idxOf? s = some n) :
    (stepSlot salts salt).1 = n ↔ salt = s := by
  constructor
  · intro hn
    by_contra hne
    have h1 : (stepSlot salts salt).2.idxOf? s = some n := by
      rw [stepSlot_idxOf?_of_ne salts (Ne.symm hne), hs]
    have h2 : (stepSlot salts salt).2.idxOf? salt = some n := by
      rw [stepSlot_idxOf?_self, hn]
    exact hne (idxOf?_inj h2 h1)
  · rintro rfl
    unfold stepSlot
    rw [hs]

theorem isQueryBoundP_zero_query_bind {ι α : Type} {spec : OracleSpec ι}
    {P : spec.Domain → Prop} [DecidablePred P] (q : spec.Domain)
    (k : spec.Range q → OracleComp spec α)
    (h : ((liftM (OracleSpec.query q) : OracleComp spec (spec.Range q)) >>= k).IsQueryBoundP P 0) :
    ¬ P q ∧ ∀ u, (k u).IsQueryBoundP P 0 := by
  rw [isQueryBoundP_query_bind_iff] at h
  have hp : ¬ P q := h.1.resolve_right (Nat.not_lt_zero 0)
  refine ⟨hp, fun u => ?_⟩
  have hu := h.2 u
  simpa [hp] using hu

@[local simp] theorem readSlotKey_run {H : Type} (h : H) (k : DerivedMessageKeys) :
    readSlotKey.run (h, some k) = pure (k, (h, some k)) := rfl

@[local simp] theorem wImpl_enc_real (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (ids : SerializedIdentityKeys) (hdr : SignalHeader) (m : Plain ℓ)
    (wst : WireState DerivedMessageKeys SerializedIdentityKeys (BitVec 64))
    (hwb : wst.b = false) (hwchal : wst.chal.isSome = false) :
    (simulateQ (wImpl C codec ℓ)
      (query (spec := LibsignalWireOracleSpec ℓ) (Sum.inr (Sum.inl (ids, hdr, m))))).run wst =
      let wc := (lWire C codec ℓ).enc wst.key ids hdr m
      pure (some wc, { wst with chal := some (ids, wc) }) := by
  simp [wImpl, wireEncrypt, hwb, hwchal]

@[local simp] theorem wImpl_dec_real (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (ids : SerializedIdentityKeys) (wc : List (BitVec 8) × BitVec 64)
    (wst : WireState DerivedMessageKeys SerializedIdentityKeys (BitVec 64))
    (hwb : wst.b = false) :
    (simulateQ (wImpl C codec ℓ)
      (query (spec := LibsignalWireOracleSpec ℓ) (Sum.inr (Sum.inr (ids, wc))))).run wst =
      if wst.chal == some (ids, wc) then pure (none, wst)
      else pure ((lWire C codec ℓ).dec wst.key ids wc, wst) := by
  simp [wImpl, wireDecrypt, hwb]
  split_ifs <;> rfl

abbrev WRealH := WRedSt × Option (SerializedIdentityKeys × (List (BitVec 8) × BitVec 64))

def wRealStep [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    (getK : StateT (WRealH × Option DerivedMessageKeys) ProbComp DerivedMessageKeys) :
    QueryImpl (QSpecS Pt ℓ) (StateT (WRealH × Option DerivedMessageKeys) ProbComp)
  | .inl n => onH (EtMProof.coin n)
  | .inr (.inl ⟨a, m⟩) => do
    let ⟨st, wc⟩ ← onH get
    if st.2.2.2 then return none
    let (n, salts') := stepSlot st.1 a.2.2.salt
    if n ≠ j then
      onH (set ((salts', st.2.1, true, true), wc))
      return none
    let k' ← getK
    let wc' := (lWire C codec ℓ).enc k' (lIds idOf a.2.1.1) (lHeader encT a.1 a.2.1 a.2.2) m
    onH (set ((salts', st.2.1, st.2.2.1, true), some (lIds idOf a.2.1.1, wc')))
    return some (wc', a.2.2.salt)
  | .inr (.inr ⟨a, e⟩) => do
    let ⟨st, wc⟩ ← onH get
    if !st.2.2.2 || e.2 ≠ a.2.2.salt then return none
    let (n, salts') := stepSlot st.1 a.2.2.salt
    onH (set ((salts', st.2.1, st.2.2.1, st.2.2.2), wc))
    if n = j then
      if wc == some (lIds idOf a.2.1.1, e.1) then return none
      else
        let k' ← getK
        return (lAeadK C codec ℓ encT idOf).dec k' ((a.1, a.2.1), a.2.2) e
    else
      return none

theorem wRealStep_rc [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ) :
    ∀ t, RC (fillKey (H := WRealH))
      (wRealStep C codec ℓ encT idOf j getSlotKey t)
      (wRealStep C codec ℓ encT idOf j readSlotKey t) := by
  intro t
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · exact rc_onH _
  · refine (rc_onH _).bind fun ⟨st, wc⟩ => ?_
    by_cases heq : st.2.2.2 = true
    · simp only [heq, ↓reduceIte]; exact RC.pure (idem_fillKey (H := WRealH)) _
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      by_cases hnj : (stepSlot st.1 a.2.2.salt).1 ≠ j
      · simp only [ne_eq, hnj, not_false_eq_true, ↓reduceIte]
        exact (rc_onH _).bind fun _ => RC.pure (idem_fillKey (H := WRealH)) _
      · simp only [hnj, ↓reduceIte]
        exact rc_getSlotKey.bind fun k' =>
          (rc_onH _).bind fun _ => RC.pure (idem_fillKey (H := WRealH)) _
  · refine (rc_onH _).bind fun ⟨st, wc⟩ => ?_
    by_cases hcond : (!st.2.2.2 || decide (e.2 ≠ a.2.2.salt)) = true
    · simp only [hcond, ↓reduceIte]
      exact RC.pure (idem_fillKey (H := WRealH)) _
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      refine (rc_onH _).bind fun _ => ?_
      by_cases hnj : (stepSlot st.1 a.2.2.salt).1 = j
      · simp only [hnj, ↓reduceIte]
        by_cases hwc : (wc == some (lIds idOf a.2.1.1, e.1)) = true
        · simp only [hwc, ↓reduceIte]; exact RC.pure (idem_fillKey (H := WRealH)) _
        · simp only [hwc, Bool.false_eq_true, ↓reduceIte]
          exact rc_getSlotKey.bind fun _ => RC.pure (idem_fillKey (H := WRealH)) _
      · simp only [hnj, ↓reduceIte]
        exact RC.pure (idem_fillKey (H := WRealH)) _

theorem wRedImpl_real_eq [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α) :
    ∀ (st : WRedSt) (key : DerivedMessageKeys) (wchal : Option (SerializedIdentityKeys × (List (BitVec 8) × BitVec 64))),
      (st.2.2.2 = false → wchal.isSome = false) →
      (fun z : (α × WRedSt) × WireState DerivedMessageKeys SerializedIdentityKeys (BitVec 64) =>
          (z.1.1, ((z.1.2, z.2.chal), some z.2.key))) <$>
        (simulateQ (wImpl C codec ℓ)
          ((simulateQ (wRedImpl C codec ℓ encT idOf j) oa).run st)).run
          { key, b := false, chal := wchal } =
      (simulateQ (wRealStep C codec ℓ encT idOf j readSlotKey) oa).run ((st, wchal), some key) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st key wchal _; simp
  | query_bind q k ih =>
    intro st key wchal hchal
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp [wRedImpl, wRealStep, wImpl, onH, EtMProof.coin]
      exact bind_congr fun u => ih u st key wchal hchal
    · by_cases heq : st.2.2.2 = true
      · simp only [wRedImpl, wRealStep, onH, StateT.run_bind, StateT.run_get, StateT.run_mk,
          pure_bind, map_pure, heq, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact ih none st key wchal hchal
      · have heqf : st.2.2.2 = false := Bool.eq_false_iff.mpr heq
        have hwchal : wchal.isSome = false := hchal heqf
        by_cases hnj : (stepSlot st.1 a.2.2.salt).1 ≠ j
        · simp only [wRedImpl, wRealStep, onH, StateT.run_bind, StateT.run_get, StateT.run_mk,
            pure_bind, map_pure, heqf, Bool.false_eq_true, ↓reduceIte, wSlot_run,
            StateT.run_modify, ne_eq, hnj, not_false_eq_true, StateT.run_set, StateT.run_pure,
            simulateQ_pure]
          exact ih none ((stepSlot st.1 a.2.2.salt).2, st.2.1, true, true) key wchal
            (fun h => by cases h)
        · simp only [ne_eq, Decidable.not_not] at hnj
          simp only [wRedImpl, wRealStep, onH, readSlotKey_run, StateT.run_bind, StateT.run_get,
            StateT.run_mk, pure_bind, map_pure, heqf, Bool.false_eq_true, ↓reduceIte, wSlot_run,
            StateT.run_modify, ne_eq, hnj, not_true_eq_false, StateT.run_set, StateT.run_lift,
            StateT.run_pure, simulateQ_bind, simulateQ_pure,
            wImpl_enc_real C codec ℓ _ _ _ { key, b := false, chal := wchal } rfl hwchal]
          exact ih (some ((lWire C codec ℓ).enc key (lIds idOf a.2.1.1)
              (lHeader encT a.1 a.2.1 a.2.2) m, a.2.2.salt))
            ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true) key
            (some (lIds idOf a.2.1.1, (lWire C codec ℓ).enc key (lIds idOf a.2.1.1)
              (lHeader encT a.1 a.2.1 a.2.2) m)) (fun h => by cases h)
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [wRedImpl, wRealStep, onH, StateT.run_bind, StateT.run_get, StateT.run_mk,
          pure_bind, map_pure, hs, ne_eq, not_false_eq_true, decide_true, Bool.or_true, ↓reduceIte,
          StateT.run_pure, simulateQ_pure]
        exact ih none st key wchal hchal
      · simp only [ne_eq, Decidable.not_not] at hs
        by_cases heq : st.2.2.2 = true
        · by_cases hnj : (stepSlot st.1 a.2.2.salt).1 = j
          · by_cases hwc : (wchal == some (lIds idOf a.2.1.1, e.1)) = true
            · simp only [wRedImpl, wRealStep, onH, StateT.run_bind, StateT.run_get, StateT.run_mk,
                pure_bind, map_pure, heq, Bool.not_true, hs, ne_eq, not_true_eq_false, decide_false,
                Bool.false_or, Bool.false_eq_true, ↓reduceIte, wSlot_run, StateT.run_set, hnj,
                StateT.run_lift, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                wImpl_dec_real C codec ℓ _ _ { key, b := false, chal := wchal } rfl, hwc]
              exact ih none ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true)
                key wchal (fun h => by cases h)
            · simp only [wRedImpl, wRealStep, onH, readSlotKey_run, StateT.run_bind, StateT.run_get,
                StateT.run_mk, pure_bind, map_pure, heq, Bool.not_true, hs, ne_eq,
                not_true_eq_false, decide_false, Bool.false_or, ↓reduceIte, wSlot_run,
                StateT.run_set, hnj, StateT.run_lift, StateT.run_pure, simulateQ_bind,
                simulateQ_pure,
                wImpl_dec_real C codec ℓ _ _ { key, b := false, chal := wchal } rfl,
                hwc, Bool.false_eq_true, lAeadK]
              cases (lWire C codec ℓ).dec key (lIds idOf a.2.1.1) e.1 with
              | none =>
                exact ih none ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true)
                  key wchal (fun h => by cases h)
              | some p =>
                exact ih _ ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true)
                  key wchal (fun h => by cases h)
          · simp only [wRedImpl, wRealStep, onH, StateT.run_bind, StateT.run_get, StateT.run_mk,
              pure_bind, map_pure, heq, Bool.not_true, hs, ne_eq, not_true_eq_false, decide_false,
              Bool.false_or, Bool.false_eq_true, ↓reduceIte, wSlot_run, StateT.run_set, hnj,
              StateT.run_pure, simulateQ_pure]
            exact ih none ((stepSlot st.1 a.2.2.salt).2, st.2.1, st.2.2.1, true) key wchal
              (fun h => by cases h)
        · have heqf : st.2.2.2 = false := Bool.eq_false_iff.mpr heq
          simp only [wRedImpl, wRealStep, onH, StateT.run_bind, StateT.run_get, StateT.run_mk,
            pure_bind, map_pure, heqf, Bool.not_false, Bool.true_or, ↓reduceIte, StateT.run_pure,
            simulateQ_pure]
          exact ih none st key wchal hchal

theorem evalDist_wireBranch_false_eq_lazy [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType) :
    𝒟[wireBranch C codec ℓ encT idOf false j B] =
      𝒟[(simulateQ (wRealStep C codec ℓ encT idOf j getSlotKey) B).run
          ((([], [], false, false), none), none) >>= fun z =>
        if z.2.1.1.2.2.1 || (!z.2.1.1.2.2.2 && j ≠ 0) then $ᵗ Bool else pure z.1] := by
  rw [← evalDist_eager_eq_lazy (wRealStep C codec ℓ encT idOf j getSlotKey)
    (wRealStep C codec ℓ encT idOf j readSlotKey) (wRealStep_rc C codec ℓ encT idOf j)
    B (([], [], false, false), none)
    (fun b' h => if h.1.2.2.1 || (!h.1.2.2.2 && j ≠ 0) then $ᵗ Bool else pure b')]
  unfold wireBranch
  rw [lWireRed_eq]
  refine evalDist_bind_congr ($ᵗ DerivedMessageKeys) _ _ fun key => congrArg evalDist ?_
  have hsim := wRedImpl_real_eq C codec ℓ encT idOf j B ([], [], false, false) key none
    (fun _ => rfl)
  rw [← hsim]
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]
  refine congrArg (Bind.bind (m := ProbComp) _) (funext fun p => ?_)
  rcases p with ⟨⟨b', st⟩, wst⟩
  dsimp only
  by_cases hcond : (st.2.2.1 || (!st.2.2.2 && decide (j ≠ 0))) = true
  · simp only [hcond, ↓reduceIte, simulateQ_wImpl_liftM, StateT.run_monadLift,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, bind_pure]
    rfl
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure, map_pure]

end CryptoGames.LibsignalSM.Proofs.WireHop
