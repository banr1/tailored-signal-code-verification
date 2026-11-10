/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.Assumptions
public import Computational.Specifications.Assumptions.KemCorrect
public import Computational.Proofs.SpecLemmas.Assumptions.AssumptionsProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.ModelProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# PQXDH Assumption Helpers and First-Message AD Layout

**Checked by Lean.**

Proof-side assumption definitions (`HkdfRO`, Kyber-1024 `KemIndCca`, multi-key AEAD integrity
`AeadMuIntCtxt`, and `CryptoWellFormedPrimitives`) and parsing lemmas for `firstMsgAD`
(`goodFirstMsgAD_iff`).
-/

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

/-- Lazy-caching random oracle mapping `secrets` to a uniform 96-byte `DRKey` (DEV-PQ14). -/
def HkdfRO (P : Primitives) (roCache : List (Bytes × DRKey)) (secrets : Bytes) :
    ProbComp (DRKey × List (Bytes × DRKey)) :=
  evalHkdfOrRo true P roCache secrets

/-- Decapsulation oracle query in the Kyber-1024 IND-CCA2 game. -/
inductive KemCcaQuery where
  | decaps (ct : Bytes)
  deriving DecidableEq, Repr

@[reducible] def kemCcaSpec : OracleSpec KemCcaQuery := fun _ => Option Bytes

/-- Adversary against the Kyber-1024 IND-CCA2 game with decapsulation and primitive-oracle budgets. -/
structure KemIndCcaAdv where
  run    : Bytes → Bytes → Bytes → OracleComp (PrimBaseSpec + kemCcaSpec) Bool
  q_dec  : Nat
  q_prim : Nat

/-- Kyber-1024 IND-CCA2 experiment returning whether the adversary guesses the challenge bit `b`. -/
noncomputable def kemIndCcaExp (P : Primitives) (A : KemIndCcaAdv) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (pk, sk) ← sampleKemKeyGen P
  let r ← sampleCoins32
  let some (ss0, ctStar) := P.kemEncaps pk r | do let coin ← $ᵗ Bool; return coin
  let ss1 ← sampleBytes32
  let ssStar := if b then ss0 else ss1
  let decImpl : QueryImpl kemCcaSpec ProbComp := fun (.decaps ct) =>
    if ct == ctStar || ct.length != kyberCtLen then pure none else pure (P.kemDecaps sk ct)
  let b' ← simulateQ (primBaseImpl P + decImpl) (A.run pk ctStar ssStar)
  return (b' == b)

/-- IND-CCA2 distinguishing bias against Kyber-1024. -/
noncomputable def KemIndCca (P : Primitives) (A : KemIndCcaAdv) : ℝ :=
  (𝒟[kemIndCcaExp P A].boolBias).toReal

/-- Predicate characterizing `firstMsgAD ikA ikB ephAPk pq` for 32-byte EC public keys. -/
def IsFirstMsgAD (ad : Bytes) : Prop :=
  ∃ ikA ikB ephAPk pq : Bytes, ikA.length = 32 ∧ ikB.length = 32 ∧ ephAPk.length = 32 ∧
    ad = firstMsgAD ikA ikB ephAPk pq

/-- Computable check for `IsFirstMsgAD` (`goodFirstMsgAD_iff`), restricting INT-CTXT games to
    associated data on which `aeadMacInput` uniquely determines `(ad, ct)`. -/
def goodFirstMsgAD (ad : Bytes) : Bool :=
  let ikA := (ad.drop 1).take 32
  let ikB := (ad.drop 34).take 32
  let ephAPk := (ad.drop 70).take 32
  let tl := ad.drop firstMsgHdrLen
  decide (firstMsgHdrLen ≤ ad.length) &&
    (List.range (tl.length + 1)).any (fun k => ad == firstMsgAD ikA ikB ephAPk (tl.drop k))

@[reducible] def aeadMuIntSpec : OracleSpec AeadMuIntQuery := fun
  | .encOnce _ _ _  => Option Bytes
  | .tryForge _ _ _ => Bool

/-- Adversary against multi-key INT-CTXT ciphertext integrity of the first-message AEAD. -/
structure AeadMuIntCtxtAdv where
  run    : OracleComp (PrimBaseSpec + aeadMuIntSpec) Unit
  q_enc  : ℕ
  q_dec  : ℕ
  q_prim : ℕ

def AeadMuIntCtxtAdv.Bounded (A : AeadMuIntCtxtAdv) : Prop :=
  OracleComp.IsQueryBoundP A.run isMuEncQuery A.q_enc ∧
  OracleComp.IsQueryBoundP A.run isMuForgeQuery A.q_dec ∧
  OracleComp.IsQueryBoundP A.run (fun q => isPrimQuery q = true) A.q_prim

abbrev AeadMuIntState :=
  List (ℕ × MessageKeys) × List (ℕ × (Bytes × Bytes)) × Bool

def aeadMuIntKey (i : ℕ) : StateT AeadMuIntState ProbComp MessageKeys := do
  let (keys, chal, w) ← get
  match keys.lookup i with
  | some mk => return mk
  | none =>
    let mk ← liftM sampleMessageKeys80
    set ((i, mk) :: keys, chal, w)
    return mk

/-- Multi-key INT-CTXT experiment with lazy independent 80-byte keys, at most one encryption per
    key, and associated data restricted to `goodFirstMsgAD`. -/
def aeadMuIntCtxtExp (P : Primitives) (A : AeadMuIntCtxtAdv) : ProbComp Bool := do
  let impl : QueryImpl aeadMuIntSpec (StateT AeadMuIntState ProbComp) := fun q =>
    match q with
    | .encOnce i ad pt => do
      if !goodFirstMsgAD ad then return none
      let (_, chal, _) ← get
      match chal.lookup i with
      | some _ => return none
      | none =>
        let mk ← aeadMuIntKey i
        let ct := P.aeadEnc mk ad pt
        let (keys, chal', w) ← get
        set (keys, (i, (ad, ct)) :: chal', w)
        return (some ct)
    | .tryForge i ad ct => do
      if !goodFirstMsgAD ad then return false
      let (_, chal, _) ← get
      if chal.lookup i == some (ad, ct) then return false
      let mk ← aeadMuIntKey i
      match P.aeadDec mk ad ct with
      | some _ =>
        let (keys, chal', _) ← get
        set (keys, chal', true)
        return true
      | none => return false
  let fullImpl := (primBaseImpl P).liftTarget (StateT AeadMuIntState ProbComp) + impl
  let (_, (_, _, wonFinal)) ← (simulateQ fullImpl A.run).run ([], [], false)
  return wonFinal

/-- Multi-key INT-CTXT forgery advantage against the first-message AEAD over `goodFirstMsgAD`. -/
noncomputable def AeadMuIntCtxt (P : Primitives) (A : AeadMuIntCtxtAdv) : ℝ :=
  (𝒟[aeadMuIntCtxtExp P A] {true}).toReal

/-- Combined KEM correctness (`WellFormedPrimitives`) and cryptographic well-formedness
    (`CryptoWellFormedPrimitivesδ`). -/
structure CryptoWellFormedPrimitives (P : Primitives) : Prop
    extends WellFormedPrimitives P, CryptoWellFormedPrimitivesδ P

end SignalPqxdh

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

theorem firstMsgAD_layout (a b e pq : Bytes) (he : e.length = 32) :
    firstMsgAD a b e pq = 0x05 :: (a ++ 0x05 :: (b ++ 0x44 :: 0x0a :: 0x21 :: 0x05 ::
      (e ++ 0x10 :: 0x00 :: 0x18 :: 0x00 ::
        (if pq.isEmpty then [] else pbBytesField 5 pq)))) := by
  have h : pbVarint 33 = [0x21] := by decide
  simp only [firstMsgAD, encodeEC, pbBytesField, List.length_cons, he, h, TAG_EC_DJB]
  simp

theorem firstMsgAD_fields (a b e pq : Bytes) (ha : a.length = 32) (hb : b.length = 32)
    (he : e.length = 32) :
    ((firstMsgAD a b e pq).drop 1).take 32 = a ∧ ((firstMsgAD a b e pq).drop 34).take 32 = b ∧
    ((firstMsgAD a b e pq).drop 70).take 32 = e ∧
    (firstMsgAD a b e pq).drop firstMsgHdrLen = (if pq.isEmpty then [] else pbBytesField 5 pq) ∧
    firstMsgHdrLen ≤ (firstMsgAD a b e pq).length := by
  rw [firstMsgAD_layout a b e pq he]
  have da : ∀ k, 32 ≤ k → a.drop k = [] := fun k hk => List.drop_eq_nil_of_le (by omega)
  have db : ∀ k, 32 ≤ k → b.drop k = [] := fun k hk => List.drop_eq_nil_of_le (by omega)
  have de : ∀ k, 32 ≤ k → e.drop k = [] := fun k hk => List.drop_eq_nil_of_le (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [ha]
  · simp [List.drop_append, ha, hb, da]
  · simp [List.drop_append, ha, hb, he, da, db]
  · simp [firstMsgHdrLen, List.drop_append, ha, hb, he, da, db, de]
  · simp [firstMsgHdrLen, ha, hb, he]; omega

theorem goodFirstMsgAD_iff (ad : Bytes) : goodFirstMsgAD ad = true ↔ IsFirstMsgAD ad := by
  constructor
  · intro h
    simp only [goodFirstMsgAD, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      beq_iff_eq] at h
    obtain ⟨hlen, k, -, hk⟩ := h
    refine ⟨_, _, _, _, ?_, ?_, ?_, hk⟩ <;> simp [List.length_take, List.length_drop] <;>
      simp [firstMsgHdrLen] at hlen <;> omega
  · rintro ⟨a, b, e, pq, ha, hb, he, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := firstMsgAD_fields a b e pq ha hb he
    simp only [goodFirstMsgAD, h1, h2, h3, h4, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true, beq_iff_eq, List.mem_range]
    refine ⟨h5, ?_⟩
    by_cases hp : pq.isEmpty
    · refine ⟨0, by simp [hp], ?_⟩
      have : pq = [] := List.isEmpty_iff.mp hp
      subst this; rfl
    · refine ⟨1 + (pbVarint pq.length).length, ?_, ?_⟩
      · simp [hp, pbBytesField]; omega
      · simp only [hp, pbBytesField, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_comm, List.drop_succ_cons, List.drop_left]

end SignalPqxdh
