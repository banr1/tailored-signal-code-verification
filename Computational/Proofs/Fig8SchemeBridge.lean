/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8Atomic
public import Computational.Proofs.ReductionDsl.PureAuxMacroLift
public import Computational.Proofs.ReductionDsl.SM.Theorem1
public import Computational.Proofs.ReductionDsl.SM.RedCKA
public import Computational.Proofs.ReductionDsl.SM.RedPRNG
public import Computational.Proofs.ReductionDsl.SM.RedFS
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSession.Fig8SchemeBridge

open OracleComp OracleSpec ENNReal
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  LibsignalProtoCodec HMAC HKDF CBC LibsignalAead SM SM.Engine SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD
open ReductionDsl
open Computational.Proofs.ReductionDsl.Fig8Atomic

section PartyParity

lemma sendsIn_one_A : Party.A.sendsIn 1 = true := rfl
lemma sendsIn_one_B : Party.B.sendsIn 1 = false := rfl

lemma sendsIn_succ (P : Party) (t : ℕ) : P.sendsIn (t + 1) = !P.sendsIn t := by
  cases P <;> rw [Bool.eq_iff_iff] <;> simp only [Party.sendsIn, Bool.not_eq_true',
    beq_iff_eq, beq_eq_false_iff_ne] <;> omega

lemma sendsIn_other (P : Party) (t : ℕ) : P.other.sendsIn t = !P.sendsIn t := by
  cases P <;> rw [Bool.eq_iff_iff] <;> simp only [Party.other, Party.sendsIn, Bool.not_eq_true',
    beq_iff_eq, beq_eq_false_iff_ne] <;> omega

/-- Ping-pong role invariant on `DDH.State`: when `P` sends next (`P.sendsIn (t + 1)`), `γ` holds
a public point `.pub T`; otherwise `γ` holds a secret scalar `.exp x`. -/
def DdhRoleOk {Sc Pt : Type} (P : Party) (t : ℕ) (γ : CKA.DDH.State Sc Pt) : Prop :=
  if P.sendsIn (t + 1) then ∃ T, γ = .pub T else ∃ x, γ = .exp x

lemma ddhRoleOk_initA {Pt : Type} [Zero Pt] (Dh : DHFun (BitVec 256) Pt) (k : BitVec 256) :
    DdhRoleOk .A 0 ((dhScheme Dh).initA k) :=
  ⟨Dh.dh k Dh.base, rfl⟩

lemma ddhRoleOk_initB {Pt : Type} [Zero Pt] (Dh : DHFun (BitVec 256) Pt) (k : BitVec 256) :
    DdhRoleOk .B 0 ((dhScheme Dh).initB k) :=
  ⟨k, rfl⟩

lemma dhSchemeFb_send_of_roleOk {Pt : Type} [Zero Pt] (Dh : DHFun (BitVec 256) Pt)
    {P : Party} {t : ℕ} {γ : CKA.DDH.State (BitVec 256) Pt}
    (hRole : DdhRoleOk P t γ) (hSend : P.sendsIn (t + 1) = true) (r : BitVec 256) :
    (dhSchemeFb Dh).send γ r = (dhScheme Dh).send γ r ∧
      DdhRoleOk P (t + 1) ((dhScheme Dh).send γ r).1 := by
  unfold DdhRoleOk at hRole ⊢
  rw [hSend] at hRole
  simp only [↓reduceIte] at hRole
  rcases hRole with ⟨T, rfl⟩
  rw [sendsIn_succ, hSend]
  exact ⟨rfl, ⟨r, rfl⟩⟩

lemma dhSchemeFb_receive_of_roleOk {Pt : Type} [Zero Pt] (Dh : DHFun (BitVec 256) Pt)
    {P : Party} {t : ℕ} {γ : CKA.DDH.State (BitVec 256) Pt}
    (hRole : DdhRoleOk P t γ) (hRecv : P.sendsIn (t + 1) = false) (T : Pt) :
    (dhSchemeFb Dh).receive γ T = (dhScheme Dh).receive γ T ∧
      DdhRoleOk P (t + 1) ((dhScheme Dh).receive γ T).1 := by
  unfold DdhRoleOk at hRole ⊢
  rw [hRecv] at hRole
  simp only [Bool.false_eq_true, ↓reduceIte] at hRole
  rcases hRole with ⟨x, rfl⟩
  rw [sendsIn_succ, hRecv]
  exact ⟨rfl, ⟨T, rfl⟩⟩

end PartyParity

section CkaGameBridge

variable {Pt : Type} [Zero Pt]

/-- Ping-pong state invariant for `CKA.GameState` on `dhScheme Dh`. -/
def CkaStateInv (s : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) : Prop :=
  (∀ P, DdhRoleOk P (s.epoch P) (s.st P)) ∧
  (s.epoch .A = s.epoch .B ∨
    (s.epoch .A = s.epoch .B + 1 ∧ Party.A.sendsIn (s.epoch .A) = true) ∨
    (s.epoch .B = s.epoch .A + 1 ∧ Party.B.sendsIn (s.epoch .B) = true))

lemma ckaStateInv_init (Dh : DHFun (BitVec 256) Pt) (k : BitVec 256) (b : Bool) :
    CkaStateInv (CKA.initState (dhScheme Dh) k b) := by
  refine ⟨fun P => ?_, Or.inl rfl⟩
  cases P
  · exact ddhRoleOk_initA Dh k
  · exact ddhRoleOk_initB Dh k

omit [Zero Pt] in
lemma ckaStateInv_afterSend {s : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt}
    (hs : CkaStateInv s) {P : Party} (hCan : s.canSend P = true)
    {γ' : CKA.DDH.State (BitVec 256) Pt} (hγ' : DdhRoleOk P (s.epoch P + 1) γ') (T : Pt) :
    CkaStateInv (s.afterSend P γ' T) := by
  unfold CKA.GameState.canSend at hCan
  rw [Bool.and_eq_true, beq_iff_eq] at hCan
  refine ⟨fun Q => ?_, ?_⟩
  · by_cases hQP : Q = P
    · subst hQP; simpa [CKA.GameState.afterSend] using hγ'
    · simpa [CKA.GameState.afterSend, hQP] using hs.1 Q
  · cases P
    · right; left
      simpa [CKA.GameState.afterSend, hCan.1] using hCan.2
    · right; right
      simpa [CKA.GameState.afterSend, hCan.1] using hCan.2

omit [Zero Pt] in
lemma ckaStateInv_canReceive_not_sendsIn {s : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt}
    (hs : CkaStateInv s) {P : Party} (hCan : s.canReceive P = true) :
    P.sendsIn (s.epoch P + 1) = false := by
  unfold CKA.GameState.canReceive at hCan
  rw [beq_iff_eq] at hCan
  cases P <;> simp only [Party.other_A, Party.other_B] at hCan
  · rcases hs.2 with hEq | ⟨hEq, _⟩ | ⟨hEq, hB⟩
    · omega
    · omega
    · rw [hCan] at hB
      have := sendsIn_other .B (s.epoch .A + 1)
      rw [Party.other_B, hB] at this
      exact this
  · rcases hs.2 with hEq | ⟨hEq, hA⟩ | ⟨hEq, _⟩
    · omega
    · rw [hCan] at hA
      have := sendsIn_other .A (s.epoch .B + 1)
      rw [Party.other_A, hA] at this
      exact this
    · omega

omit [Zero Pt] in
lemma ckaStateInv_afterReceive {s : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt}
    (hs : CkaStateInv s) {P : Party} (hCan : s.canReceive P = true)
    {γ' : CKA.DDH.State (BitVec 256) Pt} (hγ' : DdhRoleOk P (s.epoch P + 1) γ') :
    CkaStateInv (s.afterReceive P γ') := by
  unfold CKA.GameState.canReceive at hCan
  rw [beq_iff_eq] at hCan
  refine ⟨fun Q => ?_, Or.inl ?_⟩
  · by_cases hQP : Q = P
    · subst hQP; simpa [CKA.GameState.afterReceive] using hγ'
    · simpa [CKA.GameState.afterReceive, hQP] using hs.1 Q
  · cases P <;> simp only [Party.other_A, Party.other_B] at hCan <;>
      simp [CKA.GameState.afterReceive] <;> omega

lemma ckaOracleImpl_dhSchemeFb_eq [SampleableType Pt] (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ)
    (q : (CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt).Domain)
    (s : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) (hs : CkaStateInv s) :
    (CKA.oracleImpl (dhSchemeFb Dh) Δ tStar q).run s =
      (CKA.oracleImpl (dhScheme Dh) Δ tStar q).run s ∧
    ∀ res ∈ support ((CKA.oracleImpl (dhScheme Dh) Δ tStar q).run s), CkaStateInv res.2 := by
  rcases q with (((P | ⟨P, r⟩) | P) | P) | P
  · dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inl]
    unfold CKA.sendImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hbad : (!(s.canSend P) || s.epoch P + 1 == tStar) = true
    · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => h ▸ hs⟩
    · simp only [Bool.not_eq_true] at hbad
      have hCan : s.canSend P = true := by
        rcases Bool.or_eq_false_iff.mp hbad with ⟨h1, _⟩; simpa using h1
      have hSend : P.sendsIn (s.epoch P + 1) = true :=
        (Bool.and_eq_true_iff.mp hCan).2
      simp only [hbad, Bool.false_eq_true, ↓reduceIte]
      have hL : ∀ (cka : CKAScheme (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt),
          (do
            let r' ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
              StateT (CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) ProbComp (BitVec 256))
            let out := cka.send (s.st P) r'
            set (s.afterSend P out.1 out.2.1)
            pure (some out.2)).run s =
          (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun r' =>
            let out := cka.send (s.st P) r'
            pure (some out.2, s.afterSend P out.1 out.2.1)) := by
        intro cka
        simp [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set]
      rw [hL (dhSchemeFb Dh), hL (dhScheme Dh)]
      refine ⟨bind_congr fun r' => ?_, fun res hmem => ?_⟩
      · rw [(dhSchemeFb_send_of_roleOk Dh (hs.1 P) hSend r').1]
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
        rcases hmem with ⟨r', _, rfl⟩
        exact ckaStateInv_afterSend hs hCan
          (dhSchemeFb_send_of_roleOk Dh (hs.1 P) hSend r').2 _
  · dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    unfold CKA.sendWithAdversaryCoinsImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hbad : (!(s.canSend P) || !decide (s.epoch P + 1 + 2 ≤ tStar)) = true
    · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => h ▸ hs⟩
    · simp only [Bool.not_eq_true] at hbad
      have hCan : s.canSend P = true := by
        rcases Bool.or_eq_false_iff.mp hbad with ⟨h1, _⟩; simpa using h1
      have hSend : P.sendsIn (s.epoch P + 1) = true :=
        (Bool.and_eq_true_iff.mp hCan).2
      have ⟨hEq, hRole'⟩ := dhSchemeFb_send_of_roleOk Dh (hs.1 P) hSend r
      simp only [hbad, Bool.false_eq_true, ↓reduceIte, hEq, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => h ▸ ckaStateInv_afterSend hs hCan hRole' _⟩
  · dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    unfold CKA.challImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hbad : (!(s.canSend P) || s.epoch P + 1 != tStar) = true
    · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => h ▸ hs⟩
    · simp only [Bool.not_eq_true] at hbad
      have hCan : s.canSend P = true := by
        rcases Bool.or_eq_false_iff.mp hbad with ⟨h1, _⟩; simpa using h1
      have hSend : P.sendsIn (s.epoch P + 1) = true :=
        (Bool.and_eq_true_iff.mp hCan).2
      simp only [hbad, Bool.false_eq_true, ↓reduceIte]
      have hL : ∀ (cka : CKAScheme (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt),
          (do
            let r' ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
              StateT (CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) ProbComp (BitVec 256))
            let out := cka.send (s.st P) r'
            set (s.afterSend P out.1 out.2.1)
            if s.b then do
              let I' ← (liftM ($ᵗ Pt : ProbComp Pt) :
                StateT (CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) ProbComp Pt)
              pure (some (out.2.1, I'))
            else pure (some out.2)).run s =
          (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun r' =>
            let out := cka.send (s.st P) r'
            let s' := s.afterSend P out.1 out.2.1
            if s.b then ($ᵗ Pt : ProbComp Pt) >>= fun I' => pure (some (out.2.1, I'), s')
            else pure (some out.2, s')) := by
        intro cka
        by_cases hb : s.b = true <;>
          simp [hb, StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set]
      rw [hL (dhSchemeFb Dh), hL (dhScheme Dh)]
      refine ⟨bind_congr fun r' => ?_, fun res hmem => ?_⟩
      · rw [(dhSchemeFb_send_of_roleOk Dh (hs.1 P) hSend r').1]
      · simp only [mem_support_bind_iff] at hmem
        rcases hmem with ⟨r', _, hmem2⟩
        have hInv' := ckaStateInv_afterSend hs hCan
          (dhSchemeFb_send_of_roleOk Dh (hs.1 P) hSend r').2 ((dhScheme Dh).send (s.st P) r').2.1
        by_cases hb : s.b = true
        · simp only [hb, ↓reduceIte, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hmem2
          rcases hmem2 with ⟨_, _, rfl⟩
          exact hInv'
        · simp only [Bool.not_eq_true] at hb
          simp only [hb, Bool.false_eq_true, ↓reduceIte, support_pure,
            Set.mem_singleton_iff] at hmem2
          exact hmem2 ▸ hInv'
  · dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    unfold CKA.receiveImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hbad : (!(s.canReceive P)) = true
    · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => h ▸ hs⟩
    · simp only [Bool.not_eq_true, Bool.not_eq_false'] at hbad
      simp only [hbad, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases hlm : s.lastMsg with _ | T
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => h ▸ hs⟩
      · have hRecv := ckaStateInv_canReceive_not_sendsIn hs hbad
        have ⟨hEq, hRole'⟩ := dhSchemeFb_receive_of_roleOk Dh (hs.1 P) hRecv T
        simp only [hEq, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => h ▸ ckaStateInv_afterReceive hs hbad hRole'⟩
  · dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inr]
    unfold CKA.corrImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] <;>
      exact ⟨trivial, fun _ h => h ▸ hs⟩

lemma simulateQ_ckaImpl_dhSchemeFb_eq [SampleableType Pt] (Dh : DHFun (BitVec 256) Pt)
    (Δ tStar : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) α)
    (s : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) (hs : CkaStateInv s) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) ProbComp) +
        CKA.oracleImpl (dhSchemeFb Dh) Δ tStar) oa).run s =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) ProbComp) +
        CKA.oracleImpl (dhScheme Dh) Δ tStar) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => rfl
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | q_cka
    · change (StateT.lift ($ᵗ (Fin (n + 1)) : ProbComp (Fin (n + 1)))).run s >>= _ =
        (StateT.lift ($ᵗ (Fin (n + 1)) : ProbComp (Fin (n + 1)))).run s >>= _
      simp only [StateT.run_lift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u s hs
    · change (CKA.oracleImpl (dhSchemeFb Dh) Δ tStar q_cka).run s >>= _ =
        (CKA.oracleImpl (dhScheme Dh) Δ tStar q_cka).run s >>= _
      obtain ⟨hEq, hInv⟩ := ckaOracleImpl_dhSchemeFb_eq Dh Δ tStar q_cka s hs
      rw [hEq]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, s'⟩ hmem =>
        ih u s' (hInv (u, s') hmem)

theorem ckaBranch_dhSchemeFb_eq [SampleableType Pt] (Dh : DHFun (BitVec 256) Pt)
    (Δ tStar : ℕ) (b : Bool)
    (A : CKA.Adversary (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) :
    CKA.branch (dhSchemeFb Dh) Δ tStar b A = CKA.branch (dhScheme Dh) Δ tStar b A := by
  unfold CKA.branch
  refine bind_congr fun k => ?_
  have hinit : CKA.initState (dhSchemeFb Dh) k b = CKA.initState (dhScheme Dh) k b := rfl
  rw [hinit, StateT.run'_eq, StateT.run'_eq]
  exact congrArg (Prod.fst <$> ·) (simulateQ_ckaImpl_dhSchemeFb_eq Dh Δ tStar A _
    (ckaStateInv_init Dh k b))

end CkaGameBridge

section RSReachCapBridge

/-- Step-capped `RSReachB` invariant: for `k ≤ qMax`, `rs` satisfies `RSReachB maxSkip k rs`. -/
def RSReachCap {CK MK : Type} (maxSkip qMax k : ℕ)
    (v : FSAEAD.RatchetReceiverState CK MK) : Prop :=
  k ≤ qMax → RSReachB maxSkip k v

lemma rsReachCap_init {CK MK AD M C : Type}
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip qMax : ℕ) (k : CK) :
    RSReachCap maxSkip qMax 0 ((FSAEAD.fromAEADPRG ae G maxSkip).initReceiver k) :=
  fun _ => RSReachB.init ae G maxSkip k

lemma rsReachCap_mono {CK MK : Type} {maxSkip qMax k k' : ℕ}
    {v : FSAEAD.RatchetReceiverState CK MK}
    (hle : k ≤ k') (h : RSReachCap maxSkip qMax k v) : RSReachCap maxSkip qMax k' v :=
  fun hk' => (h (Nat.le_trans hle hk')).mono hle

lemma rsReachCap_init_fsAtomicB {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B0 qMax : ℕ) (k : BitVec 256) :
    RSReachCap maxForwardJumps qMax 0 ((fsAtomicB C ℓ encT idOf B0).initReceiver k) :=
  rsReachCap_init (lAead C protoSignalCodec ℓ encT idOf |>.movePubPartToAD (lPubOf protoSignalCodec))
    (lChainPRG C.F) maxForwardJumps qMax k

lemma rsReachCap_len_le {CK MK : Type} {maxSkip qMax B0 k : ℕ}
    (hB0 : (qMax + 1) * (maxSkip + 1) ≤ B0) {v : FSAEAD.RatchetReceiverState CK MK}
    (hv : RSReachCap maxSkip qMax k v) (hk : k ≤ qMax) :
    v.skippedKeys.length ≤ B0 := by
  have hb := hv hk
  have h1 := hb.1.1
  have h2 := hb.2
  have h3 : k * (maxSkip + 1) ≤ (qMax + 1) * (maxSkip + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

lemma rsReachCap_receive_fsAtomicB {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) {qMax B0 k : ℕ}
    (hB0 : (qMax + 1) * (maxForwardJumps + 1) ≤ B0)
    {v v' : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)}
    {hdr : Header Pt} {e : ℕ × LibsignalCiphertextWithSalt32}
    {i : ℕ} {m : LibsignalMsgPublicPart × Plain ℓ}
    (hv : RSReachCap maxForwardJumps qMax k v)
    (hrec : (fsAtomicB C ℓ encT idOf B0).receive v hdr e = some (v', i, m)) :
    RSReachCap maxForwardJumps qMax (k + 1) v' := by
  intro hk1
  have hk : k ≤ qMax := by omega
  have hlen := rsReachCap_len_le hB0 hv hk
  rw [fsAtomicB_receive_eq C ℓ encT idOf B0 v hdr e hlen] at hrec
  exact (RSReachB.receive_fromAEADPRG
    ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
    (lChainPRG C.F) maxForwardJumps k (hv hk) hrec).2

lemma rsReachCap_fsB {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) {qMax B0 : ℕ}
    (hB0 : (qMax + 1) * (maxForwardJumps + 1) ≤ B0)
    (rs : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rs' : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
    (i : ℕ) (m : LibsignalMsgPublicPart × Plain ℓ)
    (hv : RSReachCap maxForwardJumps qMax qMax rs)
    (hrec : (fsAtomicB C ℓ encT idOf B0).receive rs hdr e = some (rs', i, m)) :
    i ≤ B0 := by
  have hlen := rsReachCap_len_le hB0 hv (le_rfl)
  rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen] at hrec
  have hi := (RSReachB.receive_fromAEADPRG
    ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
    (lChainPRG C.F) maxForwardJumps qMax (hv le_rfl) hrec).1
  omega

lemma hooksCKA_vrInv_fsAtomicB {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {qMax B0 : ℕ} (hB0 : (qMax + 1) * (maxForwardJumps + 1) ≤ B0)
    (Δcka : ℕ) (mo : Mode) :
    HooksVRInv (RSReachCap maxForwardJumps qMax)
      (hooksCKA cka prng (fsAtomicB C ℓ encT idOf B0) Δcka mo) where
  mono hle hv := rsReachCap_mono hle hv
  startRecv_step ctx P t γ σ Tn h :=
    hooksCKA_startRecv_rs cka prng (fsAtomicB C ℓ encT idOf B0) Δcka mo
      (rsReachCap_init_fsAtomicB C ℓ encT idOf B0 qMax) ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksCKA] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact rsReachCap_receive_fsAtomicB C ℓ encT idOf hB0 hVR hmem.1.symm
  commit_vR := hooksCKA_commit_vR cka prng (fsAtomicB C ℓ encT idOf B0) Δcka mo

lemma hooksPRNG_vrInv_fsAtomicB {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {qMax B0 : ℕ} (hB0 : (qMax + 1) * (maxForwardJumps + 1) ≤ B0) (mo : Mode) :
    HooksVRInv (RSReachCap maxForwardJumps qMax)
      (hooksPRNG cka prng (fsAtomicB C ℓ encT idOf B0) mo) where
  mono hle hv := rsReachCap_mono hle hv
  startRecv_step ctx P t γ σv Tn h :=
    hooksPRNG_startRecv_rs cka prng (fsAtomicB C ℓ encT idOf B0) mo
      (rsReachCap_init_fsAtomicB C ℓ encT idOf B0 qMax) ctx P t γ σv Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksPRNG] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact rsReachCap_receive_fsAtomicB C ℓ encT idOf hB0 hVR hmem.1.symm
  commit_vR := hooksPRNG_commit_vR cka prng (fsAtomicB C ℓ encT idOf B0) mo

end RSReachCapBridge

section EngineStepHelpers

open CryptoGames.LibsignalSM.Proofs

lemma mode_cfg_challMsg {M : Type} (mo : Mode) (t : ℕ) :
    (mo.cfg (M := M)).challMsg t = none := by
  rcases mo with ⟨auth, _, _⟩
  cases auth <;> rfl

lemma badSendMsg_query_bind_step {St Msg Coins C α : Type} (ok : Msg → Bool)
    (qy : (unifSpec + SM.spec St Msg Coins C).Domain)
    (mx : (unifSpec + SM.spec St Msg Coins C).Range qy → SM.AdversaryComp St Msg Coins C α)
    (h : IsQueryBoundP
      ((liftM (OracleSpec.query qy) : OracleComp (unifSpec + SM.spec St Msg Coins C) _) >>= mx)
      (fun t => SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) ok t = true) 0) :
    SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) ok qy = false ∧
      ∀ u, IsQueryBoundP (mx u)
        (fun t => SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) ok t = true) 0 := by
  rw [isQueryBoundP_query_bind_iff] at h
  rcases h with ⟨hq0, hmx⟩
  have hnb : ¬ (SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) ok qy = true) :=
    hq0.resolve_right (by omega)
  have hbf : SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) ok qy = false :=
    Bool.eq_false_iff.mpr hnb
  refine ⟨hbf, fun u => ?_⟩
  have hu := hmx u
  simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hu
  exact hu

lemma badSendMsg_transmit_false {St Msg Coins C : Type} {ok : Msg → Bool}
    {P : Party} {m : Msg} {r : Option Coins}
    (h : SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) ok
      (.inr (.inl (.inl (.inl (.inl (P, m, r)))))) = false) :
    ok m = true := by
  simpa [SessionShort.badSendMsg] using h

lemma badSendMsg_chall_false {St Msg Coins C : Type} {ok : Msg → Bool}
    {P : Party} {m₀ m₁ : Msg} {r : Option Coins}
    (h : SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) ok
      (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) = false) :
    ok m₀ = true ∧ ok m₁ = true := by
  simpa [SessionShort.badSendMsg, Bool.or_eq_false_iff] using h

/-- Local party-role invariant for `hooksPRNG` and `hooksFS` (where virtual CKA state is `Γ`). -/
def LocalPartyInv {Pt σV ssV rsV : Type} (P : Party)
    (vp : VP (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) : Prop :=
  vp.id = P ∧ DdhRoleOk P vp.tcur vp.γ

lemma localPartyInv_mkParties {Pt σV ssV rsV : Type} [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (kc : BitVec 256) (σ : σV) (ssB : ssV) (rsA : rsV) :
    let ab := mkParties (T := Pt) ((dhScheme Dh).initA kc) ((dhScheme Dh).initB kc) σ ssB rsA
    ∀ P : Party, LocalPartyInv P (match P with | .A => ab.1 | .B => ab.2) := by
  intro ab P
  cases P
  · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
  · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩

lemma afterCorr_st_eq {St Msg C : Type} (s : SM.GameState St Msg C) (P : Party) :
    (s.afterCorr P).st = s.st := rfl

lemma record_st_eq {St Msg C : Type} (s : SM.GameState St Msg C)
    (Δ : ℕ) (P : Party) (st' : St) (r : SM.Record Msg C) (isChall : Bool) :
    (s.record Δ P st' r isChall).st = Function.update s.st P st' := rfl

lemma accept_st_eq {St Msg C : Type} (s : SM.GameState St Msg C)
    (P : Party) (st' : St) (pos : SM.Pos) :
    (s.accept P st' pos).st = Function.update s.st P st' := rfl

end EngineStepHelpers

section LocalCKASwap

variable {Pt RSt SS RS M E σV ssV rsV HS ι : Type} {TSpec : OracleSpec.{0, 0} ι}

/-- Agreement of two `Hooks` (`dhSchemeFb Dh` vs `dhScheme Dh`) when virtual CKA states are local. -/
structure HooksLocalCKAAgree (PInv : Party → CKA.DDH.State (BitVec 256) Pt → ℕ → Prop)
    (hk₁ hk₂ : Hooks TSpec HS (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E (BitVec 256)
      (CKA.DDH.State (BitVec 256) Pt) σV ssV rsV) : Prop where
  startSend_eq : ∀ ctx P t γ σ r h, 1 ≤ t → P.sendsIn t = true → PInv P γ (t - 1) →
    (hk₁.startSend ctx P t γ σ r).run h = (hk₂.startSend ctx P t γ σ r).run h ∧
    ∀ q ∈ support ((hk₂.startSend ctx P t γ σ r).run h),
      ∀ γ' T' σ' ss, q.1 = some (γ', T', σ', ss) → PInv P γ' t
  startRecv_eq : ∀ ctx P t γ σ Tn h, 1 ≤ t → P.sendsIn t = false → PInv P γ (t - 1) →
    (hk₁.startRecv ctx P t γ σ Tn).run h = (hk₂.startRecv ctx P t γ σ Tn).run h ∧
    ∀ q ∈ support ((hk₂.startRecv ctx P t γ σ Tn).run h),
      ∀ γ' σ' rs, q.1 = some (some (γ', σ', rs)) → PInv P γ' t
  fsSend_eq : hk₁.fsSend = hk₂.fsSend
  fsRecv_eq : hk₁.fsRecv = hk₂.fsRecv
  commit_eq : ∀ ctx P old new, hk₁.commit ctx P old new = pure (some new) ∧
    hk₂.commit ctx P old new = pure (some new)
  reveal_eq : hk₁.reveal = hk₂.reveal

lemma vSend_localCKA_eq [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E (BitVec 256)
      (CKA.DDH.State (BitVec 256) Pt) σV ssV rsV}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (ctx : Ctx (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV M E) (P : Party)
    (s : VP (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) (m : M) (pair : Option (M × M))
    (r : Option (BitVec 256)) (h : HS) (hs : LocalPartyInv P s) :
    (vSend hk₁ ctx P s m pair r).run h = (vSend hk₂ ctx P s m pair r).run h ∧
    ∀ res ∈ support ((vSend hk₂ ctx P s m pair r).run h),
      ∀ st' ct, res.1 = some (st', ct) → LocalPartyInv P st' := by
  rw [vSend_eq_bind, vSend_eq_bind, StateT.run_bind, StateT.run_bind]
  have hStep1 : (vSendStep1 hk₁ ctx P s r).run h = (vSendStep1 hk₂ ctx P s r).run h ∧
      ∀ p ∈ support ((vSendStep1 hk₂ ctx P s r).run h),
        ∀ s₁, p.1 = some s₁ → LocalPartyInv P s₁ := by
    unfold vSendStep1
    by_cases hSend : s.id.sendsIn (s.tcur + 1) = true
    · have hPSend : P.sendsIn (s.tcur + 1) = true := hs.1 ▸ hSend
      have hss := hAg.startSend_eq ctx P (s.tcur + 1) s.γ s.root r h (Nat.le_add_left 1 s.tcur)
        hPSend (by simpa using hs.2)
      simp only [hSend, ↓reduceIte, StateT.run_bind, hss.1]
      refine ⟨trivial, fun p hp s₁ hs₁ => ?_⟩
      rw [mem_support_bind_iff] at hp
      obtain ⟨⟨q, h₁⟩, hq, hp⟩ := hp
      rcases q with _ | ⟨γ', T', σ', ss⟩ <;>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp <;> subst hp
      · cases hs₁
      · cases hs₁; exact ⟨hs.1, hss.2 _ hq γ' T' σ' ss rfl⟩
    · simp only [hSend, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff]
      exact ⟨trivial, fun p hp s₁ hs₁ => by subst hp; cases hs₁; exact hs⟩
  rw [hStep1.1]
  refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun _ _ => by simp only [hAg.fsSend_eq],
    fun res hmem st' ct hEq => ?_⟩
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hp, hmem2⟩ := hmem
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
    subst hmem2; cases hEq
  · have hs₁ := hStep1.2 _ hp s₁ rfl
    rcases hvS : s₁.vS with _ | v
    · simp only [hvS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
      subst hmem2; cases hEq; exact hs₁
    · simp only [hvS, StateT.run_bind, mem_support_bind_iff] at hmem2
      obtain ⟨⟨fsRes, h₂⟩, _, hmem2⟩ := hmem2
      rcases fsRes with _ | ⟨v', e⟩ <;>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2 <;>
        subst hmem2 <;> cases hEq
      exact hs₁

lemma vRecv_localCKA_eq
    {hk₁ hk₂ : Hooks TSpec HS (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E (BitVec 256)
      (CKA.DDH.State (BitVec 256) Pt) σV ssV rsV}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (ctx : Ctx (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV M E) (P : Party)
    (s : VP (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) (c : Header Pt × E)
    (rec_ : Option (Record M (Header Pt × E))) (h : HS) (hs : LocalPartyInv P s) :
    (vRecv hk₁ ctx P s c rec_).run h = (vRecv hk₂ ctx P s c rec_).run h ∧
    ∀ res ∈ support ((vRecv hk₂ ctx P s c rec_).run h),
      ∀ st' t' i' m', res.1 = some (some (st', t', i', m')) → LocalPartyInv P st' := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    exact ⟨trivial, fun res hmem _ _ _ _ hEq => by subst hmem; cases hEq⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hNotSend : s.id.sendsIn c.1.1 = false := by
      rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr href) with ⟨h1, _⟩; exact h1
    have hStep1 : (vRecvStep1 hk₁ ctx P s c).run h = (vRecvStep1 hk₂ ctx P s c).run h ∧
        ∀ p ∈ support ((vRecvStep1 hk₂ ctx P s c).run h),
          ∀ s₁, p.1 = some (some s₁) → LocalPartyInv P s₁ := by
      unfold vRecvStep1
      by_cases ht : c.1.1 = s.tcur + 1
      · simp only [ht, ↓reduceIte]
        rcases hTn : c.1.2 with _ | Tn
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun p hp _ hEq => by subst hp; cases hEq⟩
        · have hPRecv : P.sendsIn (s.tcur + 1) = false := by
            rw [← hs.1, ← ht]; exact hNotSend
          have hsr := hAg.startRecv_eq ctx P (s.tcur + 1) s.γ s.root Tn h (Nat.le_add_left 1 s.tcur)
            hPRecv (by simpa using hs.2)
          simp only [StateT.run_bind, hsr.1]
          refine ⟨trivial, fun p hp s₁ hs₁ => ?_⟩
          rw [mem_support_bind_iff] at hp
          obtain ⟨⟨q, h₁⟩, hq, hp⟩ := hp
          rcases q with _ | _ | ⟨γ', σ', rs⟩ <;>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp <;> subst hp
          · cases hs₁
          · cases hs₁
          · cases hs₁; exact ⟨hs.1, hsr.2 _ hq γ' σ' rs rfl⟩
      · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun p hp s₁ hs₁ => by subst hp; cases hs₁; exact hs⟩
    rw [hStep1.1]
    refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun _ _ => by simp only [hAg.fsRecv_eq],
      fun res hmem st' t' i' m' hEq => ?_⟩
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hp, hmem2⟩ := hmem
    rcases s₁? with _ | (_ | s₁)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
      subst hmem2; cases hEq
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
      subst hmem2; cases hEq
    · have hs₁ := hStep1.2 _ hp s₁ rfl
      rcases hvR : s₁.vR c.1.1 with _ | v
      · simp only [hvR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
        subst hmem2; cases hEq
      · simp only [hvR, StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨fsRes, h₂⟩, _, hmem2⟩ := hmem2
        rcases fsRes with _ | _ | ⟨v', i', m'⟩ <;>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2 <;>
          subst hmem2 <;> cases hEq
        exact hs₁

def AllPartiesInv (es : EState (VP (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) M (Header Pt × E) HS) :
    Prop :=
  ∀ P : Party, LocalPartyInv P (es.g.st P)

lemma commitE_localCKA_eq
    {hk₁ hk₂ : Hooks TSpec HS (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E (BitVec 256)
      (CKA.DDH.State (BitVec 256) Pt) σV ssV rsV}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (s : Ctx (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV M E) (P : Party)
    (old new : VP (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) (pos : SM.Pos)
    (es : EState (VP (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) M (Header Pt × E) HS)
    (hS : ∀ Q, LocalPartyInv Q (s.st Q)) (hNew : LocalPartyInv P new) :
    (commitE hk₁ s P old new pos).run es = (commitE hk₂ s P old new pos).run es ∧
    ∀ res ∈ support ((commitE hk₂ s P old new pos).run es),
      res.2.g = es.g ∧ ∀ s₁, res.1 = some s₁ → ∀ Q, LocalPartyInv Q (s₁.st Q) := by
  unfold commitE
  simp only [run_liftH_bind, (hAg.commit_eq (s.accept P new pos) P old new).1,
    (hAg.commit_eq (s.accept P new pos) P old new).2, StateT.run_pure, pure_bind,
    support_pure, Set.mem_singleton_iff]
  refine ⟨trivial, fun res hmem => ?_⟩
  subst hmem
  refine ⟨rfl, fun s₁ hs₁ Q => ?_⟩
  cases hs₁
  by_cases hQP : Q = P
  · subst hQP; simp [hNew]
  · simp [Function.update_of_ne hQP, accept_st_eq, hS Q]

lemma implE_localCKA_eq [DecidableEq Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E (BitVec 256)
      (CKA.DDH.State (BitVec 256) Pt) σV ssV rsV}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) M (Header Pt × E) HS)
    (t : (SM.spec (PartyState (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E)).Domain)
    (hEs : AllPartiesInv es) :
    (implE hk₁ Δ qep maxSkip cfg π (.inr t)).run es =
      (implE hk₂ Δ qep maxSkip cfg π (.inr t)).run es ∧
    ∀ res ∈ support ((implE hk₂ Δ qep maxSkip cfg π (.inr t)).run es), AllPartiesInv res.2 := by
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · have hI₁ : implE hk₁ Δ qep maxSkip cfg π (.inr (.inl (.inl (.inl (.inl (P, m, r)))))) =
        transmitE hk₁ Δ qep π (P, m, r) := rfl
    have hI₂ : implE hk₂ Δ qep maxSkip cfg π (.inr (.inl (.inl (.inl (.inl (P, m, r)))))) =
        transmitE hk₂ Δ qep π (P, m, r) := rfl
    rw [hI₁, hI₂]; unfold transmitE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
      · by_cases hdoom : π.leakDoom es.g s₁ = true
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
        · have hs₁P : LocalPartyInv P (s₁.st P) := by rw [Engine.epMgmt_st_eq hep]; exact hEs P
          have hvs := vSend_localCKA_eq hAg s₁ P (s₁.st P) m none r es.h hs₁P
          simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvs.1]
          refine ⟨trivial, fun res hmem => ?_⟩
          rw [mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvsMem, hmem⟩ := hmem
          rcases vsRes with _ | ⟨st', ct⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hEs
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; intro Q
            by_cases hQP : Q = P
            · subst hQP; simp [record_st_eq, hvs.2 _ hvsMem st' ct rfl]
            · simp [record_st_eq, Function.update_of_ne hQP, Engine.epMgmt_st_eq hep, hEs Q]
  · have hI₁ : implE hk₁ Δ qep maxSkip cfg π (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) =
        challE hk₁ Δ qep cfg π (P, m₀, m₁, r) := rfl
    have hI₂ : implE hk₂ Δ qep maxSkip cfg π (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) =
        challE hk₂ Δ qep cfg π (P, m₀, m₁, r) := rfl
    rw [hI₁, hI₂]; unfold challE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
      · by_cases hch : (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P))) = true
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          by_cases hdoom : π.leakDoom es.g s₁ = true
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
          · have hs₁P : LocalPartyInv P (s₁.st P) := by rw [Engine.epMgmt_st_eq hep]; exact hEs P
            have hvs := vSend_localCKA_eq hAg s₁ P (s₁.st P)
              ((cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀))
              (some (m₀, m₁)) r es.h hs₁P
            simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvs.1]
            refine ⟨trivial, fun res hmem => ?_⟩
            rw [mem_support_bind_iff] at hmem
            obtain ⟨⟨vsRes, h'⟩, hvsMem, hmem⟩ := hmem
            rcases vsRes with _ | ⟨st', ct⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact hEs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; intro Q
              by_cases hQP : Q = P
              · subst hQP; simp [record_st_eq, hvs.2 _ hvsMem st' ct rfl]
              · simp [record_st_eq, Function.update_of_ne hQP, Engine.epMgmt_st_eq hep, hEs Q]
  · have hI₁ : implE hk₁ Δ qep maxSkip cfg π (.inr (.inl (.inl (.inr (P, c))))) =
        deliverE hk₁ maxSkip cfg (P, c) := rfl
    have hI₂ : implE hk₂ Δ qep maxSkip cfg π (.inr (.inl (.inl (.inr (P, c))))) =
        deliverE hk₂ maxSkip cfg (P, c) := rfl
    rw [hI₁, hI₂]; unfold deliverE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
      · have hvr := vRecv_localCKA_eq hAg es.g P (es.g.st P) c (some r) es.h (hEs P)
        simp only [run_liftH_bind, hvr.1]
        refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvrMem => ?_,
          fun res hmem => ?_⟩
        · rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · rfl
          · rfl
          · simp only [StateT.run_bind]
            rw [(commitE_localCKA_eq hAg es.g P (es.g.st P) st' r.pos { es with h := h' }
              hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).1]
        · rw [mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h'⟩, hvrMem, hmem⟩ := hmem
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hEs
          · split_ifs at hmem <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff] at hmem;
               subst hmem; exact hEs)
          · rw [StateT.run_bind, mem_support_bind_iff] at hmem
            obtain ⟨⟨cmRes, es₁⟩, hcmMem, hmem⟩ := hmem
            have hcm := (commitE_localCKA_eq hAg es.g P (es.g.st P) st' r.pos { es with h := h' }
              hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).2 _ hcmMem
            rcases cmRes with _ | s₁
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; intro Q; dsimp [AllPartiesInv] at *; rw [hcm.1]; exact hEs Q
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; intro Q
              split_ifs <;> exact hcm.2 s₁ rfl Q
  · have hI₁ : implE hk₁ Δ qep maxSkip cfg π (.inr (.inl (.inr (P, c)))) =
        injectE hk₁ Δ qep cfg (P, c) := rfl
    have hI₂ : implE hk₂ Δ qep maxSkip cfg π (.inr (.inl (.inr (P, c)))) =
        injectE hk₂ Δ qep cfg (P, c) := rfl
    rw [hI₁, hI₂]; unfold injectE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ)) = true
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
    · have hvr := vRecv_localCKA_eq hAg es.g P (es.g.st P) c none es.h (hEs P)
      simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvr.1]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvrMem => ?_,
        fun res hmem => ?_⟩
      · rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · rfl
        · rfl
        · by_cases hqep : qep + 1 < t'
          · simp [hqep]
          · simp only [hqep, ↓reduceIte]
            by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind]
              rw [(commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).1]
            · simp [htriv]
      · rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvrMem, hmem⟩ := hmem
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hEs
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hEs
        · by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hEs
          · simp only [hqep, ↓reduceIte] at hmem
            by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨cmRes, es₁⟩, hcmMem, hmem⟩ := hmem
              have hcm := (commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).2 _ hcmMem
              rcases cmRes with _ | s₁
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; intro Q; dsimp [AllPartiesInv] at *; rw [hcm.1]; exact hEs Q
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact hcm.2 s₁ rfl
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              split_ifs at hmem <;>
                (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                   support_pure, Set.mem_singleton_iff] at hmem;
                 subst hmem; exact hEs)
  · have hI₁ : implE hk₁ Δ qep maxSkip cfg π (.inr (.inr P)) = corrE hk₁ π P := rfl
    have hI₂ : implE hk₂ Δ qep maxSkip cfg π (.inr (.inr P)) = corrE hk₂ π P := rfl
    rw [hI₁, hI₂]; unfold corrE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hAg.reveal_eq]
    refine ⟨trivial, fun res hmem => ?_⟩
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P)) = true
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hEs
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P) = true
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hEs
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
        rcases revRes with _ | stP <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             support_pure, Set.mem_singleton_iff] at hmem;
           subst hmem; exact hEs)

lemma simulateQ_implE_localCKA_eq [DecidableEq Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E (BitVec 256)
      (CKA.DDH.State (BitVec 256) Pt) σV ssV rsV}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) {α : Type}
    (oa : OracleComp (unifSpec + SM.spec (PartyState (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E)) α)
    (es : EState (VP (CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) M (Header Pt × E) HS)
    (hEs : AllPartiesInv es) :
    (simulateQ (implE hk₁ Δ qep maxSkip cfg π) oa).run es =
      (simulateQ (implE hk₂ Δ qep maxSkip cfg π) oa).run es := by
  induction oa using OracleComp.inductionOn generalizing es with
  | pure x => rfl
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · change (coinsE n).run es >>= _ = (coinsE n).run es >>= _
      simp only [coinsE, StateT.run_lift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u es hEs
    · obtain ⟨hEq, hInv⟩ := implE_localCKA_eq hAg Δ qep maxSkip cfg π es t_sm hEs
      change (implE hk₁ Δ qep maxSkip cfg π (.inr t_sm)).run es >>= _ =
        (implE hk₂ Δ qep maxSkip cfg π (.inr t_sm)).run es >>= _
      rw [hEq]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem =>
        ih u es' (hInv (u, es') hmem)

lemma hooksPRNG_localCKAAgree [DecidableEq Pt] [Zero Pt]
    {KR RSt K SS RS M E : Type}
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (mo : Mode) :
    HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ)
      (hooksPRNG (dhSchemeFb Dh) prng fs mo) (hooksPRNG (dhScheme Dh) prng fs mo) where
  startSend_eq ctx P t γ σv r h ht hSend hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hSend' : P.sendsIn ((t - 1) + 1) = true := ht1.symm ▸ hSend
    dsimp only [hooksPRNG]
    have hCoins : ∀ coins : BitVec 256,
        (do
          let rtRes ← Construction.rootPRNG prng mo t ((dhSchemeFb Dh).send γ coins).2.2 σv
          match rtRes with
          | none => pure none
          | some (σ', k) => do
            modify fun (s : PRNGState Pt RSt K) => { cache := Function.update s.cache t (some (((dhSchemeFb Dh).send γ coins).2.1, σ', k)) }
            pure (some (((dhSchemeFb Dh).send γ coins).1, ((dhSchemeFb Dh).send γ coins).2.1, σ', fs.initSender k))).run h =
        (do
          let rtRes ← Construction.rootPRNG prng mo t ((dhScheme Dh).send γ coins).2.2 σv
          match rtRes with
          | none => pure none
          | some (σ', k) => do
            modify fun (s : PRNGState Pt RSt K) => { cache := Function.update s.cache t (some (((dhScheme Dh).send γ coins).2.1, σ', k)) }
            pure (some (((dhScheme Dh).send γ coins).1, ((dhScheme Dh).send γ coins).2.1, σ', fs.initSender k))).run h ∧
        ∀ q ∈ support ((do
          let rtRes ← Construction.rootPRNG prng mo t ((dhScheme Dh).send γ coins).2.2 σv
          match rtRes with
          | none => pure none
          | some (σ', k) => do
            modify fun (s : PRNGState Pt RSt K) => { cache := Function.update s.cache t (some (((dhScheme Dh).send γ coins).2.1, σ', k)) }
            pure (some (((dhScheme Dh).send γ coins).1, ((dhScheme Dh).send γ coins).2.1, σ', fs.initSender k))).run h),
          ∀ γ' T' σ' ss, q.1 = some (γ', T', σ', ss) → DdhRoleOk P t γ' := by
      intro coins
      have hsnd := dhSchemeFb_send_of_roleOk Dh hRole hSend' coins
      have hRole' : DdhRoleOk P t ((dhScheme Dh).send γ coins).1 := ht1 ▸ hsnd.2
      simp only [hsnd.1]
      refine ⟨trivial, fun q hq γ' T' σ' ss hEq => ?_⟩
      rw [StateT.run_bind, mem_support_bind_iff] at hq
      obtain ⟨⟨rtRes, h₂⟩, _, hq⟩ := hq
      rcases rtRes with _ | ⟨σ₁, k₁⟩ <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           support_pure, Set.mem_singleton_iff] at hq;
         subst hq; cases hEq)
      exact hRole'
    rcases r with _ | c
    · simp only [StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind]
      refine ⟨bind_congr fun coins => (hCoins coins).1, fun q hq γ' T' σ' ss hEq => ?_⟩
      rw [mem_support_bind_iff] at hq
      obtain ⟨coins, _, hq⟩ := hq
      exact (hCoins coins).2 q hq γ' T' σ' ss hEq
    · simp only [pure_bind]
      exact hCoins c
  startRecv_eq ctx P t γ σv Tn h ht hRecv hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hRecv' : P.sendsIn ((t - 1) + 1) = false := ht1.symm ▸ hRecv
    have hrcv := dhSchemeFb_receive_of_roleOk Dh hRole hRecv' Tn
    have hRole' : DdhRoleOk P t ((dhScheme Dh).receive γ Tn).1 := ht1 ▸ hrcv.2
    dsimp only [hooksPRNG]
    simp only [hrcv.1]
    refine ⟨trivial, fun q hq γ' σ' rs hEq => ?_⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hq
    rcases hcache : h.cache t with _ | ⟨Tc, σc, kc⟩
    · simp only [hcache] at hq
      split_ifs at hq
      · simp only [StateT.run_bind, mem_support_bind_iff] at hq
        obtain ⟨⟨chRes, h₁⟩, _, hq⟩ := hq
        rcases chRes with _ | ⟨σ₁, k₁⟩ <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq;
           subst hq; cases hEq)
        exact hRole'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
        subst hq; cases hEq
    · simp only [hcache] at hq
      by_cases hTc : Tc = Tn
      · simp only [hTc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
        subst hq; cases hEq; exact hRole'
      · simp only [hTc, ↓reduceIte] at hq
        split_ifs at hq
        · simp only [StateT.run_bind, mem_support_bind_iff] at hq
          obtain ⟨⟨chRes, h₁⟩, _, hq⟩ := hq
          rcases chRes with _ | ⟨σ₁, k₁⟩ <;>
            (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq;
             subst hq; cases hEq)
          exact hRole'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
          subst hq; cases hEq
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := rfl

theorem runPRNG_dhSchemeFb_eq [DecidableEq Pt] [Zero Pt]
    {KR RSt K SS RS M E : Type} [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka qep : ℕ) (mo : Mode) (b : Bool)
    (A : SchemeAdversary (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    runPRNG (dhSchemeFb Dh) prng fs lam Δcka qep mo b A =
      runPRNG (dhScheme Dh) prng fs lam Δcka qep mo b A := by
  unfold runPRNG engRun
  have hInit : initPRNG (dhSchemeFb Dh) prng fs lam mo = initPRNG (dhScheme Dh) prng fs lam mo := rfl
  rw [hInit]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · have hAll : AllPartiesInv (M := M) (E := Header Pt × E)
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := b }, h := h } := by
      unfold initPRNG at hmem
      simp only [StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨kc, _, ⟨rtRes, _⟩, _, hmem⟩ := hmem
      rcases rtRes with _ | ⟨σ, k⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        cases hmem.1
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at hmem
        rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
        exact localPartyInv_mkParties Dh kc σ (fs.initSender k) (fs.initReceiver k)
    dsimp only
    exact congrArg (· >>= fun res => pure (some res))
      (simulateQ_implE_localCKA_eq (hooksPRNG_localCKAAgree Dh prng fs mo)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy A _ hAll)

lemma hooksFS_localCKAAgree [DecidableEq Pt] [Zero Pt]
    {KR RSt K SS RS M E : Type} [DecidableEq E] [SampleableType Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ)
      (hooksFS (dhSchemeFb Dh) prng fs Δcka mo j) (hooksFS (dhScheme Dh) prng fs Δcka mo j) where
  startSend_eq ctx P t γ σ r h ht hSend hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hSend' : P.sendsIn ((t - 1) + 1) = true := ht1.symm ▸ hSend
    dsimp only [hooksFS]
    have hCoins : ∀ coins : BitVec 256,
        (do
          let (σ', k, sid) ← rootFS (M := M) prng mo t ((dhSchemeFb Dh).send γ coins).2.2 σ
          let ext ← extOf (M := M) j sid
          modify fun (s : FSState Pt RSt K Pt SS RS E) => { s with cache := Function.update s.cache t (some (((dhSchemeFb Dh).send γ coins).2.1, σ', k, ext)) }
          pure (some (((dhSchemeFb Dh).send γ coins).1, ((dhSchemeFb Dh).send γ coins).2.1, σ', if ext then none else some (fs.initSender k)))).run h =
        (do
          let (σ', k, sid) ← rootFS (M := M) prng mo t ((dhScheme Dh).send γ coins).2.2 σ
          let ext ← extOf (M := M) j sid
          modify fun (s : FSState Pt RSt K Pt SS RS E) => { s with cache := Function.update s.cache t (some (((dhScheme Dh).send γ coins).2.1, σ', k, ext)) }
          pure (some (((dhScheme Dh).send γ coins).1, ((dhScheme Dh).send γ coins).2.1, σ', if ext then none else some (fs.initSender k)))).run h ∧
        ∀ q ∈ support ((do
          let (σ', k, sid) ← rootFS (M := M) prng mo t ((dhScheme Dh).send γ coins).2.2 σ
          let ext ← extOf (M := M) j sid
          modify fun (s : FSState Pt RSt K Pt SS RS E) => { s with cache := Function.update s.cache t (some (((dhScheme Dh).send γ coins).2.1, σ', k, ext)) }
          pure (some (((dhScheme Dh).send γ coins).1, ((dhScheme Dh).send γ coins).2.1, σ', if ext then none else some (fs.initSender k)))).run h),
          ∀ γ' T' σ' ss, q.1 = some (γ', T', σ', ss) → DdhRoleOk P t γ' := by
      intro coins
      have hsnd := dhSchemeFb_send_of_roleOk Dh hRole hSend' coins
      have hRole' : DdhRoleOk P t ((dhScheme Dh).send γ coins).1 := ht1 ▸ hsnd.2
      simp only [hsnd.1]
      refine ⟨trivial, fun q hq γ' T' σ' ss hEq => ?_⟩
      rw [StateT.run_bind, mem_support_bind_iff] at hq
      obtain ⟨⟨⟨σ₁, k₁, sid⟩, h₂⟩, _, hq⟩ := hq
      rw [StateT.run_bind, mem_support_bind_iff] at hq
      obtain ⟨⟨ext, h₃⟩, _, hq⟩ := hq
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hq
      subst hq; cases hEq; exact hRole'
    rcases r with _ | c
    · simp only [StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind]
      refine ⟨bind_congr fun coins => (hCoins coins).1, fun q hq γ' T' σ' ss hEq => ?_⟩
      rw [mem_support_bind_iff] at hq
      obtain ⟨coins, _, hq⟩ := hq
      exact (hCoins coins).2 q hq γ' T' σ' ss hEq
    · simp only [pure_bind]
      exact hCoins c
  startRecv_eq ctx P t γ σ Tn h ht hRecv hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hRecv' : P.sendsIn ((t - 1) + 1) = false := ht1.symm ▸ hRecv
    have hrcv := dhSchemeFb_receive_of_roleOk Dh hRole hRecv' Tn
    have hRole' : DdhRoleOk P t ((dhScheme Dh).receive γ Tn).1 := ht1 ▸ hrcv.2
    dsimp only [hooksFS]
    simp only [hrcv.1]
    refine ⟨trivial, fun q hq γ' σ' rs hEq => ?_⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hq
    rcases hcache : h.cache t with _ | ⟨Tc, σc, kc, ext⟩
    · simp only [hcache] at hq
      split_ifs at hq
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
        subst hq; cases hEq
      · simp only [StateT.run_bind, mem_support_bind_iff] at hq
        obtain ⟨⟨k', h₁⟩, _, ⟨ext', h₂⟩, _, hq⟩ := hq
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
        subst hq; cases hEq; exact hRole'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
        subst hq; cases hEq
    · simp only [hcache] at hq
      by_cases hTc : Tc = Tn
      · simp only [hTc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
        subst hq; cases hEq; exact hRole'
      · simp only [hTc, ↓reduceIte] at hq
        split_ifs at hq
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
          subst hq; cases hEq
        · simp only [StateT.run_bind, mem_support_bind_iff] at hq
          obtain ⟨⟨k', h₁⟩, _, ⟨ext', h₂⟩, _, hq⟩ := hq
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
          subst hq; cases hEq; exact hRole'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
          subst hq; cases hEq
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := rfl

theorem runFS_dhSchemeFb_eq [DecidableEq Pt] [Zero Pt]
    {KR RSt K SS RS M E : Type} [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka qep : ℕ) (mo : Mode)
    (j : ℕ) (b : Bool)
    (A : SchemeAdversary (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    runFS (dhSchemeFb Dh) prng fs lam Δcka qep mo j b A =
      runFS (dhScheme Dh) prng fs lam Δcka qep mo j b A := by
  unfold runFS engRun
  have hInit : initFS (dhSchemeFb Dh) prng fs lam mo j = initFS (dhScheme Dh) prng fs lam mo j := rfl
  rw [hInit]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · have hAll : AllPartiesInv (M := M) (E := Header Pt × E)
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := b }, h := h } := by
      unfold initFS at hmem
      simp only [StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨kr, _, kc, _, ⟨⟨σ, k, sid⟩, _⟩, _, ⟨ext, _⟩, _, hmem⟩ := hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        Option.some.injEq] at hmem
      rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
      exact localPartyInv_mkParties Dh kc σ
        (if ext then none else some (fs.initSender k))
        (if ext then none else some (fs.initReceiver k))
    dsimp only
    exact congrArg (· >>= fun res => pure (some res))
      (simulateQ_implE_localCKA_eq (hooksFS_localCKAAgree Dh prng fs Δcka mo j)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy A _ hAll)

end LocalCKASwap

section InterpretedCKASwap

variable {Pt KR RSt SS RS M E : Type}

abbrev ckaFullImpl [SampleableType Pt]
    (cka : CKAScheme (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (Δ tStar : ℕ) :
    QueryImpl (unifSpec + CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
      (StateT (CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) ProbComp) +
  CKA.oracleImpl cka Δ tStar

def OptPartySync (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) (P : Party)
    (vp : VP (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) : Prop :=
  vp.id = P ∧
  match vp.γ with
  | some γ => DdhRoleOk P vp.tcur γ
  | none => vp.tcur = sc.epoch P

def OptCKASync {HS : Type}
    (es : EState (VP (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) M (Header Pt × E) HS)
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) : Prop :=
  CkaStateInv sc ∧ (es.abort = false → ∀ P : Party, OptPartySync sc P (es.g.st P))

lemma optPartySync_of_epoch_eq {sc sc' : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt}
    {P : Party} {vp : VP (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS}
    (h : OptPartySync sc P vp) (hep : sc'.epoch P = sc.epoch P) : OptPartySync sc' P vp := by
  refine ⟨h.1, ?_⟩
  rcases hγ : vp.γ with _ | γ
  · have h2 := h.2; rw [hγ] at h2; omega
  · have h2 := h.2; rw [hγ] at h2; exact h2

lemma simulateQ_ckaFullImpl_liftProb [SampleableType Pt]
    (cka : CKAScheme (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (Δ tStar : ℕ) {α : Type} (oa : ProbComp α)
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) :
    (simulateQ (ckaFullImpl cka Δ tStar)
      (liftM oa : TComp (CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) α)).run sc =
    (oa >>= fun a => pure (a, sc)) := by
  let S := unifSpec + CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
  induction oa using OracleComp.inductionOn with
  | pure x => simp [StateT.run_pure]
  | query_bind qy mx ih =>
    rw [← (liftComp_eq_liftM (liftM (OracleSpec.query qy) >>= mx) :
        (liftM (OracleSpec.query qy) >>= mx).liftComp S = _),
      liftComp_bind, bind_assoc]
    have hq : (liftM (OracleSpec.query qy) : ProbComp (Fin (qy + 1))).liftComp S =
        liftM (OracleSpec.query (spec := S) (.inl qy)) := rfl
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    have hImpl : ckaFullImpl cka Δ tStar (.inl qy) =
        StateT.lift (liftM (OracleSpec.query qy) : ProbComp (Fin (qy + 1))) := rfl
    rw [hq, simulateQ_query_bind, StateT.run_bind, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, hImpl, StateT.run_lift,
      bind_assoc, pure_bind]
    refine congrArg ((liftM (OracleSpec.query qy) : ProbComp (Fin (qy + 1))) >>= ·)
      (funext fun u => ?_)
    rw [liftComp_eq_liftM]
    exact ih u

lemma simulateQ_ckaFullImpl_liftC_query [SampleableType Pt]
    (cka : CKAScheme (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (Δ tStar : ℕ) (q_s : (CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt).Domain)
    (h : CKAState Pt Pt) (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) :
    (simulateQ (ckaFullImpl cka Δ tStar)
      ((liftC (query (spec := unifSpec + CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) (.inr q_s) :
        CKA.AdversaryComp (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt _)).run h)).run sc =
    ((CKA.oracleImpl cka Δ tStar q_s).run sc >>= fun w => pure ((w.1, h), w.2)) := by
  simp only [liftC, StateT.run_lift, simulateQ_bind, simulateQ_HasQuery_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, ckaFullImpl, QueryImpl.add_apply_inr]
  congr 1

lemma liftC_corrQuery_support [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ) (P : Party) (h : CKAState Pt Pt)
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) (hsc : CkaStateInv sc)
    {z : (Option (CKA.DDH.State (BitVec 256) Pt) × CKAState Pt Pt) ×
      CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt}
    (hz : z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δ tStar)
      ((liftC (CKA.corrQuery P)).run h)).run sc)) :
    z.2 = sc ∧ ∀ γ, z.1.1 = some γ → DdhRoleOk P (sc.epoch P) γ := by
  unfold CKA.corrQuery at hz
  rw [simulateQ_ckaFullImpl_liftC_query] at hz
  dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inr] at hz
  unfold CKA.corrImpl at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz <;> simp only [StateT.run_pure, pure_bind, support_pure,
    Set.mem_singleton_iff] at hz <;> subst hz
  · exact ⟨rfl, fun γ hEq => by cases hEq; exact hsc.1 P⟩
  · exact ⟨rfl, fun _ hEq => by cases hEq⟩

lemma liftC_receiveQuery_support [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ) (P : Party) (h : CKAState Pt Pt)
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) (hsc : CkaStateInv sc)
    {z : (Option Unit × CKAState Pt Pt) × CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt}
    (hz : z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δ tStar)
      ((liftC (CKA.receiveQuery P)).run h)).run sc)) :
    CkaStateInv z.2 ∧
    (z.1.1 = none → z.2 = sc) ∧
    (z.1.1 = some () → z.2.epoch P = sc.epoch P + 1 ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q) := by
  have hInvAll := (ckaOracleImpl_dhSchemeFb_eq Dh Δ tStar (.inl (.inr P)) sc hsc).2
  unfold CKA.receiveQuery at hz
  rw [simulateQ_ckaFullImpl_liftC_query, mem_support_bind_iff] at hz
  obtain ⟨⟨ans, sc'⟩, hmem, hz⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hsc' := hInvAll (ans, sc') hmem
  dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold CKA.receiveImpl at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hsc, fun _ => rfl, fun h => by cases h⟩
  · rcases hlm : sc.lastMsg with _ | T
    · simp only [hlm, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hsc, fun _ => rfl, fun h => by cases h⟩
    · simp only [hlm, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      dsimp only
      refine ⟨hsc', (fun h => by cases h), fun _ => ⟨by simp [CKA.GameState.afterReceive],
        fun Q hQP => by simp [CKA.GameState.afterReceive, hQP]⟩⟩

lemma liftC_sendFamily_support [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar tH t : ℕ) (P : Party) (r : Option (BitVec 256))
    (h : CKAState Pt Pt)
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) (hsc : CkaStateInv sc)
    {z : (Option (Pt × Pt) × CKAState Pt Pt) × CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt}
    (hz : z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δ tStar)
      ((match r with
        | some c => liftC (CKA.sendWithAdversaryCoinsQuery P c)
        | none => if t = tH then liftC (CKA.challQuery P) else liftC (CKA.sendQuery P)).run h)).run sc)) :
    CkaStateInv z.2 ∧
    (∀ T' Ik, z.1.1 = some (T', Ik) →
      z.2.epoch P = sc.epoch P + 1 ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q) := by
  rcases r with _ | c
  · by_cases ht : t = tH
    · simp only [ht, ↓reduceIte] at hz
      unfold CKA.challQuery at hz
      rw [simulateQ_ckaFullImpl_liftC_query, mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
      have hInvW := (ckaOracleImpl_dhSchemeFb_eq Dh Δ tStar (.inl (.inl (.inr P))) sc hsc).2 w hw
      refine ⟨hInvW, fun T' Ik hw1 => ?_⟩
      dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hw
      unfold CKA.challImpl at hw
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
      split_ifs at hw
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
        subst hw; cases hw1
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hw
        obtain ⟨_, _, _, _, hw⟩ := hw; subst hw
        exact ⟨by simp [CKA.GameState.afterSend], fun Q hQP => by simp [CKA.GameState.afterSend, hQP]⟩
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hw
        obtain ⟨_, _, hw⟩ := hw; subst hw
        exact ⟨by simp [CKA.GameState.afterSend], fun Q hQP => by simp [CKA.GameState.afterSend, hQP]⟩
    · simp only [ht, ↓reduceIte] at hz
      unfold CKA.sendQuery at hz
      rw [simulateQ_ckaFullImpl_liftC_query, mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
      have hInvW := (ckaOracleImpl_dhSchemeFb_eq Dh Δ tStar (.inl (.inl (.inl (.inl P)))) sc hsc).2 w hw
      refine ⟨hInvW, fun T' Ik hw1 => ?_⟩
      dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inl] at hw
      unfold CKA.sendImpl at hw
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
      split_ifs at hw
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
        subst hw; cases hw1
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hw
        obtain ⟨_, _, hw⟩ := hw; subst hw
        exact ⟨by simp [CKA.GameState.afterSend], fun Q hQP => by simp [CKA.GameState.afterSend, hQP]⟩
  · unfold CKA.sendWithAdversaryCoinsQuery at hz
    rw [simulateQ_ckaFullImpl_liftC_query, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    have hInvW := (ckaOracleImpl_dhSchemeFb_eq Dh Δ tStar (.inl (.inl (.inl (.inr (P, c))))) sc hsc).2 w hw
    refine ⟨hInvW, fun T' Ik hw1 => ?_⟩
    dsimp only [CKA.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hw
    unfold CKA.sendWithAdversaryCoinsImpl at hw
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw
    split_ifs at hw
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      subst hw; cases hw1
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨by simp [CKA.GameState.afterSend], fun Q hQP => by simp [CKA.GameState.afterSend, hQP]⟩

lemma vSend_ckaSync_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {K : Type} [SampleableType K] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar : ℕ) (mo : Mode)
    (ctx : Ctx (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS M E) (P : Party)
    (s : VP (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) (m : M)
    (pair : Option (M × M)) (r : Option (BitVec 256)) (h : CKAState Pt Pt)
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt)
    (hsc : CkaStateInv sc) (hs : OptPartySync sc P s) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((vSend (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) ctx P s m pair r).run h)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((vSend (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s m pair r).run h)).run sc ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((vSend (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s m pair r).run h)).run sc),
      CkaStateInv z.2 ∧
      (∀ st' ct, z.1.1 = some (st', ct) →
        OptPartySync z.2 P st' ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q) := by
  have hStep1 :
      (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
        ((vSendStep1 (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) ctx P s r).run h)).run sc =
      (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
        ((vSendStep1 (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s r).run h)).run sc ∧
      ∀ w ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
        ((vSendStep1 (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s r).run h)).run sc),
        CkaStateInv w.2 ∧
        (∀ s₁, w.1.1 = some s₁ →
          OptPartySync w.2 P s₁ ∧ ∀ Q, Q ≠ P → w.2.epoch Q = sc.epoch Q) := by
    unfold vSendStep1
    by_cases hSend : s.id.sendsIn (s.tcur + 1) = true
    · have hPSend : P.sendsIn (s.tcur + 1) = true := hs.1 ▸ hSend
      simp only [hSend, ↓reduceIte]
      rcases hγ : s.γ with _ | γ
      · let K : Option (Pt × Pt) → StateT (CKAState Pt Pt)
            (TComp (CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)) _ :=
          fun ans => match ans with
            | none => pure none
            | some (T', Ik) => do
              cacheC (s.tcur + 1) (T', Ik)
              let p := prng.up s.root Ik
              if mo.tH + Δcka ≤ s.tcur + 1 then
                match ← liftC (CKA.corrQuery P) with
                | none => pure none
                | some γ => pure (some (some γ, T', p.1, fs.initSender p.2))
              else pure (some (none, T', p.1, fs.initSender p.2))
        have hPull : (hooksCKA (dhScheme Dh) prng fs Δcka mo).startSend ctx P (s.tcur + 1) none s.root r =
            ((match r with
              | some c => liftC (CKA.sendWithAdversaryCoinsQuery P c)
              | none => if s.tcur + 1 = mo.tH then liftC (CKA.challQuery P) else liftC (CKA.sendQuery P)) >>= K) := by
          ext h₀
          dsimp only [hooksCKA, K]
          rcases r with _ | c <;> split_ifs <;> simp only [StateT.run_bind] <;>
            congr 1 <;> ext ⟨a, s'⟩ <;> rcases a with _ | ⟨T', Ik⟩
          all_goals first
            | (simp only [StateT.run_pure]; done)
            | (simp only [cacheC, StateT.run_bind, StateT.run_modify, pure_bind]; done)
            | (simp only [cacheC, StateT.run_bind, StateT.run_modify, pure_bind]
               congr 1; ext ⟨corrAns, s''⟩; rcases corrAns with _ | γ <;>
                 simp only [StateT.run_pure])
        have hEqStart : (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo).startSend ctx P (s.tcur + 1) none s.root r =
            (hooksCKA (dhScheme Dh) prng fs Δcka mo).startSend ctx P (s.tcur + 1) none s.root r := rfl
        rw [hEqStart]
        refine ⟨rfl, fun w hw => ?_⟩
        rw [hPull, bind_assoc] at hw
        rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hw
        obtain ⟨⟨⟨ans, h₁⟩, sc₁⟩, hans, hw⟩ := hw
        have ⟨hsc₁, hep₁⟩ := liftC_sendFamily_support Dh Δcka tStar mo.tH (s.tcur + 1) P r h sc hsc hans
        have hstcur : s.tcur = sc.epoch P := by have h2 := hs.2; rw [hγ] at h2; exact h2
        rcases ans with _ | ⟨T', Ik⟩
        · dsimp only [K] at hw
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw
          subst hw; exact ⟨hsc₁, fun _ hEq => nomatch hEq⟩
        · have ⟨hepP, hepQ⟩ := hep₁ T' Ik rfl
          dsimp only at hsc₁ hepP hepQ
          dsimp only [K] at hw
          simp only [cacheC, bind_assoc, StateT.run_bind, StateT.run_modify, pure_bind] at hw
          by_cases hfin : mo.tH + Δcka ≤ s.tcur + 1
          · simp only [hfin, ↓reduceIte] at hw
            rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind,
              mem_support_bind_iff] at hw
            obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hw⟩ := hw
            have ⟨hsc₂_eq, hRole₂⟩ := liftC_corrQuery_support Dh Δcka tStar P _ sc₁ hsc₁ hcorr
            dsimp only at hsc₂_eq hRole₂
            subst hsc₂_eq
            rcases corrAns with _ | γ'
            · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw
              subst hw; exact ⟨hsc₁, fun _ hEq => nomatch hEq⟩
            · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw
              subst hw
              refine ⟨hsc₁, fun s₁ hs₁ => ?_⟩
              dsimp at hs₁; cases hs₁
              have hR : DdhRoleOk P (s.tcur + 1) γ' := by
                rw [hstcur, ← hepP]; exact hRole₂ γ' rfl
              exact ⟨⟨hs.1, hR⟩, hepQ⟩
          · simp only [hfin, ↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw
            subst hw
            refine ⟨hsc₁, fun s₁ hs₁ => ?_⟩
            dsimp at hs₁; cases hs₁
            exact ⟨⟨hs.1, by dsimp; omega⟩, hepQ⟩
      · dsimp only [hooksCKA]
        have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
        have hCoinsEq : ∀ coins : BitVec 256,
            (dhSchemeFb Dh).send γ coins = (dhScheme Dh).send γ coins ∧
              DdhRoleOk P (s.tcur + 1) ((dhScheme Dh).send γ coins).1 :=
          fun coins => dhSchemeFb_send_of_roleOk Dh hRole hPSend coins
        rcases r with _ | c
        · simp only [StateT.run_bind, StateT.run_lift,
            cacheC, StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind,
            simulateQ_pure]
          refine ⟨bind_congr fun p => by rw [(hCoinsEq p.1).1], fun w hw => ?_⟩
          rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hw
          simp only [bind_assoc, pure_bind, mem_support_bind_iff,
            support_pure, Set.mem_singleton_iff] at hw
          obtain ⟨coins, _, hw⟩ := hw
          subst hw
          refine ⟨hsc, fun s₁ hs₁ => ?_⟩
          dsimp at hs₁; cases hs₁
          exact ⟨⟨hs.1, (hCoinsEq coins).2⟩, fun _ _ => rfl⟩
        · simp only [pure_bind, (hCoinsEq c).1, cacheC, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          refine ⟨trivial, fun w hw => ?_⟩
          subst hw
          refine ⟨hsc, fun s₁ hs₁ => ?_⟩
          dsimp at hs₁; cases hs₁
          exact ⟨⟨hs.1, (hCoinsEq c).2⟩, fun _ _ => rfl⟩
    · simp only [hSend, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff]
      refine ⟨trivial, fun w hw => ?_⟩
      subst hw
      exact ⟨hsc, fun s₁ hs₁ => by dsimp at hs₁; cases hs₁; exact ⟨hs, fun _ _ => rfl⟩⟩
  rw [vSend_eq_bind, vSend_eq_bind, StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind,
    StateT.run_bind, StateT.run_bind, hStep1.1]
  have hFsEq : (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo).fsSend =
      (hooksCKA (dhScheme Dh) prng fs Δcka mo).fsSend := rfl
  rw [hFsEq]
  refine ⟨rfl, fun z hz => ?_⟩
  rw [mem_support_bind_iff] at hz
  obtain ⟨⟨⟨s₁?, h₁⟩, sc₁⟩, hw, hz⟩ := hz
  have ⟨hsc₁, hs₁Sync⟩ := hStep1.2 _ hw
  rcases s₁? with _ | s₁
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨hsc₁, fun _ _ hEq => by cases hEq⟩
  · have ⟨hs₁P, hepQ⟩ := hs₁Sync s₁ rfl
    rcases hvS : s₁.vS with _ | v
    · simp only [hvS, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨hsc₁, fun _ _ hEq => by cases hEq; exact ⟨hs₁P, hepQ⟩⟩
    · simp only [hvS, hooksCKA, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hsc₁, fun st' ct hEq => by cases hEq; exact ⟨hs₁P, hepQ⟩⟩

lemma vRecv_hooksCKA_pure_eq [DecidableEq Pt] [Zero Pt]
    {K : Type}
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka : ℕ) (mo : Mode)
    (ctx : Ctx (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS M E) (P : Party)
    (s : VP (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) (c : Header Pt × E)
    (rec_ : Option (Record M (Header Pt × E))) (h : CKAState Pt Pt)
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt) (hs : OptPartySync sc P s) :
    (vRecv (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) ctx P s c rec_).run h =
      (vRecv (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s c rec_).run h ∧
    ∃ out,
      (vRecv (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s c rec_).run h = pure out ∧
      ∀ st' t' i' m', out.1 = some (some (st', t', i', m')) →
        st'.id = P ∧
        (((s.tcur < st'.tcur && s.γ.isNone) = false ∧ OptPartySync sc P st') ∨
         ((s.tcur < st'.tcur && s.γ.isNone) = true ∧ st'.γ = none ∧ st'.tcur = sc.epoch P + 1)) := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [href, ↓reduceIte, StateT.run_pure]
    exact ⟨trivial, _, rfl, fun _ _ _ _ hEq => by cases hEq⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hNotSend : s.id.sendsIn c.1.1 = false :=
      (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr href)).1
    have hStep1 :
        ∃ out1,
          (vRecvStep1 (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) ctx P s c).run h = pure out1 ∧
          (vRecvStep1 (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s c).run h = pure out1 ∧
          ∀ s₁, out1.1 = some (some s₁) →
            s₁.id = P ∧
            (((s.tcur < s₁.tcur && s.γ.isNone) = false ∧ OptPartySync sc P s₁) ∨
             ((s.tcur < s₁.tcur && s.γ.isNone) = true ∧ s₁.γ = none ∧ s₁.tcur = sc.epoch P + 1)) := by
      unfold vRecvStep1
      by_cases ht : c.1.1 = s.tcur + 1
      · simp only [ht, ↓reduceIte]
        rcases hTn : c.1.2 with _ | Tn
        · exact ⟨_, StateT.run_pure _ _, StateT.run_pure _ _, fun _ hEq => by cases hEq⟩
        · have hPRecv : P.sendsIn (s.tcur + 1) = false := by
            rw [← hs.1, ← ht]; exact hNotSend
          dsimp only [hooksCKA]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          have hMapEq :
              (s.γ.map fun γ => ((dhSchemeFb Dh).receive γ Tn).1) =
                (s.γ.map fun γ => ((dhScheme Dh).receive γ Tn).1) := by
            rcases hγ : s.γ with _ | γ
            · rfl
            · have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
              exact congrArg (fun p => some p.1) (dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn).1
          rcases hcache : h.cache (s.tcur + 1) with _ | ⟨Tc, Ik⟩
          · by_cases hauth : (mo.auth && decide (s.tcur + 1 = mo.tStar)) = true
            · simp only [hauth, ↓reduceIte]
              rcases hγ : s.γ with _ | γ
              · simp only [StateT.run_pure, pure_bind]
                exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
              · have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
                have ⟨hEq, hRole'⟩ := dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn
                simp only [hEq, StateT.run_pure, pure_bind]
                exact ⟨_, rfl, rfl, fun s₁ hs₁ => by
                  dsimp at hs₁; cases hs₁
                  exact ⟨hs.1, Or.inl ⟨by simp, ⟨hs.1, hRole'⟩⟩⟩⟩
            · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
              exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
          · by_cases hTc : Tc = Tn
            · simp only [hTc, ↓reduceIte, hMapEq, StateT.run_pure, pure_bind]
              refine ⟨_, rfl, rfl, fun s₁ hs₁ => ?_⟩
              dsimp at hs₁; cases hs₁
              rcases hγ : s.γ with _ | γ
              · refine ⟨hs.1, Or.inr ⟨by simp, rfl, ?_⟩⟩
                have h2 := hs.2; rw [hγ] at h2; dsimp; omega
              · have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
                have ⟨_, hRole'⟩ := dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn
                exact ⟨hs.1, Or.inl ⟨by simp, ⟨hs.1, hRole'⟩⟩⟩
            · simp only [hTc, ↓reduceIte]
              by_cases hauth : (mo.auth && decide (s.tcur + 1 = mo.tStar)) = true
              · simp only [hauth, ↓reduceIte]
                rcases hγ : s.γ with _ | γ
                · simp only [StateT.run_pure, pure_bind]
                  exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
                · have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
                  have ⟨hEq, hRole'⟩ := dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn
                  simp only [hEq, StateT.run_pure, pure_bind]
                  exact ⟨_, rfl, rfl, fun s₁ hs₁ => by
                    dsimp at hs₁; cases hs₁
                    exact ⟨hs.1, Or.inl ⟨by simp, ⟨hs.1, hRole'⟩⟩⟩⟩
              · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
                exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
      · simp only [ht, ↓reduceIte, StateT.run_pure]
        exact ⟨_, rfl, rfl, fun s₁ hs₁ => by
          dsimp at hs₁; cases hs₁; exact ⟨hs.1, Or.inl ⟨by simp, hs⟩⟩⟩
    obtain ⟨⟨s₁?, h₁⟩, hPureFb, hPureDh, hPost1⟩ := hStep1
    rw [hPureFb, hPureDh, pure_bind, pure_bind]
    rcases s₁? with _ | (_ | s₁)
    · exact ⟨rfl, _, StateT.run_pure _ _, fun _ _ _ _ hEq => nomatch hEq⟩
    · exact ⟨rfl, _, StateT.run_pure _ _, fun _ _ _ _ hEq => nomatch hEq⟩
    · dsimp only
      rcases hvR : s₁.vR c.1.1 with _ | v
      · rw [StateT.run_pure]
        exact ⟨rfl, _, rfl, fun _ _ _ _ hEq => nomatch hEq⟩
      · dsimp only [hooksCKA]
        rw [pure_bind]
        rcases hrc : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
        · exact ⟨rfl, _, StateT.run_pure _ _, fun _ _ _ _ hEq => nomatch hEq⟩
        · exact ⟨rfl, _, StateT.run_pure _ _, fun st' _ _ _ hEq => by
            dsimp at hEq; cases hEq; exact hPost1 s₁ rfl⟩

lemma commitE_ckaSync [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type}
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar : ℕ) (mo : Mode)
    (s : Ctx (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS M E) (P : Party)
    (old new : VP (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) (pos : SM.Pos)
    (es : EState (VP (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) M (Header Pt × E)
      (CKAState Pt Pt))
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt)
    (hsc : CkaStateInv sc)
    (hS : ∀ Q, OptPartySync sc Q (s.st Q))
    (_hEs : es.abort = false → ∀ Q, OptPartySync sc Q (es.g.st Q))
    (hNew : new.id = P ∧
      (((old.tcur < new.tcur && old.γ.isNone) = false ∧ OptPartySync sc P new) ∨
       ((old.tcur < new.tcur && old.γ.isNone) = true ∧ new.γ = none ∧ new.tcur = sc.epoch P + 1))) :
    (commitE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) s P old new pos).run es =
      (commitE (hooksCKA (dhScheme Dh) prng fs Δcka mo) s P old new pos).run es ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((commitE (hooksCKA (dhScheme Dh) prng fs Δcka mo) s P old new pos).run es)).run sc),
      CkaStateInv z.2 ∧
      (z.1.1 = none → OptCKASync z.1.2 z.2) ∧
      (∀ s₁, z.1.1 = some s₁ → z.1.2.abort = es.abort ∧
        ∀ Q, OptPartySync z.2 Q (s₁.st Q)) := by
  refine ⟨rfl, fun z hz => ?_⟩
  unfold commitE abortE at hz
  dsimp only [hooksCKA] at hz
  rw [run_liftH_bind] at hz
  rcases hNew.2 with ⟨hCond, hSyncNew⟩ | ⟨hCond, hγNone, htcurNew⟩
  · rw [hCond] at hz
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only
    refine ⟨hsc, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
    cases hs₁
    by_cases hQP : Q = P
    · subst hQP; simp [hSyncNew]
    · simp [Function.update_of_ne hQP, accept_st_eq, hS Q]
  · rw [hCond] at hz
    simp only [↓reduceIte] at hz
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨⟨rcvAns, h₁⟩, sc₁⟩, hrcv, hz⟩ := hz
    have ⟨hsc₁, _, hRcvOk⟩ := liftC_receiveQuery_support Dh Δcka tStar P es.h sc hsc hrcv
    rcases rcvAns with _ | ⟨⟩
    · simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      dsimp only
      exact ⟨hsc₁, fun _ => ⟨hsc₁, fun hab => by cases hab⟩, fun _ hEq => by cases hEq⟩
    · have ⟨hepP, hepQ⟩ := hRcvOk rfl
      dsimp only at hsc₁ hepP hepQ
      by_cases hfin : mo.tH + Δcka ≤ new.tcur
      · simp only [hfin, ↓reduceIte] at hz
        rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hz⟩ := hz
        have ⟨hsc₂_eq, hRole₂⟩ := liftC_corrQuery_support Dh Δcka tStar P h₁ sc₁ hsc₁ hcorr
        dsimp only at hsc₂_eq hRole₂
        subst hsc₂_eq
        rcases corrAns with _ | γ'
        · simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          dsimp only
          exact ⟨hsc₁, fun _ => ⟨hsc₁, fun hab => by cases hab⟩, fun _ hEq => by cases hEq⟩
        · simp only [StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          dsimp only
          refine ⟨hsc₁, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
          cases hs₁
          by_cases hQP : Q = P
          · subst hQP
            have hR : DdhRoleOk Q new.tcur γ' := by rw [htcurNew, ← hepP]; exact hRole₂ γ' rfl
            simp only [Function.update_self, accept_st_eq]
            exact ⟨hNew.1, hR⟩
          · simp [Function.update_of_ne hQP, accept_st_eq]
            exact optPartySync_of_epoch_eq (hS Q) (hepQ Q hQP)
      · simp only [hfin, ↓reduceIte, StateT.run_pure, pure_bind, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        dsimp only
        refine ⟨hsc₁, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
        cases hs₁
        by_cases hQP : Q = P
        · subst hQP
          simp only [Function.update_self, accept_st_eq]
          refine ⟨hNew.1, ?_⟩
          rw [hγNone, htcurNew, hepP]
        · simp [Function.update_of_ne hQP, accept_st_eq]
          exact optPartySync_of_epoch_eq (hS Q) (hepQ Q hQP)

lemma implE_ckaSync_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar qep maxSkip : ℕ) (mo : Mode)
    (es : EState (VP (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) M (Header Pt × E)
      (CKAState Pt Pt))
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt)
    (t : (SM.spec (PartyState (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E)).Domain)
    (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((implE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
        (.inr t)).run es)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((implE (hooksCKA (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
        (.inr t)).run es)).run sc ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((implE (hooksCKA (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
        (.inr t)).run es)).run sc), OptCKASync z.1.2 z.2 := by
  let hk₁ := hooksCKA (dhSchemeFb Dh) prng fs Δcka mo
  let hk₂ := hooksCKA (dhScheme Dh) prng fs Δcka mo
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inl (.inl (P, m, r)))))) =
        transmitE hk₁ (2 + Δcka) qep mo.policy (P, m, r) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inl (.inl (P, m, r)))))) =
        transmitE hk₂ (2 + Δcka) qep mo.policy (P, m, r) := rfl
    rw [hI₁, hI₂]; unfold transmitE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => by cases h'⟩⟩
        · have hs₁All : ∀ Q, OptPartySync sc Q (s₁.st Q) := fun Q => by
            rw [Engine.epMgmt_st_eq hep]; exact hSync.2 habF Q
          have hvs := vSend_ckaSync_eq Dh prng fs Δcka tStar mo s₁ P (s₁.st P) m none r es.h sc
            hSync.1 (hs₁All P)
          simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
          rw [run_liftH_bind, run_liftH_bind]
          simp only [simulateQ_bind, StateT.run_bind]
          rw [hvs.1]
          refine ⟨rfl, fun z hz => ?_⟩
          rw [mem_support_bind_iff] at hz
          obtain ⟨⟨⟨vsRes, h'⟩, sc₁⟩, hvsMem, hz⟩ := hz
          have ⟨hsc₁, hvsPost⟩ := hvs.2 _ hvsMem
          rcases vsRes with _ | ⟨st', ct⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨hsc₁, fun h' => nomatch h'⟩
          · obtain ⟨hst'P, hepQ⟩ := hvsPost st' ct rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            refine ⟨hsc₁, fun _ Q => ?_⟩
            by_cases hQP : Q = P
            · subst hQP; simp [record_st_eq, hst'P]
            · simp [record_st_eq, Function.update_of_ne hQP]
              exact optPartySync_of_epoch_eq (hs₁All Q) (hepQ Q hQP)
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) =
        challE hk₁ (2 + Δcka) qep mo.cfg mo.policy (P, m₀, m₁, r) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) =
        challE hk₂ (2 + Δcka) qep mo.cfg mo.policy (P, m₀, m₁, r) := rfl
    rw [hI₁, hI₂]; unfold challE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !((mo.cfg (M := M)).challAllowedIn (s₁.epoch P))) = true
        · simp only [hch, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
          · have hs₁All : ∀ Q, OptPartySync sc Q (s₁.st Q) := fun Q => by
              rw [Engine.epMgmt_st_eq hep]; exact hSync.2 habF Q
            have hvs := vSend_ckaSync_eq Dh prng fs Δcka tStar mo s₁ P (s₁.st P)
              (((mo.cfg (M := M)).challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀))
              (some (m₀, m₁)) r es.h sc hSync.1 (hs₁All P)
            simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
            rw [run_liftH_bind, run_liftH_bind]
            simp only [simulateQ_bind, StateT.run_bind]
            rw [hvs.1]
            refine ⟨rfl, fun z hz => ?_⟩
            rw [mem_support_bind_iff] at hz
            obtain ⟨⟨⟨vsRes, h'⟩, sc₁⟩, hvsMem, hz⟩ := hz
            have ⟨hsc₁, hvsPost⟩ := hvs.2 _ hvsMem
            rcases vsRes with _ | ⟨st', ct⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨hsc₁, fun h' => nomatch h'⟩
            · obtain ⟨hst'P, hepQ⟩ := hvsPost st' ct rfl
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz
              refine ⟨hsc₁, fun _ Q => ?_⟩
              by_cases hQP : Q = P
              · subst hQP; simp [record_st_eq, hst'P]
              · simp [record_st_eq, Function.update_of_ne hQP]
                exact optPartySync_of_epoch_eq (hs₁All Q) (hepQ Q hQP)
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inr (P, c))))) =
        deliverE hk₁ maxSkip mo.cfg (P, c) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inr (P, c))))) =
        deliverE hk₂ maxSkip mo.cfg (P, c) := rfl
    rw [hI₁, hI₂]; unfold deliverE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
          vRecv_hooksCKA_pure_eq Dh prng fs Δcka mo es.g P (es.g.st P) c (some r) es.h sc
            (hSync.2 habF P)
        rw [run_liftH_bind, run_liftH_bind]
        dsimp only [hk₁, hk₂]
        simp only [hvrEq, hvrPure, pure_bind]
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
        · split_ifs <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               simulateQ_pure, support_pure, Set.mem_singleton_iff];
             exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
        · have hcm := commitE_ckaSync Dh prng fs Δcka tStar mo es.g P (es.g.st P) st' r.pos
            { es with h := h' } sc hSync.1 (hSync.2 habF) hSync.2 (hvrPost st' t' i' m' rfl)
          simp only [StateT.run_bind, simulateQ_bind]
          rw [hcm.1]
          refine ⟨rfl, fun z hz => ?_⟩
          rw [mem_support_bind_iff] at hz
          obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
          obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hcmNone rfl
          · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            refine ⟨hsc₁, fun _ Q => ?_⟩
            split_ifs <;> exact hs₁Sync Q
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inr (P, c)))) =
        injectE hk₁ (2 + Δcka) qep mo.cfg (P, c) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inr (P, c)))) =
        injectE hk₂ (2 + Δcka) qep mo.cfg (P, c) := rfl
    rw [hI₁, hI₂]; unfold injectE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := by
        rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr href) with ⟨h1, _⟩
        rcases Bool.or_eq_false_iff.mp h1 with ⟨h2, _⟩
        exact (Bool.or_eq_false_iff.mp h2).1
      obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
        vRecv_hooksCKA_pure_eq Dh prng fs Δcka mo es.g P (es.g.st P) c none es.h sc
          (hSync.2 habF P)
      simp only [href, Bool.false_eq_true, ↓reduceIte]
      rw [run_liftH_bind, run_liftH_bind]
      dsimp only [hk₁, hk₂]
      simp only [hvrEq, hvrPure, pure_bind]
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · simp only [hqep, ↓reduceIte]
          by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
          · have hcm := commitE_ckaSync Dh prng fs Δcka tStar mo es.g P (es.g.st P) st'
              ⟨P.other, t', i'⟩ { es with h := h' } sc hSync.1 (hSync.2 habF) hSync.2
              (hvrPost st' t' i' m' rfl)
            simp only [htriv, ↓reduceIte, StateT.run_bind, simulateQ_bind]
            rw [hcm.1]
            refine ⟨rfl, fun z hz => ?_⟩
            rw [mem_support_bind_iff] at hz
            obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
            obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem
            rcases cmRes with _ | s₁
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hcmNone rfl
            · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨hsc₁, fun _ => hs₁Sync⟩
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
            split_ifs <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 simulateQ_pure, support_pure, Set.mem_singleton_iff];
               exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inr P)) =
        corrE hk₁ mo.policy P := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inr P)) =
        corrE hk₂ mo.policy P := rfl
    rw [hI₁, hI₂]
    have hRevEq : hk₁.reveal = hk₂.reveal := rfl
    unfold corrE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hRevEq]
    refine ⟨trivial, fun z hz => ?_⟩
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P)) = true
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hSync
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hdoom : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P) = true
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨hSync.1, fun h' => nomatch h'⟩
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hz
        rw [run_liftH_bind] at hz
        simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨revRes, h'⟩, sc₁⟩, hrev, hz⟩ := hz
        have hsc₁_eq : sc₁ = sc := by
          dsimp only [hk₂, hooksCKA] at hrev
          rcases hγ : (es.g.st P).γ with _ | γ
          · simp only [hγ, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hrev
            obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hrev⟩ := hrev
            have ⟨heq, _⟩ := liftC_corrQuery_support Dh Δcka tStar P es.h sc hSync.1 hcorr
            subst heq
            rcases corrAns with _ | γ' <;>
              (simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hrev;
               exact (Prod.mk.inj hrev).2)
          · simp only [hγ, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hrev
            exact (Prod.mk.inj hrev).2
        subst hsc₁_eq
        rcases revRes with _ | stP
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨hSync.1, fun h' => nomatch h'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hSync

lemma simulateQ_implE_ckaSync_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K α : Type} [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar qep maxSkip : ℕ) (mo : Mode)
    (oa : OracleComp (unifSpec + SM.spec (PartyState (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E)) α)
    (es : EState (VP (Option (CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) M (Header Pt × E)
      (CKAState Pt Pt))
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt)
    (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((simulateQ (implE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip
        mo.cfg mo.policy) oa).run es)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((simulateQ (implE (hooksCKA (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip
        mo.cfg mo.policy) oa).run es)).run sc := by
  induction oa using OracleComp.inductionOn generalizing es sc with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · have hInl₁ :
          (implE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
            (.inl n)).run es = (coinsE n).run es := rfl
      have hInl₂ :
          (implE (hooksCKA (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
            (.inl n)).run es = (coinsE n).run es := rfl
      rw [hInl₁, hInl₂]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, simulateQ_bind, simulateQ_HasQuery_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure] at hmem
      have hInlQ : ckaFullImpl (dhScheme Dh) Δcka tStar (Sum.inl n) =
          StateT.lift ($ᵗ (Fin (n + 1)) : ProbComp (Fin (n + 1))) := rfl
      rw [hInlQ, StateT.run_lift] at hmem
      simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨_, _, hEq⟩ := hmem
      rcases Prod.mk.inj hEq with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨rfl, hesEq⟩
      dsimp only [id]
      rw [hesEq, hscEq]
      exact ih u es sc hSync
    · obtain ⟨hEq, hPost⟩ := implE_ckaSync_eq Dh prng fs Δcka tStar qep maxSkip mo es sc t_sm hSync
      rw [hEq]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem =>
        ih _ es' sc' (hPost _ hmem)

theorem simulateQ_runCKA_dhSchemeFb_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType KR] [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka tStar qep : ℕ) (mo : Mode)
    (b : Bool)
    (A : SchemeAdversary (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E)
    (sc : CKA.GameState (CKA.DDH.State (BitVec 256) Pt) Pt)
    (hsc : CkaStateInv sc) (hep₀ : ∀ P, sc.epoch P = 0) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      (runCKA (dhSchemeFb Dh) prng fs lam Δcka qep mo b A)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      (runCKA (dhScheme Dh) prng fs lam Δcka qep mo b A)).run sc := by
  unfold runCKA engRun
  have hInit : initCKA (dhSchemeFb Dh) prng fs lam mo = initCKA (dhScheme Dh) prng fs lam mo := rfl
  rw [hInit, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨vs, h⟩, sc₁⟩ hmem => ?_
  have hSyncInit : sc₁ = sc ∧ ∀ vA vB, vs = some (vA, vB) →
      OptCKASync (M := M) (E := Header Pt × E)
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := b }, h := h } sc := by
    unfold initCKA at hmem
    simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, bind_assoc, pure_bind] at hmem
    rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hmem
    simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hmem
    obtain ⟨kr, _, hmem⟩ := hmem
    rcases htL : mo.tL with _ | tLv
    · simp only [htL, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind] at hmem
      rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hmem
      simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨kc, _, hmem⟩ := hmem
      rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
      refine ⟨hscEq, fun vA vB hEq => ?_⟩
      rw [hvs, Option.some.injEq] at hEq; cases hEq
      refine ⟨hsc, fun _ P => ?_⟩
      cases P
      · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
      · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩
    · simp only [htL, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
      refine ⟨hscEq, fun vA vB hEq => ?_⟩
      rw [hvs, Option.some.injEq] at hEq; cases hEq
      refine ⟨hsc, fun _ P => ?_⟩
      cases P <;> exact ⟨rfl, (hep₀ _).symm⟩
  obtain ⟨hscEq, hSyncInit⟩ := hSyncInit
  rw [hscEq]
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · dsimp only
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    rw [simulateQ_implE_ckaSync_eq Dh prng fs Δcka tStar qep fs.maxSkip mo A _ sc
      (hSyncInit vA vB rfl)]

theorem ckaBranch_redCKAAuth_dhSchemeFb_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType KR] [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka tStar qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (b : Bool)
    (A : SchemeAdversary (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    CKA.branch (dhSchemeFb Dh) Δcka tStar b
      (redCKAAuth (dhSchemeFb Dh) prng fs lam Δcka qep tL t A) =
    CKA.branch (dhScheme Dh) Δcka tStar b
      (redCKAAuth (dhScheme Dh) prng fs lam Δcka qep tL t A) := by
  rw [ckaBranch_dhSchemeFb_eq]
  unfold CKA.branch redCKAAuth
  refine bind_congr fun k => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  simp only [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_runCKA_dhSchemeFb_eq Dh prng fs lam Δcka tStar qep ⟨true, tL, t⟩ false A
    (CKA.initState (dhScheme Dh) k b) (ckaStateInv_init Dh k b) (fun _ => rfl)]

theorem ckaBranch_redCKAPriv_dhSchemeFb_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType KR] [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka tStar qep : ℕ)
    (tL : Option ℕ) (i : ℕ) (b : Bool)
    (A : SchemeAdversary (CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    CKA.branch (dhSchemeFb Dh) Δcka tStar b
      (redCKAPriv (dhSchemeFb Dh) prng fs lam Δcka qep tL i A) =
    CKA.branch (dhScheme Dh) Δcka tStar b
      (redCKAPriv (dhScheme Dh) prng fs lam Δcka qep tL i A) := by
  rw [ckaBranch_dhSchemeFb_eq]
  unfold CKA.branch redCKAPriv
  refine bind_congr fun k => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  simp only [simulateQ_bind, StateT.run_bind]
  rw [sampleT, simulateQ_ckaFullImpl_liftProb]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun bSM => ?_
  rw [simulateQ_runCKA_dhSchemeFb_eq Dh prng fs lam Δcka tStar qep ⟨false, tL, i⟩ bSM A
    (CKA.initState (dhScheme Dh) k b) (ckaStateInv_init Dh k b) (fun _ => rfl)]

end InterpretedCKASwap

end CryptoVerification.LibsignalSession.Fig8SchemeBridge
