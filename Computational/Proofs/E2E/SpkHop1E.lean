/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1D
public import Computational.Proofs.E2E.SpkHop2A
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.GameHop.Fel

/-!
# Hop 2 Game-State Invariant

Defines the game-state invariant `Hop2GameInv` for `hop2Impl`, proves its preservation across
oracle steps, and introduces parity-indexed root-key patching (`partyOfParity`,
`patchGamePartyIdx`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq

section Hop2Coupling

open CryptoGames.CKA CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF MACScheme

set_option linter.unusedSectionVars false

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

omit [SampleableType Pt] in
theorem dh_lookup_isSome_prob_le_hop2CreateCollUnit
    (Dh : DHFun (BitVec 256) Pt) (hnez : ∀ r T, T ≠ 0 → Dh.dh r T ≠ 0)
    (T : Pt) (hT0 : T ≠ 0) (tbl : List (Pt × BitVec 256)) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
        fun r => pure (tbl.lookup (Dh.dh r T)).isSome] {true} ≤
      (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh := by
  have hev : ∀ (f : BitVec 256 → Bool),
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun r => pure (f r)] {true} =
        Pr{let r ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))}[f r = true] := fun f => by
    rw [prEvent_eq_evalDist_of_discrete]
    have hmap : (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun r => pure (f r)) =
        f <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
      simp [map_eq_bind_pure_comp]
    rw [hmap, evalDist_map_of_discrete,
      MeasureTheory.Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
    rfl
  have hlk : ∀ r : BitVec 256,
      (tbl.lookup (Dh.dh r T)).isSome = tbl.any (fun p => Dh.dh r T == p.1) := fun r => by
    induction tbl with
    | nil => rfl
    | cons hd tl ih => cases h : (Dh.dh r T == hd.1) <;> simp [List.lookup, h, ih]
  simp_rw [hlk, hev]
  refine (Computational.Proofs.GameHop.Fel.prEvent_any_list_le_sum
    ($ᵗ BitVec 256 : ProbComp (BitVec 256)) tbl (fun r p => Dh.dh r T == p.1)).trans ?_
  have hle : ∀ p ∈ tbl,
      Pr{let r ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))}[(Dh.dh r T == p.1) = true] ≤
        hop2CreateCollUnit Dh := fun ⟨Q, _⟩ _ => by
    rw [← hev (fun r => Dh.dh r T == Q)]
    simp only [beq_eq_decide]
    by_cases hQ : Q = 0
    · subst hQ; simp [fun r => decide_eq_false (hnez r T hT0)]
    · exact dh_createColl_prob_le_hop2CreateCollUnit Dh T Q hQ
  refine (List.sum_le_length_nsmul _ (hop2CreateCollUnit Dh) fun x hx => ?_).trans ?_
  · rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩; exact hle p hp
  · simp only [List.length_map, nsmul_eq_mul, le_rfl]

def pureStepHyb (k' : ℕ) (rc : Ratchet.RootKey × BitVec 256) (f : Pt → BitVec 256) : Hop2Hyb Pt :=
  ⟨k', rc, fun I => pure (f I)⟩

def pureStepImpl (f : Pt → BitVec 256) : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (fun I => (pure (f I) : ProbComp (BitVec 256)) : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem simulateQ_pureStepImpl_liftM {α : Type} (f : Pt → BitVec 256) (oa : ProbComp α) :
    simulateQ (pureStepImpl f) (liftM oa : Hop2Comp Pt α) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change (liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) >>=
        (fun u => simulateQ (pureStepImpl f) (liftM (k u))) = _
    congr 1
    funext u
    exact ih u

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem simulateQ_pureStepImpl_hop2Unif (f : Pt → BitVec 256) :
    simulateQ (pureStepImpl f) (hop2Unif (Pt := Pt)) = ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :=
  simulateQ_pureStepImpl_liftM f ($ᵗ BitVec 256)

omit [SampleableType Pt] in
theorem simulateQ_lazyImpl_hop2RecvHalf_pureStep {ℓ : ℕ}
    (P : Params Bytes PQC) (k' : ℕ) (rc : Ratchet.RootKey × BitVec 256) (f : Pt → BitVec 256)
    (idx : Option ℕ) (rk : Ratchet.RootKey) (their : PublicKey) (our : PrivateKey) (Q : Pt)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt))
      ((hop2RecvHalf P (pureStepHyb k' rc f) idx rk their our Q).run st)).run tbl =
      (·, tbl) <$> simulateQ (pureStepImpl f)
        ((hop2RecvHalf P (pureStepHyb k' rc f) idx rk their our Q).run st) := by
  unfold hop2RecvHalf
  cases idx with
  | none =>
    dsimp only []
    cases rootCreateChain P.C rk their our <;> simp [StateT.run_pure]
  | some t =>
    dsimp only [pureStepHyb]
    by_cases hQ0 : Q = 0
    · simp [hQ0, StateT.run_pure]
    · simp only [hQ0, ↓reduceIte]
      by_cases htle : t ≤ k'
      · simp only [htle, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
        cases st.2.made.lookup (t, Q) with
        | some ck => simp [StateT.run_pure]
        | none =>
          unfold hop2Lazy
          simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
          cases st.2.lazy.lookup (t, Q) with
          | some u => simp [StateT.run_pure]
          | none =>
            simp [StateT.run_bind, StateT.run_set, StateT.run_pure,
              bind_assoc, pure_bind, simulateQ_bind, simulateQ_lazyImpl_hop2Unif,
              simulateQ_pureStepImpl_hop2Unif, map_eq_bind_pure_comp, Function.comp_apply]
      · simp [htle, StateT.run_pure]

omit [SampleableType Pt] in
theorem simulateQ_lazyImpl_hop2SendHalf_pureStep
    (P : Params Bytes PQC) (k' : ℕ) (rc : Ratchet.RootKey × BitVec 256) (f : Pt → BitVec 256)
    (idx : Option ℕ) (rk : Ratchet.RootKey) (their : PublicKey) (our' : PrivateKey) (Q' : Pt)
    (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt))
      (hop2SendHalf P (pureStepHyb k' rc f) idx rk their our' Q')).run tbl =
      (·, tbl) <$> simulateQ (pureStepImpl f)
        (hop2SendHalf P (pureStepHyb k' rc f) idx rk their our' Q') := by
  unfold hop2SendHalf
  cases idx with
  | none =>
    dsimp only []
    cases rootCreateChain P.C rk their our' <;> simp [StateT.run_pure]
  | some j =>
    dsimp only [pureStepHyb]
    by_cases hQ0 : Q' = 0
    · simp [hQ0, StateT.run_pure]
    · simp only [hQ0, ↓reduceIte]
      by_cases hjlt : j < k'
      · simp [hjlt, simulateQ_bind, simulateQ_lazyImpl_hop2Unif,
          simulateQ_pureStepImpl_hop2Unif, StateT.run_bind, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      · simp only [hjlt, ↓reduceIte]
        by_cases hjeq : j = k' <;> simp [hjeq, StateT.run_pure]

omit [SampleableType Pt] in
theorem simulateQ_lazyImpl_hop2DH_pureStep {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k' : ℕ) (rc : Ratchet.RootKey × BitVec 256)
    (f : Pt → BitVec 256) (idx : Option ℕ) (coins : BitVec 256)
    (g : GhostState Bytes) (msg : SignalMessage) (rc' : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt))
      ((hop2DH (ℓ := ℓ) P Dh encT decT (pureStepHyb k' rc f) idx coins g msg rc').run st)).run tbl =
      (·, tbl) <$> simulateQ (pureStepImpl f)
        ((hop2DH (ℓ := ℓ) P Dh encT decT (pureStepHyb k' rc f) idx coins g msg rc').run st) := by
  unfold hop2DH
  cases decT msg.senderRatchetKey with
  | none => simp [StateT.run_pure]
  | some T =>
    dsimp only []
    split
    · simp [StateT.run_pure]
    · cases g.session.senderChain with
      | none => simp [StateT.run_pure]
      | some sc =>
        dsimp only []
        simp only [StateT.run_bind, simulateQ_bind,
          simulateQ_lazyImpl_hop2RecvHalf_pureStep P k' rc f idx g.session.rootKey
            msg.senderRatchetKey sc.ratchetKey.privateKey (Dh.dh coins T) st tbl,
          map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
        refine bind_congr fun r1 => ?_
        rcases r1 with ⟨opt1, st1⟩
        cases opt1 with
        | none => simp [StateT.run_pure]
        | some v1 =>
          rcases v1 with ⟨idx1, rkM, ckR⟩
          dsimp only []
          simp only [stateT_lift_run_hop2, StateT.run_bind, simulateQ_bind,
            simulateQ_lazyImpl_hop2SendHalf_pureStep P k' rc f idx1 rkM
              msg.senderRatchetKey (KeyPair.generate P.C rc').privateKey (Dh.dh rc' T) tbl,
            map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind
            ]
          refine bind_congr fun opt2 => ?_
          cases opt2 with
          | none => simp [StateT.run_pure]
          | some v2 =>
            rcases v2 with ⟨idx2, rk2, ckS, pend⟩
            dsimp only []
            rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper rc' _ with ⟨r_tr, s_out⟩
            cases r_tr <;> simp [StateT.run_pure]

omit [SampleableType Pt] in
theorem simulateQ_lazyImpl_hop2Recv_pureStep {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k' : ℕ) (rc : Ratchet.RootKey × BitVec 256)
    (f : Pt → BitVec 256) (g : GhostState Bytes) (c : Bytes) (rc' : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv (ℓ := ℓ) P Dh encT decT (pureStepHyb k' rc f) g c rc').run st)).run tbl =
      (·, tbl) <$> simulateQ (pureStepImpl f)
        ((hop2Recv (ℓ := ℓ) P Dh encT decT (pureStepHyb k' rc f) g c rc').run st) := by
  unfold hop2Recv
  cases SignalMessage.tryFrom P.codec c with
  | error _ => simp [StateT.run_pure]
  | ok msg =>
    dsimp only []
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.2.idx g.party with
    | none => simp [StateT.run_pure]
    | some t =>
      dsimp only []
      split
      · exact simulateQ_lazyImpl_hop2DH_pureStep P Dh encT decT k' rc f (some t)
          (st.2.coins g.party) g msg rc' st tbl
      · simp [StateT.run_pure]

omit [SampleableType Pt] in
theorem simulateQ_lazyImpl_hop2Impl_pureStep {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (k' : ℕ) (rc : Ratchet.RootKey × BitVec 256) (f : Pt → BitVec 256)
    (t : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt))
      ((hop2Impl P Dh encT decT qep s (pureStepHyb k' rc f) t).run st)).run tbl =
      (·, tbl) <$> simulateQ (pureStepImpl f)
        ((hop2Impl P Dh encT decT qep s (pureStepHyb k' rc f) t).run st) := by
  rcases t with u | t1
  · simp [hop2Impl, lazyImpl, pureStepImpl, StateT.run_bind,
      StateT.run_monadLift, monadLift_self, StateT.run_pure, bind_assoc, pure_bind,
      map_eq_bind_pure_comp, Function.comp_apply]
  · rcases t1 with t2 | y_corr
    · rcases t2 with t3 | ⟨Q, c⟩
      · rcases t3 with t4 | ⟨Q, c⟩
        · rcases t4 with y_tr | y_ch
          · simp [hop2Impl, hop2Lift, StateT.run_bind, simulateQ_bind,
              simulateQ_lazyImpl_liftM, simulateQ_pureStepImpl_liftM,
              StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
          · simp [hop2Impl, hop2Lift, StateT.run_bind, simulateQ_bind,
              simulateQ_lazyImpl_liftM, simulateQ_pureStepImpl_liftM,
              StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
        · dsimp only [hop2Impl]
          unfold hop2Deliver
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          split
          · simp [StateT.run_pure]
          · cases st.1.inTransit Q.other c with
            | none => simp [StateT.run_pure]
            | some r =>
              simp only [stateT_lift_run_hop2, StateT.run_bind, simulateQ_bind,
                simulateQ_lazyImpl_hop2Unif, stateT_lift_probComp_run,
                    simulateQ_pureStepImpl_hop2Unif,
                map_eq_bind_pure_comp,
                bind_assoc, pure_bind]
              refine bind_congr fun rc' => ?_
              rw [simulateQ_lazyImpl_hop2Recv_pureStep P Dh encT decT k' rc f (st.1.st Q) c rc' st
                  tbl]
              simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
              refine bind_congr fun r1 => ?_
              rcases r1 with ⟨opt1, st1⟩
              cases opt1 with
              | none => simp [StateT.run_pure]
              | some v1 =>
                rcases v1 with ⟨⟨st', t', i', m'⟩, u⟩
                simp [StateT.run_set, StateT.run_pure]
      · dsimp only [hop2Impl]
        unfold hop2Inject
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · simp [StateT.run_pure]
        · simp only [stateT_lift_run_hop2, StateT.run_bind, simulateQ_bind,
            simulateQ_lazyImpl_hop2Unif, stateT_lift_probComp_run, simulateQ_pureStepImpl_hop2Unif,
            map_eq_bind_pure_comp,
            bind_assoc, pure_bind]
          refine bind_congr fun rc' => ?_
          rw [simulateQ_lazyImpl_hop2Recv_pureStep P Dh encT decT k' rc f (st.1.st Q) c rc' st tbl]
          simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
          refine bind_congr fun r1 => ?_
          rcases r1 with ⟨opt1, st1⟩
          cases opt1 with
          | none => simp [StateT.run_pure]
          | some v1 =>
            rcases v1 with ⟨⟨st', t', i', m'⟩, u⟩
            simp only [StateT.run_bind, StateT.run_get, pure_bind]
            split
            · simp [StateT.run_set, StateT.run_pure]
            · split <;> simp [StateT.run_set, StateT.run_pure]
    · simp [hop2Impl, hop2Lift, StateT.run_bind, simulateQ_bind,
        simulateQ_lazyImpl_liftM, simulateQ_pureStepImpl_liftM,
        StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]

omit [SampleableType Pt] in
theorem simulateQ_prfReal_hop2Impl_run {ℓ : ℕ} {α : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (k' : ℕ) (rc : Ratchet.RootKey × BitVec 256) (f : Pt → BitVec 256)
    (m : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) α)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt))
      ((simulateQ (hop2Impl P Dh encT decT qep s (pureStepHyb k' rc f)) m).run st)).run tbl =
      (·, tbl) <$> simulateQ (pureStepImpl f)
        ((simulateQ (hop2Impl P Dh encT decT qep s (pureStepHyb k' rc f)) m).run st) := by
  induction m using OracleComp.inductionOn generalizing st tbl with
  | pure a => simp [StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      StateT.run_bind,
      simulateQ_lazyImpl_hop2Impl_pureStep P Dh encT decT qep s k' rc f t st tbl,
      map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    refine bind_congr fun z => ?_
    simpa only [map_eq_bind_pure_comp, Function.comp_apply, id_eq] using ih z.1 z.2 tbl

omit [SampleableType Pt] in
theorem simulateQ_prfReal_hop2Impl_eq_runHop2 {ℓ : ℕ} {α : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (k' : ℕ) (rc : Ratchet.RootKey × BitVec 256) (f : Pt → BitVec 256)
    (m : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) α)
    (st : Hop2State Pt ℓ) :
    ( do
        let (_, fin) ← simulateQ (pureStepImpl f)
          ((simulateQ (hop2Impl P Dh encT decT qep s (pureStepHyb k' rc f)) m).run st)
        return fin.2.bad : ProbComp Bool ) =
      runHop2 P Dh encT decT qep s (pureStepHyb k' rc f) m st [] := by
  unfold runHop2
  rw [StateT.run'_eq, simulateQ_bind, StateT.run_bind,
    simulateQ_prfReal_hop2Impl_run P Dh encT decT qep s k' rc f m st []]
  simp [StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply,
    bind_assoc, pure_bind]

omit [SampleableType Pt] in
theorem evalDist_runHop2_tbl_discard {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) (I : Pt) :
    𝒟[(do
      let (_, tbl') ← (lazyStep I).run tbl
      runHop2 P Dh encT decT qep s h oa st tbl')] =
      𝒟[runHop2 P Dh encT decT qep s h oa st tbl] := by
  simpa [runHop2, StateT.run'_eq, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc] using
    evalDist_lazyStep_discard I (do
      let (_, fin) ← (simulateQ (hop2Impl P Dh encT decT qep s h) oa).run st
      return fin.2.bad) tbl

/-- Game-state invariant for `hop2Impl` tracking party tags, sender-chain invariants,
ratchet-key admissibility of in-transit records, and sender-key coins. -/
structure Hop2GameInv {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (st : Hop2State Pt ℓ) : Prop where
  party_eq : ∀ Q : Party, (st.1.st Q).party = Q
  sender_inv : ∀ Q : Party, SpkHop2.SessionSenderInv P (st.1.st Q).session
  trans_inv : ∀ r ∈ st.1.trans, ratchetKeyAdmissible protoSignalCodec decT encT r.ct = true
  coins_sc : ∀ Q : Party, st.2.idx Q ≠ none →
    ∃ ckS0, (st.1.st Q).session.senderChain =
      some ⟨KeyPair.generate P.C (st.2.coins Q), ckS0⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2GameInv_init {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool) (ck0 x alice pqr ck1 : BitVec 256) (I0 : Pt) :
    let spk := (KeyPair.generate P.C x).publicKey
    let sessA := ((SessionState.new currentVersion P.idA P.idB 0
      (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
      (KeyPair.generate P.C alice) ⟨ck1, 0⟩
    let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
    let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
    let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
      { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
    let aux0 : Hop2Aux Pt :=
      { made := [((0, I0), ck1)]
        idx := fun Q => match Q with | .A => some 1 | .B => some 0
        coins := fun Q => match Q with | .A => alice | .B => x }
    Hop2GameInv P decT encT (initSt, aux0) := by
  intro spk sessA stA stB initSt aux0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q; cases Q <;> rfl
  · intro Q; cases Q with
    | A =>
      refine ⟨rfl, ?_⟩
      intro sc hsc
      dsimp only [initSt, stA, sessA, SessionState.setUnacknowledgedPreKeyMessage,
        SessionState.setSenderChain, SessionState.addReceiverChain, SessionState.new] at hsc
      injection hsc with h; subst h
      exact ⟨alice, rfl⟩
    | B => exact SpkHop2.sessionSenderInv_initB P ⟨0, ck0, x, alice, pqr⟩
  · intro r hr; cases hr
  · intro Q _
    cases Q with
    | A => exact ⟨⟨ck1, 0⟩, rfl⟩
    | B => exact ⟨⟨ck0, 0⟩, rfl⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem inTransit_hop2GameInv {ℓ : ℕ}
    {P : Params Bytes PQC} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {st : Hop2State Pt ℓ} (hinv : Hop2GameInv P decT encT st)
    {Q : Party} {c : Bytes} {r : SM.Record (CBC.Plain ℓ) Bytes}
    (htr : st.1.inTransit Q c = some r) :
    ratchetKeyAdmissible protoSignalCodec decT encT c = true := by
  unfold SM.GameState.inTransit at htr
  have hmem : r ∈ st.1.trans := List.mem_of_find?_eq_some htr
  have hpred := List.find?_some htr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  rw [← hpred.2]
  exact hinv.trans_inv r hmem

theorem transmitR_support_hop2GameInv {ℓ : ℕ} (P : Params Bytes PQC)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (x : Party × CBC.Plain ℓ × Option PQC)
    (st : Hop2State Pt ℓ) (hinv : Hop2GameInv P decT encT st) :
    ∀ z ∈ support ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st.1),
      Hop2GameInv P decT encT (z.2, st.2) := by
  rcases x with ⟨Q, m, r_opt⟩
  intro z hz
  unfold SM.transmitR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st.1 Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hinv
    · rw [StateT.run_bind] at hz
      simp only [StateT.run_monadLift, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz2⟩
      cases hep : st.1.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz2
        subst hz2; exact hinv
      | some s₁ =>
        simp only [hep, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hz2
        subst hz2
        obtain ⟨hst1, htr1⟩ := GameEq.epMgmt_st_trans hep
        have hsend_eq : ∀ s0, ((sessionSchemeU P ℓ).sendPart.send s0 m cb.1) =
            ((sessionSchemeU P ℓ).send s0 m cb.1) := fun _ => rfl
        rw [hsend_eq, hst1]
        have hprops := sessionSchemeU_send_props P (st.1.st Q) m cb.1
        obtain ⟨hsend_inv, _, _⟩ :=
          SpkHop2.sessionSenderInv_send P (st.1.st Q) m cb.1 (hinv.sender_inv Q)
        have horc : ratchetKeyAdmissible protoSignalCodec decT encT
            ((sessionSchemeU P ℓ).send (st.1.st Q) m cb.1).2 = true :=
          SpkHop2.ratchetKeyOnCurve_send P hcodec hL Dh encPt encT decT hX hdec (st.1.st Q)
            (hinv.sender_inv Q).1 (hinv.sender_inv Q).2 m cb.1
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro R
          unfold SM.GameState.record; dsimp only []; rw [hst1]
          by_cases hR : R = Q
          · subst hR; rw [Function.update_self]; exact hprops.1.trans (hinv.party_eq R)
          · rw [Function.update_of_ne hR]; exact hinv.party_eq R
        · intro R
          unfold SM.GameState.record; dsimp only []; rw [hst1]
          by_cases hR : R = Q
          · subst hR; rw [Function.update_self]; exact hsend_inv
          · rw [Function.update_of_ne hR]; exact hinv.sender_inv R
        · intro r hr
          unfold SM.GameState.record at hr; dsimp only [] at hr
          rcases List.mem_cons.mp hr with rfl | hr_old
          · exact horc
          · rw [htr1] at hr_old; exact hinv.trans_inv r hr_old
        · intro R hidxR
          unfold SM.GameState.record; dsimp only []; rw [hst1]
          by_cases hR : R = Q
          · subst hR; rw [Function.update_self]
            obtain ⟨ckS0, hsc0⟩ := hinv.coins_sc R hidxR
            exact send_preserves_senderChain_ratchetKey P (st.1.st R)
              (KeyPair.generate P.C (st.2.coins R)) ckS0 m.toList cb.1 hsc0
          · rw [Function.update_of_ne hR]; exact hinv.coins_sc R hidxR
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hinv

theorem challR_support_hop2GameInv {ℓ : ℕ} (P : Params Bytes PQC)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (st : Hop2State Pt ℓ) (hinv : Hop2GameInv P decT encT st) :
    ∀ z ∈ support ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st.1),
      Hop2GameInv P decT encT (z.2, st.2) := by
  rcases x with ⟨Q, m₀, m₁, r_opt⟩
  intro z hz
  unfold SM.challR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st.1 Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hinv
    · rw [StateT.run_bind] at hz
      simp only [StateT.run_monadLift, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz2⟩
      cases hep : st.1.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz2
        subst hz2; exact hinv
      | some s₁ =>
        rw [hep] at hz2
        dsimp only [] at hz2
        split at hz2
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz2
          subst hz2; exact hinv
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hz2
          subst hz2
          obtain ⟨hst1, htr1⟩ := GameEq.epMgmt_st_trans hep
          set m := (SM.Config.h1.challMsg (s₁.epoch Q)).getD (if st.1.b then m₁ else m₀)
          have hsend_eq : ∀ s0, ((sessionSchemeU P ℓ).sendPart.send s0 m cb.1) =
              ((sessionSchemeU P ℓ).send s0 m cb.1) := fun _ => rfl
          rw [hsend_eq, hst1]
          have hprops := sessionSchemeU_send_props P (st.1.st Q) m cb.1
          obtain ⟨hsend_inv, _, _⟩ :=
            SpkHop2.sessionSenderInv_send P (st.1.st Q) m cb.1 (hinv.sender_inv Q)
          have horc : ratchetKeyAdmissible protoSignalCodec decT encT
              ((sessionSchemeU P ℓ).send (st.1.st Q) m cb.1).2 = true :=
            SpkHop2.ratchetKeyOnCurve_send P hcodec hL Dh encPt encT decT hX hdec (st.1.st Q)
              (hinv.sender_inv Q).1 (hinv.sender_inv Q).2 m cb.1
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro R
            unfold SM.GameState.record; dsimp only []; rw [hst1]
            by_cases hR : R = Q
            · subst hR; rw [Function.update_self]; exact hprops.1.trans (hinv.party_eq R)
            · rw [Function.update_of_ne hR]; exact hinv.party_eq R
          · intro R
            unfold SM.GameState.record; dsimp only []; rw [hst1]
            by_cases hR : R = Q
            · subst hR; rw [Function.update_self]; exact hsend_inv
            · rw [Function.update_of_ne hR]; exact hinv.sender_inv R
          · intro r hr
            unfold SM.GameState.record at hr; dsimp only [] at hr
            rcases List.mem_cons.mp hr with rfl | hr_old
            · exact horc
            · rw [htr1] at hr_old; exact hinv.trans_inv r hr_old
          · intro R hidxR
            unfold SM.GameState.record; dsimp only []; rw [hst1]
            by_cases hR : R = Q
            · subst hR; rw [Function.update_self]
              obtain ⟨ckS0, hsc0⟩ := hinv.coins_sc R hidxR
              exact send_preserves_senderChain_ratchetKey P (st.1.st R)
                (KeyPair.generate P.C (st.2.coins R)) ckS0 m.toList cb.1 hsc0
            · rw [Function.update_of_ne hR]; exact hinv.coins_sc R hidxR
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hinv

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrR_support_hop2GameInv {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (x : Party)
    (st : Hop2State Pt ℓ) (hinv : Hop2GameInv P decT encT st) :
    ∀ z ∈ support ((SM.corrR (configRefuseEarlyBobCorr decT encT) x).run st.1),
      Hop2GameInv P decT encT (z.2, st.2) := by
  intro z hz
  unfold SM.corrR at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hinv
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hinv.party_eq, hinv.sender_inv, hinv.trans_inv, hinv.coins_sc⟩

omit [SampleableType Pt] in
theorem hop2RecvHalf_support_props {ℓ : ℕ} (P : Params Bytes PQC) (h : Hop2Hyb Pt)
    (idx : Option ℕ) (rk : Ratchet.RootKey) (their : PublicKey) (our : PrivateKey) (Q : Pt)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (z : (Option (Option ℕ × Ratchet.RootKey × BitVec 256) × Hop2State Pt ℓ) × List (Pt × BitVec
        256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2RecvHalf P h idx rk their our Q).run st)).run tbl)) :
    z.1.2.1 = st.1 ∧ z.1.2.2.bad = st.2.bad ∧
    z.1.2.2.idx = st.2.idx ∧ z.1.2.2.coins = st.2.coins ∧ z.1.2.2.made = st.2.made := by
  unfold hop2RecvHalf at hz
  cases idx with
  | none =>
    dsimp only [] at hz
    cases hcc : rootCreateChain P.C rk their our with
    | error _ =>
      rw [hcc] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | ok p =>
      rcases p with ⟨rk', ck⟩
      rw [hcc] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some t =>
    dsimp only [] at hz
    split_ifs at hz with hQ0 htle
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
      cases hmade : st.2.made.lookup (t, Q) with
      | some ck =>
        rw [hmade] at hz
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | none =>
        rw [hmade] at hz
        unfold hop2Lazy at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc] at hz
        cases hlazy : st.2.lazy.lookup (t, Q) with
        | some u =>
          rw [hlazy] at hz
          simp only [StateT.run_pure] at hz
          subst hz; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        | none =>
          rw [hlazy] at hz
          simp only [stateT_lift_run_hop2, StateT.run_bind, StateT.run_set, StateT.run_pure,
            bind_assoc, pure_bind, simulateQ_bind, simulateQ_lazyImpl_hop2Unif,
            stateT_lift_probComp_run, simulateQ_pure, MonadAttach.mem_support_bind,
            support_pure, Set.mem_singleton_iff] at hz
          rcases hz with ⟨u, _, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [stateT_lift_run_hop2, StateT.run_bind, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, bind_assoc, pure_bind] at hz
      rcases hz with ⟨⟨u, tbl'⟩, _, rfl⟩
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [SampleableType Pt] in
theorem hop2DH_support_hop2GameInv {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (idx : Option ℕ) (coins : BitVec 256)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hfind : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none)
    (hsinv : SpkHop2.SessionSenderInv P g.session)
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2DH P Dh encT decT h idx coins g msg rc).run st)).run tbl)) :
    z.1.2.1 = st.1 ∧ z.1.2.2.bad = st.2.bad ∧
    z.1.2.2.idx = st.2.idx ∧ z.1.2.2.coins = st.2.coins ∧ z.1.2.2.made = st.2.made ∧
    ∀ st' t' i' m' u, z.1.1 = some ((st', t', i', m'), u) →
      st'.party = g.party ∧
      SpkHop2.SessionSenderInv P st'.session ∧
      ∃ ckS0, st'.session.senderChain =
        some ⟨KeyPair.generate P.C ((hop2Commit st.2 g.party u).coins g.party), ckS0⟩ := by
  unfold hop2DH at hz
  cases hdec : decT msg.senderRatchetKey with
  | none =>
    rw [hdec] at hz
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ _ h => by cases h⟩
  | some T =>
    rw [hdec] at hz
    dsimp only [] at hz
    split_ifs at hz with hT
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ _ h => by cases h⟩
    · cases hsc : g.session.senderChain with
      | none =>
        rw [hsc] at hz
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ _ h => by cases h⟩
      | some sc =>
        rw [hsc] at hz
        simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨⟨⟨r1, st1⟩, tbl1⟩, hz1, hz2⟩
        have h1 := hop2RecvHalf_support_props P h idx g.session.rootKey msg.senderRatchetKey
          sc.ratchetKey.privateKey (Dh.dh coins T) st tbl _ hz1
        cases r1 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz2
          subst hz2; exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2,
              fun _ _ _ _ _ h => by cases h⟩
        | some p1 =>
          rcases p1 with ⟨idx1, rkM, ckR⟩
          simp only [stateT_lift_run_hop2, StateT.run_bind, bind_assoc, pure_bind,
            simulateQ_bind, MonadAttach.mem_support_bind] at hz2
          rcases hz2 with ⟨⟨r2, tbl2⟩, _, hz3⟩
          cases r2 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz3
            subst hz3; exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2,
                fun _ _ _ _ _ h => by cases h⟩
          | some p2 =>
            rcases p2 with ⟨idx2, rk2, ckS, pend⟩
            dsimp only [] at hz3
            set prev := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
            have hstep := tryDecryptFromRecord_steppedSess P g msg rc prev
              rk2 ckR (some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩) hfind
            dsimp only [] at hstep
            rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper rc
              { steppedSessBase g msg prev ckR with
                rootKey := rk2
                senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ } with ⟨r_tr, s_out⟩
            have htr' : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper rc
              { g.session with
                previousCounter := prev
                rootKey := rk2
                receiverChains := RatchetState.evictReceiverChains
                  (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ } = (r_tr, s_out) := htr
            rw [htr'] at hz3
            cases r_tr with
            | error _ =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hz3
              subst hz3; exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2,
                  fun _ _ _ _ _ h => by cases h⟩
            | ok m_plain =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hz3
              subst hz3
              refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2,
                  fun st' t' i' m' u hsome => ?_⟩
              injection hsome with hpair
              rcases Prod.mk.inj hpair with ⟨h4, rfl⟩
              rcases Prod.mk.inj h4 with ⟨rfl, _⟩
              have hsinv_in : SpkHop2.SessionSenderInv P
                  { steppedSessBase g msg prev ckR with
                    rootKey := rk2
                    senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ } := by
                refine ⟨hsinv.1, ?_⟩
                intro sc' hsc'
                dsimp only [steppedSessBase] at hsc'
                injection hsc' with h_eq; subst h_eq
                exact ⟨rc, rfl⟩
              have hsinv_out : SpkHop2.SessionSenderInv P s_out :=
                SpkHop2.tryDecryptFromRecord_preserve_sender P (P.expectedAddrs g.party)
                  msg rc _ s_out m_plain hsinv_in htr
              have hs_out_sc : s_out.senderChain = some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ := by
                rw [htr] at hstep
                injection hstep with _ hs_eq
                rw [hs_eq]
              refine ⟨rfl, hsinv_out, ?_⟩
              dsimp only [hop2Commit]
              rw [Function.update_self]
              exact ⟨⟨ckS, 0⟩, hs_out_sc⟩

omit [SampleableType Pt] in
theorem hop2Recv_support_hop2GameInv {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (Q : Party) (c : Bytes) (rc : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hinv : Hop2GameInv P decT encT st)
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st)).run tbl)) :
    z.1.2.1 = st.1 ∧ z.1.2.2.bad = st.2.bad ∧
    z.1.2.2.idx = st.2.idx ∧ z.1.2.2.coins = st.2.coins ∧ z.1.2.2.made = st.2.made ∧
    ∀ st' t' i' m' u, z.1.1 = some ((st', t', i', m'), u) →
      st'.party = Q ∧
      SpkHop2.SessionSenderInv P st'.session ∧
      ((hop2Commit st.2 Q u).idx Q ≠ none →
        ∃ ckS0, st'.session.senderChain =
          some ⟨KeyPair.generate P.C ((hop2Commit st.2 Q u).coins Q), ckS0⟩) := by
  set g := st.1.st Q
  have hpartyQ : g.party = Q := hinv.party_eq Q
  unfold hop2Recv at hz
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ =>
    rw [htry] at hz
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ _ h => by cases h⟩
  | ok msg =>
    rw [htry] at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hpartyQ] at hz
    cases hidx : st.2.idx Q with
    | none =>
      rw [hidx] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun st' t' i' m' u hsome => ?_⟩
      simp only [Option.map_eq_some_iff] at hsome
      rcases hsome with ⟨⟨st1, t1, i1, m1⟩, hrec, hpair⟩
      rcases Prod.mk.inj hpair with ⟨h4, rfl⟩
      rcases Prod.mk.inj h4 with ⟨rfl, _⟩
      have hsinv := SpkHop2.sessionSenderInv_receive P g c rc (st1, t1, i1, m1)
        (hinv.sender_inv Q) hrec
      refine ⟨hsinv.2.1.trans hpartyQ, hsinv.1, fun hne => ?_⟩
      dsimp only [hop2Commit] at hne
      exact absurd hidx hne
    | some t =>
      rw [hidx] at hz
      dsimp only [] at hz
      cases hfind :
          g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
      | none =>
        rw [hfind] at hz
        simp only [Option.isNone_none, ↓reduceIte] at hz
        have hdh := hop2DH_support_hop2GameInv P Dh encT decT h (some t) (st.2.coins Q)
          g msg rc st tbl hfind (hinv.sender_inv Q) z hz
        refine ⟨hdh.1, hdh.2.1, hdh.2.2.1, hdh.2.2.2.1, hdh.2.2.2.2.1,
            fun st' t' i' m' u hsome => ?_⟩
        obtain ⟨hp, hs, hsc⟩ := hdh.2.2.2.2.2 st' t' i' m' u hsome
        rw [hpartyQ] at hsc
        exact ⟨hp.trans hpartyQ, hs, fun _ => hsc⟩
      | some i =>
        rw [hfind] at hz
        simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun st' t' i' m' u hsome => ?_⟩
        simp only [Option.map_eq_some_iff] at hsome
        rcases hsome with ⟨⟨st1, t1, i1, m1⟩, hrec, hpair⟩
        rcases Prod.mk.inj hpair with ⟨h4, rfl⟩
        rcases Prod.mk.inj h4 with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨rfl, rfl⟩
        have hsinv := SpkHop2.sessionSenderInv_receive P g c rc (st1, t1, i1, m1)
          (hinv.sender_inv Q) hrec
        refine ⟨hsinv.2.1.trans hpartyQ, hsinv.1, fun hne => ?_⟩
        dsimp only [hop2Commit]
        have hrec_raw : (P.receive g c rc).map (fun x => (x.1, x.2.1, x.2.2.1,
            padOrTruncatePlain ℓ x.2.2.2)) =
            some (st1, t1, i1, m1) := hrec
        simp only [Option.map_eq_some_iff] at hrec_raw
        rcases hrec_raw with ⟨⟨g0, t0, i0, m0⟩, hrec0, htuple⟩
        rcases Prod.mk.inj htuple with ⟨rfl, _⟩
        have hset_self : setRootKey g.session.rootKey g = g := by
          cases g; rfl
        have hsc_eq := ((receive_setRootKey_of_findIdx_some P g.session.rootKey g c rc msg i
          htry hfind).2 g0 t0 i0 m0 hrec0).1
        obtain ⟨ckS0, hsc0⟩ := hinv.coins_sc Q (by simp [hidx])
        exact ⟨ckS0, hsc_eq.trans hsc0⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2DeliverPost_preserves_hop2GameInv {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (s : BitVec 256) (Q : Party) (c : Bytes) (r : SM.Record (CBC.Plain ℓ) Bytes)
    (st st2 : Hop2State Pt ℓ) (o : Hop2Out Pt ℓ)
    (hinv : Hop2GameInv P decT encT st)
    (hst1 : st2.1 = st.1) (hidx : st2.2.idx = st.2.idx) (hcoins : st2.2.coins = st.2.coins)
    (hsome : ∀ st' t' i' m' u, o = some ((st', t', i', m'), u) →
      st'.party = Q ∧
      SpkHop2.SessionSenderInv P st'.session ∧
      ((hop2Commit st.2 Q u).idx Q ≠ none →
        ∃ ckS0, st'.session.senderChain =
          some ⟨KeyPair.generate P.C ((hop2Commit st.2 Q u).coins Q), ckS0⟩)) :
    Hop2GameInv P decT encT (hop2DeliverPost P s Q c (st.1.st Q) r o st2).2 := by
  cases o with
  | none =>
    dsimp only [hop2DeliverPost]
    exact ⟨hst1 ▸ hinv.party_eq, hst1 ▸ hinv.sender_inv, hst1 ▸ hinv.trans_inv,
      fun R hR => hst1 ▸ hcoins ▸ hinv.coins_sc R (hidx ▸ hR)⟩
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    obtain ⟨hp, hs, hsc⟩ := hsome st' t' i' m' u rfl
    dsimp only [hop2DeliverPost]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro R; unfold SM.GameState.accept; dsimp only []; rw [hst1]
      by_cases hR : R = Q
      · subst hR; rw [Function.update_self]; exact hp
      · rw [Function.update_of_ne hR]; exact hinv.party_eq R
    · intro R; unfold SM.GameState.accept; dsimp only []; rw [hst1]
      by_cases hR : R = Q
      · subst hR; rw [Function.update_self]; exact hs
      · rw [Function.update_of_ne hR]; exact hinv.sender_inv R
    · intro r' hr'
      unfold SM.GameState.accept SM.GameState.delete at hr'; dsimp only [] at hr'
      rw [hst1] at hr'
      exact hinv.trans_inv r' (List.mem_of_mem_filter hr')
    · intro R hidxR
      unfold SM.GameState.accept; dsimp only [] at hidxR ⊢; rw [hst1]
      have hcomm_idx : (hop2Commit st2.2 Q u).idx = (hop2Commit st.2 Q u).idx := by
        cases u <;> simp [hop2Commit, hidx]
      have hcomm_coins : (hop2Commit st2.2 Q u).coins = (hop2Commit st.2 Q u).coins := by
        cases u <;> simp [hop2Commit, hcoins]
      rw [hcomm_idx] at hidxR
      rw [hcomm_coins]
      by_cases hR : R = Q
      · subst hR; rw [Function.update_self]; exact hsc hidxR
      · rw [Function.update_of_ne hR]
        have hidxR' : st.2.idx R ≠ none := by
          cases u with
          | none => exact hidxR
          | some upd => simp [hop2Commit, Function.update_of_ne hR] at hidxR; exact hidxR
        have hcoinsR : (hop2Commit st.2 Q u).coins R = st.2.coins R := by
          cases u <;> simp [hop2Commit, Function.update_of_ne hR]
        rw [hcoinsR]
        exact hinv.coins_sc R hidxR'

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2InjectPost_preserves_hop2GameInv {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qep : ℕ) (s : BitVec 256) (Q : Party) (c : Bytes)
    (st st2 : Hop2State Pt ℓ) (o : Hop2Out Pt ℓ)
    (hinv : Hop2GameInv P decT encT st)
    (hst1 : st2.1 = st.1) (hidx : st2.2.idx = st.2.idx) (hcoins : st2.2.coins = st.2.coins)
    (hsome : ∀ st' t' i' m' u, o = some ((st', t', i', m'), u) →
      st'.party = Q ∧
      SpkHop2.SessionSenderInv P st'.session ∧
      ((hop2Commit st.2 Q u).idx Q ≠ none →
        ∃ ckS0, st'.session.senderChain =
          some ⟨KeyPair.generate P.C ((hop2Commit st.2 Q u).coins Q), ckS0⟩)) :
    Hop2GameInv P decT encT (hop2InjectPost P qep s Q c (st.1.st Q) o st2).2 := by
  cases o with
  | none =>
    dsimp only [hop2InjectPost]
    exact ⟨hst1 ▸ hinv.party_eq, hst1 ▸ hinv.sender_inv, hst1 ▸ hinv.trans_inv,
      fun R hR => hst1 ▸ hcoins ▸ hinv.coins_sc R (hidx ▸ hR)⟩
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    obtain ⟨hp, hs, hsc⟩ := hsome st' t' i' m' u rfl
    dsimp only [hop2InjectPost]
    split_ifs with hqep htriv
    · refine ⟨hst1 ▸ hinv.party_eq, hst1 ▸ hinv.sender_inv, hst1 ▸ hinv.trans_inv, ?_⟩
      intro R hR; dsimp only [] at hR ⊢; rw [hst1, hcoins]; exact hinv.coins_sc R (hidx ▸ hR)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro R; unfold SM.GameState.accept; dsimp only []; rw [hst1]
        by_cases hR : R = Q
        · subst hR; rw [Function.update_self]; exact hp
        · rw [Function.update_of_ne hR]; exact hinv.party_eq R
      · intro R; unfold SM.GameState.accept; dsimp only []; rw [hst1]
        by_cases hR : R = Q
        · subst hR; rw [Function.update_self]; exact hs
        · rw [Function.update_of_ne hR]; exact hinv.sender_inv R
      · intro r' hr'
        unfold SM.GameState.accept SM.GameState.delete at hr'; dsimp only [] at hr'
        rw [hst1] at hr'
        exact hinv.trans_inv r' (List.mem_of_mem_filter hr')
      · intro R hidxR
        unfold SM.GameState.accept; dsimp only [] at hidxR ⊢; rw [hst1]
        have hcomm_idx : (hop2Commit { st2.2 with
                                       bad := st2.2.bad || hop2BadAt P s (st.1.st Q) c } Q u).idx =
            (hop2Commit st.2 Q u).idx := by
          cases u <;> simp [hop2Commit, hidx]
        have hcomm_coins : (hop2Commit { st2.2 with
                                         bad := st2.2.bad ||
                                         hop2BadAt P s (st.1.st Q) c } Q u).coins =
            (hop2Commit st.2 Q u).coins := by
          cases u <;> simp [hop2Commit, hcoins]
        rw [hcomm_idx] at hidxR
        rw [hcomm_coins]
        by_cases hR : R = Q
        · subst hR; rw [Function.update_self]; exact hsc hidxR
        · rw [Function.update_of_ne hR]
          have hidxR' : st.2.idx R ≠ none := by
            cases u with
            | none => exact hidxR
            | some upd => simp [hop2Commit, Function.update_of_ne hR] at hidxR; exact hidxR
          have hcoinsR : (hop2Commit st.2 Q u).coins R = st.2.coins R := by
            cases u <;> simp [hop2Commit, Function.update_of_ne hR]
          rw [hcoinsR]
          exact hinv.coins_sc R hidxR'
    · refine ⟨hst1 ▸ hinv.party_eq, hst1 ▸ hinv.sender_inv, hst1 ▸ hinv.trans_inv, ?_⟩
      intro R hR; dsimp only [] at hR ⊢; rw [hst1, hcoins]; exact hinv.coins_sc R (hidx ▸ hR)

/-- The party whose chain indices have parity `t % 2` (`0 ↦ .B`, `1 ↦ .A`). -/
def partyOfParity (t : ℕ) : Party :=
  if t % 2 = 0 then .B else .A

@[simp] theorem partyOfParity_zero : partyOfParity 0 = .B := rfl
@[simp] theorem partyOfParity_one : partyOfParity 1 = .A := rfl

theorem partyOfParity_succ (t : ℕ) : partyOfParity (t + 1) = (partyOfParity t).other := by
  unfold partyOfParity Party.other
  by_cases h : t % 2 = 0
  · have h1 : (t + 1) % 2 ≠ 0 := by omega
    simp [h, h1]
  · have h1 : (t + 1) % 2 = 0 := by omega
    simp [h, h1]

@[simp] theorem partyOfParity_add_two (t : ℕ) : partyOfParity (t + 2) = partyOfParity t := by
  unfold partyOfParity
  rw [Nat.add_mod_right]

theorem partyOfParity_succ_ne (t : ℕ) : partyOfParity (t + 1) ≠ partyOfParity t := by
  rw [partyOfParity_succ]
  cases partyOfParity t <;> decide

def patchGamePartyIdx {ℓ : ℕ} (m : ℕ) (rk : Ratchet.RootKey) (idx : Party → Option ℕ)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
  { s with st := fun Q => patchPartyIdx m rk (idx Q) (s.st Q) }

@[simp] theorem patchPartyIdx_party (m : ℕ) (rk : Ratchet.RootKey) (idx : Option ℕ)
    (g : GhostState Bytes) :
    (patchPartyIdx m rk idx g).party = g.party := by
  unfold patchPartyIdx; split <;> rfl

@[simp] theorem patchPartyIdx_chainEpochs (m : ℕ) (rk : Ratchet.RootKey) (idx : Option ℕ)
    (g : GhostState Bytes) :
    (patchPartyIdx m rk idx g).chainEpochs = g.chainEpochs := by
  unfold patchPartyIdx; split <;> rfl

@[simp] theorem patchPartyIdx_epoch (m : ℕ) (rk : Ratchet.RootKey) (idx : Option ℕ)
    (g : GhostState Bytes) :
    (patchPartyIdx m rk idx g).epoch = g.epoch := by
  unfold patchPartyIdx; split <;> rfl

@[simp] theorem hop2BadAt_patchPartyIdx (P : Params Bytes PQC) (s : BitVec 256)
    (m : ℕ) (rk : Ratchet.RootKey) (idx : Option ℕ) (g : GhostState Bytes) (c : Bytes) :
    hop2BadAt P s (patchPartyIdx m rk idx g) c = hop2BadAt P s g c := by
  unfold hop2BadAt
  simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2Absorbed_of_patchGamePartyIdx {ℓ : ℕ} (m : ℕ) (rk : Ratchet.RootKey)
    (st_L st_R : Hop2State Pt ℓ)
    (hst : st_L.1 = patchGamePartyIdx m rk st_R.2.idx st_R.1)
    (hbad : st_L.2.bad = st_R.2.bad) :
    Hop2Absorbed st_L ↔ Hop2Absorbed st_R := by
  unfold Hop2Absorbed
  rw [hst, hbad]
  dsimp only [patchGamePartyIdx]
  simp only [patchPartyIdx_party, patchPartyIdx_chainEpochs]

@[simp] theorem patchGamePartyIdx_noBobEpoch0 {ℓ : ℕ} (m : ℕ) (rk : Ratchet.RootKey)
    (idx : Party → Option ℕ) (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Q : Party) :
    noBobSendInEpoch0 (patchGamePartyIdx m rk idx s) Q = noBobSendInEpoch0 s Q := rfl

theorem patchGamePartyIdx_epMgmt {ℓ : ℕ} (m : ℕ) (rk : Ratchet.RootKey)
    (idx : Party → Option ℕ) (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Δ qep : ℕ) (Q : Party) (bad : Bool) :
    (patchGamePartyIdx m rk idx s).epMgmt Δ qep Q bad =
      (s.epMgmt Δ qep Q bad).map (patchGamePartyIdx m rk idx) := by
  unfold SM.GameState.epMgmt SM.GameState.safeCh SM.GameState.leak patchGamePartyIdx
  dsimp only []
  split_ifs <;> simp

theorem patchGamePartyIdx_record {ℓ : ℕ} (m : ℕ) (rk : Ratchet.RootKey)
    (idx : Party → Option ℕ) (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Δ : ℕ) (Q : Party) (st' : GhostState Bytes) (r : SM.Record (CBC.Plain ℓ) Bytes) (isChall :
        Bool) :
    (patchGamePartyIdx m rk idx s).record Δ Q (patchPartyIdx m rk (idx Q) st') r isChall =
      patchGamePartyIdx m rk idx (s.record Δ Q st' r isChall) := by
  unfold SM.GameState.record SM.GameState.safeCh patchGamePartyIdx
  dsimp only []
  congr 1
  funext R
  by_cases hR : R = Q
  · subst hR; simp [Function.update_self]
  · simp [Function.update_of_ne hR]

theorem patchGamePartyIdx_accept {ℓ : ℕ} (m : ℕ) (rk : Ratchet.RootKey)
    (idx idx' : Party → Option ℕ) (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Q : Party) (st' : GhostState Bytes) (pos : SM.Pos)
    (hother : ∀ R ≠ Q, idx' R = idx R) :
    (patchGamePartyIdx m rk idx s).accept Q (patchPartyIdx m rk (idx' Q) st') pos =
      patchGamePartyIdx m rk idx' (s.accept Q st' pos) := by
  unfold SM.GameState.accept SM.GameState.delete patchGamePartyIdx
  dsimp only []
  congr 1
  funext R
  by_cases hR : R = Q
  · subst hR; simp [Function.update_self]
  · simp [Function.update_of_ne hR, hother R hR]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitR_patchGamePartyIdx {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (m : ℕ) (rk : Ratchet.RootKey) (idx : Party → Option ℕ)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (y : Party × CBC.Plain ℓ × Option PQC) :
    (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y).run
        (patchGamePartyIdx m rk idx s) =
      (Prod.map id (patchGamePartyIdx m rk idx)) <$>
        (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y).run s := by
  rcases y with ⟨Q, msg, r_opt⟩
  unfold SM.transmitR configRefuseEarlyBobCorr configR1OnCurve configR1
  simp only [StateT.run_bind, StateT.run_get, pure_bind, patchGamePartyIdx_noBobEpoch0]
  by_cases hok : noBobSendInEpoch0 s Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind]
    have hwin : (patchGamePartyIdx m rk idx s).win = s.win := rfl
    rw [hwin]
    split
    · simp [StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine bind_congr fun cb => ?_
      rw [patchGamePartyIdx_epMgmt]
      cases hep : s.epMgmt 3 qep Q cb.2 with
      | none => simp [StateT.run_pure]
      | some s₁ =>
        dsimp only [Option.map]
        have hsend_eq : ∀ g0, ((sessionSchemeU P ℓ).sendPart.send g0 msg cb.1) =
            ((sessionSchemeU P ℓ).send g0 msg cb.1) := fun _ => rfl
        have hst1 : (patchGamePartyIdx m rk idx s₁).st Q =
            patchPartyIdx m rk (idx Q) (s₁.st Q) := rfl
        have hep1 : (patchGamePartyIdx m rk idx s₁).epoch Q = s₁.epoch Q := rfl
        have hidx1 : (patchGamePartyIdx m rk idx s₁).idx Q = s₁.idx Q := rfl
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        rw [hsend_eq, hsend_eq, hst1, hep1, hidx1]
        simp only [sessionSchemeU, send_patchPartyIdx_eq]
        rw [patchGamePartyIdx_record m rk idx s₁ 3 Q (P.send (s₁.st Q) msg.toList cb.1).1 _ false]
        rfl
  · simp [hok, StateT.run_pure]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challR_patchGamePartyIdx {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (m : ℕ) (rk : Ratchet.RootKey) (idx : Party → Option ℕ)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (y : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC) :
    (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y).run
        (patchGamePartyIdx m rk idx s) =
      (Prod.map id (patchGamePartyIdx m rk idx)) <$>
        (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y).run s := by
  rcases y with ⟨Q, m₀, m₁, r_opt⟩
  unfold SM.challR configRefuseEarlyBobCorr configR1OnCurve configR1
  simp only [StateT.run_bind, StateT.run_get, pure_bind, patchGamePartyIdx_noBobEpoch0]
  by_cases hok : noBobSendInEpoch0 s Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind]
    have hwin : (patchGamePartyIdx m rk idx s).win = s.win := rfl
    rw [hwin]
    split
    · simp [StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine bind_congr fun cb => ?_
      rw [patchGamePartyIdx_epMgmt]
      cases hep : s.epMgmt 3 qep Q cb.2 with
      | none => simp [StateT.run_pure]
      | some s₁ =>
        dsimp only [Option.map]
        have hsafe : (patchGamePartyIdx m rk idx s₁).safeCh 3 Q = s₁.safeCh 3 Q := rfl
        have hep1 : (patchGamePartyIdx m rk idx s₁).epoch Q = s₁.epoch Q := rfl
        have hidx1 : (patchGamePartyIdx m rk idx s₁).idx Q = s₁.idx Q := rfl
        have hb : (patchGamePartyIdx m rk idx s).b = s.b := rfl
        rw [hsafe, hep1, hb]
        split
        · simp [StateT.run_pure]
        · set msg := (SM.Config.h1.challMsg (s₁.epoch Q)).getD (if s.b then m₁ else m₀)
          have hsend_eq : ∀ g0, ((sessionSchemeU P ℓ).sendPart.send g0 msg cb.1) =
              ((sessionSchemeU P ℓ).send g0 msg cb.1) := fun _ => rfl
          have hst1 : (patchGamePartyIdx m rk idx s₁).st Q =
              patchPartyIdx m rk (idx Q) (s₁.st Q) := rfl
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
          rw [hsend_eq, hsend_eq, hst1, hidx1]
          simp only [sessionSchemeU, send_patchPartyIdx_eq]
          rw [patchGamePartyIdx_record m rk idx s₁ 3 Q (P.send (s₁.st Q) msg.toList cb.1).1 _ true]
          rfl
  · simp [hok, StateT.run_pure]


omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2DeliverPost_patchPartyIdx {ℓ : ℕ} (P : Params Bytes PQC) (s : BitVec 256)
    (Q : Party) (c : Bytes) (m : ℕ) (rk : Ratchet.RootKey) (idx : Option ℕ)
    (g₀ : GhostState Bytes) (r : SM.Record (CBC.Plain ℓ) Bytes) :
    hop2DeliverPost (Pt := Pt) P s Q c (patchPartyIdx m rk idx g₀) r =
      hop2DeliverPost (Pt := Pt) P s Q c g₀ r := by
  funext o st2
  unfold hop2DeliverPost
  cases o <;> simp [hop2BadAt_patchPartyIdx]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2InjectPost_patchPartyIdx {ℓ : ℕ} (P : Params Bytes PQC) (qep : ℕ) (s : BitVec 256)
    (Q : Party) (c : Bytes) (m : ℕ) (rk : Ratchet.RootKey) (idx : Option ℕ)
    (g₀ : GhostState Bytes) :
    hop2InjectPost (Pt := Pt) (ℓ := ℓ) P qep s Q c (patchPartyIdx m rk idx g₀) =
      hop2InjectPost (Pt := Pt) (ℓ := ℓ) P qep s Q c g₀ := by
  funext o st2
  unfold hop2InjectPost
  cases o <;> simp [hop2BadAt_patchPartyIdx]

def hop2HybPrf (k : ℕ) (rc : Ratchet.RootKey × BitVec 256) : Hop2Hyb Pt :=
  ⟨k, rc, fun I => evalQuery (Input := Pt) (Tag := BitVec 256) I⟩

def hop2HybPrg (P : Params Bytes PQC) (encPt : Pt → Bytes) (k' : ℕ)
    (u_chall : BitVec 256) : Hop2Hyb Pt :=
  let rc := Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)
  pureStepHyb k' rc ((extractPRF P.C.F encPt).tag rc.1)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem hop2HybPrf_k (k : ℕ) (rc : Ratchet.RootKey × BitVec 256) :
    (hop2HybPrf (Pt := Pt) k rc).k = k := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem hop2HybPrf_chall (k : ℕ) (rc : Ratchet.RootKey × BitVec 256) :
    (hop2HybPrf (Pt := Pt) k rc).chall = rc := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem hop2HybPrf_step (k : ℕ) (rc : Ratchet.RootKey × BitVec 256) (I : Pt) :
    (hop2HybPrf (Pt := Pt) k rc).step I = evalQuery (Input := Pt) (Tag := BitVec 256) I := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem hop2HybPrg_k (P : Params Bytes PQC) (encPt : Pt → Bytes) (k' : ℕ)
    (u_chall : BitVec 256) :
    (hop2HybPrg P encPt k' u_chall).k = k' := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2OffChainOut_some_props {ℓ : ℕ} (P : Params Bytes PQC)
    (g : GhostState Bytes) (msg : SignalMessage) (sc : SenderChain) (rc u : BitVec 256)
    (hs : SpkHop2.SessionSenderInv P g.session)
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ) (upd : Option (Hop2Upd Pt))
    (h : hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u = some ((st', t', i', m'), upd)) :
    upd = some ⟨none, rc, none⟩ ∧
    st'.party = g.party ∧
    SpkHop2.SessionSenderInv P st'.session := by
  unfold hop2OffChainOut at h
  dsimp only [] at h
  cases hcc : rootCreateChain P.C (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
    msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
  | error _ => rw [hcc] at h; simp at h
  | ok p2 =>
    rcases p2 with ⟨rk2, ck2⟩
    rw [hcc] at h
    dsimp only [] at h
    rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc _ with ⟨r_tr, s_out⟩
    rw [htr] at h
    cases r_tr with
    | error _ => simp at h
    | ok m_plain =>
      injection h with hpair
      rcases Prod.mk.inj hpair with ⟨h4, rfl⟩
      rcases Prod.mk.inj h4 with ⟨rfl, _⟩
      have hs_step : SpkHop2.SessionSenderInv P
          { g.session with
            previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
            rootKey := rk2
            receiverChains := RatchetState.evictReceiverChains
              (g.session.receiverChains ++ [⟨msg.senderRatchetKey,
                some ⟨(Ratchet.rootExpand P.C.F (keyToBytes32 u)).2, 0⟩, []⟩])
            senderChain := some ⟨KeyPair.generate P.C rc, ⟨ck2.key, 0⟩⟩ } := by
        refine ⟨hs.1, ?_⟩
        intro sc' hsc'
        simp only [Option.mem_def, Option.some.injEq] at hsc'
        subst hsc'
        exact ⟨rc, rfl⟩
      have hs_out := SpkHop2.tryDecryptFromRecord_preserve_sender P (P.expectedAddrs g.party)
        msg rc _ s_out m_plain hs_step htr
      exact ⟨rfl, rfl, hs_out⟩

omit [SampleableType Pt] in
theorem hop2Recv_run_at_succ {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (k : ℕ) (rc_L : Ratchet.RootKey × BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : SenderChain)
    (hidx : st.2.idx g.party = some (k + 1))
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : g.session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st =
      (fun u => (hop2OffChainOut P ℓ g msg sc rc u, st)) <$>
        evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh (st.2.coins g.party) T) := by
  unfold hop2Recv hop2DH hop2RecvHalf hop2SendHalf hop2OffChainOut
  have hnotle : ¬ (k + 1 ≤ (hop2HybPrf (Pt := Pt) k rc_L).k) := by simp
  simp only [htry, StateT.run_bind, StateT.run_get, pure_bind, hidx, hfind, ↓reduceIte,
    hdec, hT, hsc, hQ0, hnotle, hop2HybPrf_step, stateT_lift_run_hop2,
    map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun u => ?_
  dsimp only [Function.comp_apply]
  cases rootCreateChain P.C (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
    msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
  | error _ => simp [StateT.run_pure]
  | ok p2 =>
    rcases p2 with ⟨rk2, ck2⟩
    simp only [pure_bind]
    rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc _ with ⟨r_tr, s_out⟩
    cases r_tr <;> simp [StateT.run_pure]

omit [SampleableType Pt] in
theorem hop2Recv_run_at_succ_made_none {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : SenderChain)
    (hidx : st.2.idx g.party = some h.k)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : g.session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0)
    (hmade : st.2.made.lookup (h.k, Dh.dh (st.2.coins g.party) T) = none) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st =
      (fun r => (hop2OffChainOut P ℓ g msg sc rc r.1, r.2)) <$>
        (hop2Lazy h.k (Dh.dh (st.2.coins g.party) T)).run st := by
  have hkey : hop2LazyKey P Dh encT decT h g c st =
      some ((h.k, Dh.dh (st.2.coins g.party) T), msg, sc) := by
    unfold hop2LazyKey
    simp [htry, hidx, hfind, hdec, hT, hsc, hQ0, hmade]
  simpa only [withLazy_self] using
    hop2Recv_run_of_hop2LazyKey_some P Dh encT decT h g c rc st.2.lazy st
      (h.k, Dh.dh (st.2.coins g.party) T) msg sc hkey

theorem hop2Recv_run_at_succ_made_some {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (k : ℕ) (u_chall : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : SenderChain)
    (hidx : st.2.idx g.party = some (k + 1))
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : g.session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0)
    (hmade : st.2.made.lookup (k + 1, Dh.dh (st.2.coins g.party) T) =
      some (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st =
      pure (hop2OffChainOut P ℓ g msg sc rc u_chall, st) := by
  have hM := CryptoGames.LibsignalSM.Proofs.Refinement.libX25519Rel_model hX
  have hT0 : T ≠ 0 := fun h0 => hT (Or.inl h0)
  have hencT : encT T = msg.senderRatchetKey := Decidable.of_not_not fun hne => hT (Or.inr hne)
  have hpub : msg.senderRatchetKey.bytes.toList = encPt T := by
    rw [← hencT]
    exact CryptoGames.LibsignalSM.Proofs.Refinement.encT_bytes_toList hX T
  have hrc0 : Dh.dh rc T ≠ 0 := hM.dh_ne_zero rc T hT0
  have hcc2 :=
    CryptoGames.LibsignalSM.Proofs.Refinement.rootCreateChain_generate_honest
      P.C hM (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).1 rc hT0 hpub
  have hnotlt : ¬ (k + 1 + 1 < k + 1) := by omega
  have hne : k + 1 + 1 ≠ k + 1 := by omega
  unfold hop2Recv hop2DH hop2RecvHalf hop2SendHalf hop2OffChainOut hop2HybPrg pureStepHyb
  simp only [htry, StateT.run_bind, StateT.run_get, pure_bind, hidx, hfind, ↓reduceIte,
    hdec, hT, hsc, hQ0, le_refl, hmade, StateT.run_pure, stateT_lift_run_hop2,
    hrc0, hnotlt, hne, rootExpand_extractPRF_eq_rootPRNG_up, hcc2]
  rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
    msg .whisper rc _ with ⟨r_tr, s_out⟩
  cases r_tr <;> rfl


omit [SampleableType Pt] in
theorem hop2Recv_run_of_idx_none {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (hidx : st.2.idx g.party = none) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st =
      pure (((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none)), st) := by
  unfold hop2Recv
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => simp [StateT.run_pure, sessionSchemeU, Params.receive, htry]
  | ok msg => simp [StateT.run_bind, StateT.run_get, hidx, StateT.run_pure]

def hop2NonDhOut (P : Params Bytes PQC) (ℓ : ℕ) (g : GhostState Bytes) (c : Bytes)
    (rc : BitVec 256) : Hop2Out Pt ℓ :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => none
  | .ok msg =>
    if (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone then
      none
    else
      ((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2NonDhOut_snd_none {ℓ : ℕ} (P : Params Bytes PQC) (g : GhostState Bytes)
    (c : Bytes) (rc : BitVec 256) (x :
        (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × Option (Hop2Upd Pt))
    (hx : x ∈ hop2NonDhOut (Pt := Pt) P ℓ g c rc) :
    x.2 = none := by
  simp only [Option.mem_def] at hx
  unfold hop2NonDhOut at hx
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rw [htry] at hx; cases hx
  | ok msg =>
    rw [htry] at hx
    dsimp only [] at hx
    by_cases hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true
    · simp [hfind] at hx
    · simp only [hfind, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hx
      rcases hx with ⟨_, _, rfl⟩
      rfl

omit [SampleableType Pt] in
theorem hop2Recv_run_of_idx_some_non_dh {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (m : ℕ) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st : Hop2State Pt ℓ)
    (hidx : st.2.idx g.party = some m)
    (hnot : ¬ (∃ msg T sc,
      SignalMessage.tryFrom P.codec c = .ok msg ∧
      (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
          true ∧
      decT msg.senderRatchetKey = some T ∧
      ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
      g.session.senderChain = some sc ∧
      Dh.dh (st.2.coins g.party) T ≠ 0)) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st =
      pure (hop2NonDhOut P ℓ g c rc, st) := by
  unfold hop2Recv hop2NonDhOut
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => simp [StateT.run_pure]
  | ok msg =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hidx]
    by_cases hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true
    · simp only [hfind, ↓reduceIte, hop2DH]
      cases hdec : decT msg.senderRatchetKey with
      | none => simp [StateT.run_pure]
      | some T =>
        dsimp only []
        by_cases hT : T = 0 ∨ encT T ≠ msg.senderRatchetKey
        · simp [hT, StateT.run_pure]
        · simp only [hT, ↓reduceIte]
          cases hsc : g.session.senderChain with
          | none => simp [StateT.run_pure]
          | some sc =>
            dsimp only []
            by_cases hQ0 : Dh.dh (st.2.coins g.party) T = 0
            · unfold hop2RecvHalf
              simp [hQ0, StateT.run_pure, pure_bind]
            · exfalso
              exact hnot ⟨msg, T, sc, htry, hfind, hdec, hT, hsc, hQ0⟩
    · simp [hfind, StateT.run_pure]

def IsDeliverOrInjectPost {ℓ : ℕ} (P : Params Bytes PQC) (qep : ℕ) (s : BitVec 256)
    (Q : Party) (c : Bytes) (g₀ : GhostState Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ →
        Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ) : Prop :=
  (∃ r, post = hop2DeliverPost P s Q c g₀ r) ∨ post = hop2InjectPost P qep s Q c g₀

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem IsDeliverOrInjectPost.isHop2Post {ℓ : ℕ} {P : Params Bytes PQC} {qep : ℕ} {s : BitVec 256}
    {Q : Party} {c : Bytes} {g₀ : GhostState Bytes}
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (h : IsDeliverOrInjectPost (Pt := Pt) P qep s Q c g₀ post) :
    IsHop2Post P s Q c g₀ post := by
  rcases h with ⟨r, rfl⟩ | rfl
  · exact hop2DeliverPost_isHop2Post P s Q c g₀ r
  · exact hop2InjectPost_isHop2Post P qep s Q c g₀

omit [SampleableType Pt] in
theorem IsDeliverOrInjectPost.preserves_hop2GameInv {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt}
    {qep : ℕ} {s : BitVec 256} {h : Hop2Hyb Pt}
    {Q : Party} {c : Bytes} {rc : BitVec 256} {st : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)}
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverOrInjectPost (Pt := Pt) P qep s Q c (st.1.st Q) post)
    (hinv : Hop2GameInv P decT encT st)
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st)).run tbl)) :
    Hop2GameInv P decT encT (post z.1.1 z.1.2).2 := by
  have hrec := hop2Recv_support_hop2GameInv P Dh encT decT h Q c rc st tbl hinv z hz
  rcases hpost with ⟨r, rfl⟩ | rfl
  · exact hop2DeliverPost_preserves_hop2GameInv P decT encT s Q c r st z.1.2 z.1.1 hinv
      hrec.1 hrec.2.2.1 hrec.2.2.2.1 hrec.2.2.2.2.2
  · exact hop2InjectPost_preserves_hop2GameInv P decT encT qep s Q c st z.1.2 z.1.1 hinv
      hrec.1 hrec.2.2.1 hrec.2.2.2.1 hrec.2.2.2.2.2

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem IsDeliverOrInjectPost.patchGamePartyIdx_step {ℓ : ℕ} {P : Params Bytes PQC}
    {qep : ℕ} {s : BitVec 256} {Q : Party} {c : Bytes} {g₀ : GhostState Bytes}
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverOrInjectPost (Pt := Pt) P qep s Q c g₀ post)
    (m : ℕ) (rk : Ratchet.RootKey)
    (st_L st_R : Hop2State Pt ℓ)
    (hst1 : st_L.1 = patchGamePartyIdx m rk st_R.2.idx st_R.1)
    (hbad : st_L.2.bad = st_R.2.bad)
    (o_L o_R : Hop2Out Pt ℓ)
    (ho : o_L.map (·.1) = o_R.map (fun x =>
      (patchPartyIdx m rk ((hop2Commit st_R.2 Q x.2).idx Q) x.1.1, x.1.2)))
    (hother : ∀ x ∈ o_R, ∀ R ≠ Q, (hop2Commit st_R.2 Q x.2).idx R = st_R.2.idx R) :
    (post o_L st_L).1 = (post o_R st_R).1 ∧
    (post o_L st_L).2.1 = patchGamePartyIdx m rk (post o_R st_R).2.2.idx (post o_R st_R).2.1 ∧
    (post o_L st_L).2.2.bad = (post o_R st_R).2.2.bad ∧
    (post o_L st_L).2.2.lazy = st_L.2.lazy ∧
    (post o_R st_R).2.2.lazy = st_R.2.lazy ∧
    ((o_L = none ∧ o_R = none ∧
      (post o_L st_L).2.2 = st_L.2 ∧ (post o_R st_R).2.2 = st_R.2) ∨
     (∃ st_L' st_R' t' i' m' u_L u_R,
      o_L = some ((st_L', t', i', m'), u_L) ∧
      o_R = some ((st_R', t', i', m'), u_R) ∧
      (((post o_L st_L).2.2.idx = st_L.2.idx ∧
        (post o_L st_L).2.2.coins = st_L.2.coins ∧
        (post o_L st_L).2.2.made = st_L.2.made ∧
        (post o_R st_R).2.2.idx = st_R.2.idx ∧
        (post o_R st_R).2.2.coins = st_R.2.coins ∧
        (post o_R st_R).2.2.made = st_R.2.made) ∨
       ((post o_L st_L).2.2.idx = (hop2Commit st_L.2 Q u_L).idx ∧
        (post o_L st_L).2.2.coins = (hop2Commit st_L.2 Q u_L).coins ∧
        (post o_L st_L).2.2.made = (hop2Commit st_L.2 Q u_L).made ∧
        (post o_R st_R).2.2.idx = (hop2Commit st_R.2 Q u_R).idx ∧
        (post o_R st_R).2.2.coins = (hop2Commit st_R.2 Q u_R).coins ∧
        (post o_R st_R).2.2.made = (hop2Commit st_R.2 Q u_R).made)))) := by
  cases o_R with
  | none =>
    simp only [Option.map_none, Option.map_eq_none_iff] at ho
    subst ho
    rcases hpost with ⟨r, rfl⟩ | rfl <;>
      exact ⟨rfl, hst1, hbad, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  | some x_R =>
    rcases x_R with ⟨⟨st_R', t', i', m'⟩, u_R⟩
    simp only [Option.map_some, Option.map_eq_some_iff] at ho
    rcases ho with ⟨⟨⟨st_L', t_L, i_L, m_L⟩, u_L⟩, rfl, hpair⟩
    rcases Prod.mk.inj hpair with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨ht, hrest2⟩
    rcases Prod.mk.inj hrest2 with ⟨hi, hm⟩
    subst t_L; subst i_L; subst m_L
    have hcomm_L : ∀ (aux : Hop2Aux Pt) b_new,
        (hop2Commit { aux with bad := b_new } Q u_L).idx = (hop2Commit aux Q u_L).idx ∧
        (hop2Commit { aux with bad := b_new } Q u_L).coins = (hop2Commit aux Q u_L).coins ∧
        (hop2Commit { aux with bad := b_new } Q u_L).made = (hop2Commit aux Q u_L).made ∧
        (hop2Commit { aux with bad := b_new } Q u_L).lazy = aux.lazy ∧
        (hop2Commit { aux with bad := b_new } Q u_L).bad = b_new := by
      intro aux b_new; cases u_L <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hcomm_R : ∀ (aux : Hop2Aux Pt) b_new,
        (hop2Commit { aux with bad := b_new } Q u_R).idx = (hop2Commit aux Q u_R).idx ∧
        (hop2Commit { aux with bad := b_new } Q u_R).coins = (hop2Commit aux Q u_R).coins ∧
        (hop2Commit { aux with bad := b_new } Q u_R).made = (hop2Commit aux Q u_R).made ∧
        (hop2Commit { aux with bad := b_new } Q u_R).lazy = aux.lazy ∧
        (hop2Commit { aux with bad := b_new } Q u_R).bad = b_new := by
      intro aux b_new; cases u_R <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hlazy_L : (hop2Commit st_L.2 Q u_L).lazy = st_L.2.lazy := by cases u_L <;> rfl
    have hlazy_R : (hop2Commit st_R.2 Q u_R).lazy = st_R.2.lazy := by cases u_R <;> rfl
    have hoth : ∀ R ≠ Q, (hop2Commit st_R.2 Q u_R).idx R = st_R.2.idx R :=
      hother ((st_R', t', i', m'), u_R) (by simp)
    rcases hpost with ⟨r, rfl⟩ | rfl
    · dsimp only [hop2DeliverPost]
      refine ⟨by rw [hst1]; rfl, ?_, by rw [hbad], hlazy_L, hlazy_R,
        Or.inr ⟨_, st_R', t', i', m', u_L, u_R, rfl, rfl,
          Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩
      rw [hst1]
      exact patchGamePartyIdx_accept m rk st_R.2.idx (hop2Commit st_R.2 Q u_R).idx st_R.1 Q st_R'
          r.pos hoth
    · dsimp only [hop2InjectPost]
      have htriv_eq : st_L.1.trivial 3 ⟨Q.other, t', i'⟩ = st_R.1.trivial 3 ⟨Q.other, t', i'⟩ := by
        rw [hst1]; rfl
      rw [htriv_eq]
      split_ifs with hqep htriv
      · exact ⟨rfl, hst1, by rw [hbad], rfl, rfl,
          Or.inr ⟨_, st_R', t', i', m', u_L, u_R, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩
      · have hL := hcomm_L st_L.2 (st_L.2.bad || hop2BadAt P s g₀ c)
        have hR := hcomm_R st_R.2 (st_R.2.bad || hop2BadAt P s g₀ c)
        refine ⟨rfl, ?_, by rw [hL.2.2.2.2, hR.2.2.2.2, hbad], hL.2.2.2.1, hR.2.2.2.1,
          Or.inr ⟨_, st_R', t', i', m', u_L, u_R, rfl, rfl,
            Or.inr ⟨hL.1, hL.2.1, hL.2.2.1, hR.1, hR.2.1, hR.2.2.1⟩⟩⟩
        rw [hst1, hR.1]
        exact patchGamePartyIdx_accept m rk st_R.2.idx (hop2Commit st_R.2 Q u_R).idx st_R.1 Q st_R'
            ⟨Q.other, t', i'⟩ hoth
      · refine ⟨rfl, ?_, by rw [hbad], rfl, rfl,
          Or.inr ⟨_, st_R', t', i', m', u_L, u_R, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩
        rw [hst1]; rfl

end Hop2Coupling
end CryptoVerification.E2E.SpkHop1
