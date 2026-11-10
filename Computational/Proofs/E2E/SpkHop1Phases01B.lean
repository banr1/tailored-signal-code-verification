/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1Phases01

@[expose] public section

/-!
# Initial Coupling Lemmas for `h_init`

Couples the leaked-SPK game `runSpkTab` in worlds `s` and `x` with the `ck0`-independent reference
game `runSpkRef` up to the bad-event reduction `runSpkBad`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CryptoGames.HMAC CryptoGames.MACScheme CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq
open CryptoGames.CKA (DHFun)

section HInit

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

open CryptoGames.LibsignalSM.Proofs.Refinement

def badSpkCorrA {ℓ : ℕ} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (s : GameSt Bytes ℓ) (Q : Party) : Bool :=
  !s.win && (Q == .A) && decide (0 ∈ (s.st .A).chainEpochs) &&
    (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := CBC.Plain ℓ) decT encT).corrOK s .A

def runSpkTab {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256))
    (post : β → GameSt Bytes ℓ → Bool) : ProbComp Bool := do
  let (b', (fin, _)) ← (simulateQ (spkStepImpl P ℓ Dh encT decT qep s) oa).run (st, L)
  return post b' fin

abbrev SpkRefSt (Pt : Type) (ℓ : ℕ) :=
  SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × List (Pt × BitVec 256) × Bool

def liftSpkRef {ℓ : ℕ} {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α) :
    StateT (SpkRefSt Pt ℓ) ProbComp α :=
  StateT.mk fun ⟨st, L, b⟩ => do
    let (a, st') ← m.run st
    return (a, (st', L, b))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem liftSpkRef_run {ℓ : ℕ} {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (L : List (Pt × BitVec 256)) (b : Bool) :
    (liftSpkRef m).run (st, L, b) = (m.run st >>= fun r => pure (r.1, (r.2, L, b))) :=
  rfl

def deliverSpkRef (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ)))
      (StateT (SpkRefSt Pt ℓ) ProbComp) :=
  fun ⟨Q, c⟩ => StateT.mk fun ⟨st, L, b⟩ => do
    if st.win then return (none, (st, L, b))
    match st.inTransit Q.other c with
    | none => return (none, (st, L, b))
    | some r =>
      let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let (res, L') ← stepReceiveRef P ℓ Dh encT decT s st Q c rc L
      match res with
      | none => return (some .rejected, (st, L', b))
      | some (st', t', i', m') =>
        return (some (.accepted t' i' (if st.chall.contains r.pos then none else some m')),
          (st.accept Q st' r.pos, L', b))

def injectSpkRef (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ)))
      (StateT (SpkRefSt Pt ℓ) ProbComp) :=
  fun ⟨Q, c⟩ => StateT.mk fun ⟨st, L, b⟩ => do
    if st.win || (st.inTransit Q.other c).isSome || !(st.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c) then
      return (none, (st, L, b))
    let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let (res, L') ← stepReceiveRef P ℓ Dh encT decT s st Q c rc L
    match res with
    | none => return (some .rejected, (st, L', b))
    | some (st', t', i', m') =>
      if qep + 1 < t' then return (some .rejected, (st, L', b))
      let pos : SM.Pos := ⟨Q.other, t', i'⟩
      if st.trivial 3 pos then
        return (some (.accepted t' i' (some m')), (st.accept Q st' pos, L', b))
      else
        return (some .rejected, ({ st with win := true }, L', b))

def corrSpkRef (ℓ : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (Party →ₒ Option (GhostState Bytes)) (StateT (SpkRefSt Pt ℓ) ProbComp) :=
  fun Q => StateT.mk fun ⟨st, L, b⟩ => do
    let b' := b || badSpkCorrA decT encT st Q
    let (res, st') ← (SM.corrR (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg :=
        CBC.Plain ℓ) decT encT) Q).run st
    return (res, (st', L, b'))

def spkRefImpl (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) :
    QueryImpl (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
      (StateT (SpkRefSt Pt ℓ) ProbComp)
  | .inl u => StateT.lift (query (spec := unifSpec) u)
  | .inr (.inl (.inl (.inl (.inl x)))) =>
    liftSpkRef (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inl (.inr x)))) =>
    liftSpkRef (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inr x))) =>
    deliverSpkRef P ℓ Dh encT decT s x
  | .inr (.inl (.inr x)) =>
    injectSpkRef P ℓ Dh encT decT qep s x
  | .inr (.inr x) =>
    corrSpkRef ℓ decT encT x

def runSpkRef {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (post : β → GameSt Bytes ℓ → Bool) : ProbComp Bool := do
  let (b', (fin, _, abort')) ← (simulateQ (spkRefImpl P ℓ Dh encT decT qep s) oa).run (sRef, L,
      abort)
  return (abort' || post b' fin)

omit [SampleableType Pt] in
@[simp] theorem runSpkTab_pure {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (a : β) (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256))
    (post : β → GameSt Bytes ℓ → Bool) :
    runSpkTab P Dh encT decT qep s (pure a) st L post = pure (post a st) := by
  simp [runSpkTab, StateT.run_pure]

omit [SampleableType Pt] in
theorem runSpkTab_bind_query {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (k : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Range t →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256))
    (post : β → GameSt Bytes ℓ → Bool) :
    runSpkTab P Dh encT decT qep s
      (liftM (OracleSpec.query (spec := unifSpec +
          SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) t) >>= k)
      st L post =
      ((spkStepImpl P ℓ Dh encT decT qep s t).run (st, L) >>= fun r =>
        runSpkTab P Dh encT decT qep s (k r.1) r.2.1 r.2.2 post) := by
  simp [runSpkTab, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

omit [SampleableType Pt] in
@[simp] theorem runSpkRef_pure {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (a : β) (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (post : β → GameSt Bytes ℓ → Bool) :
    runSpkRef P Dh encT decT qep s (pure a) sRef L abort post = pure (abort || post a sRef) := by
  simp [runSpkRef, StateT.run_pure]

omit [SampleableType Pt] in
theorem runSpkRef_bind_query {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (k : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Range t →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (post : β → GameSt Bytes ℓ → Bool) :
    runSpkRef P Dh encT decT qep s
      (liftM (OracleSpec.query (spec := unifSpec +
          SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) t) >>= k)
      sRef L abort post =
      ((spkRefImpl P ℓ Dh encT decT qep s t).run (sRef, L, abort) >>= fun r =>
        runSpkRef P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post) := by
  simp [runSpkRef, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

omit [SampleableType Pt] in
theorem spkRefImpl_support_abort_true {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) :
    ∀ r ∈ support ((spkRefImpl P ℓ Dh encT decT qep s t).run (st, L, true)),
      r.2.2.2 = true := by
  intro r hr
  rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
  · dsimp only [spkRefImpl] at hr
    rw [stateT_lift_run_any] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkRefImpl] at hr
    rw [liftSpkRef_run] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkRefImpl] at hr
    rw [liftSpkRef_run] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkRefImpl, deliverSpkRef] at hr
    rw [StateT.run_mk] at hr
    dsimp only [] at hr
    split at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
    · split at hr
      · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
      · simp only [support_bind, Set.mem_iUnion, exists_prop] at hr
        rcases hr with ⟨rc, _, res, _, hr⟩
        rcases res with ⟨o, L'⟩
        cases o with
        | none => simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
  · dsimp only [spkRefImpl, injectSpkRef] at hr
    rw [StateT.run_mk] at hr
    dsimp only [] at hr
    split at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
    · simp only [support_bind, Set.mem_iUnion, exists_prop] at hr
      rcases hr with ⟨rc, _, res, _, hr⟩
      rcases res with ⟨o, L'⟩
      cases o with
      | none => simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        dsimp only [] at hr
        split at hr
        · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
        · split at hr <;> (simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl)
  · dsimp only [spkRefImpl, corrSpkRef] at hr
    rw [StateT.run_mk] at hr
    simp only [Bool.true_or, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl

omit [SampleableType Pt] in
theorem evalDist_runSpkRef_true {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256))
    (post : β → GameSt Bytes ℓ → Bool) :
    𝒟[runSpkRef P Dh encT decT qep s oa sRef L true post] {true} = 1 := by
  induction oa using OracleComp.inductionOn generalizing sRef L with
  | pure a => simp [runSpkRef_pure]
  | query_bind t k ih =>
    rw [runSpkRef_bind_query]
    exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr => by
      rw [spkRefImpl_support_abort_true P Dh encT decT qep s t sRef L r hr]
      exact ih r.1 r.2.1 r.2.2.1

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitR_patchGameSpk {ℓ : ℕ}
    (P : Params Bytes PQC) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qep : ℕ) (z ck0 : BitVec 256) (spk₀ : PublicKey)
    (sRef : GameSt Bytes ℓ) (x : Party × CBC.Plain ℓ × Option PQC)
    (hinv : SpkRefInv P spk₀ sRef) :
    ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x).run
        (patchGameSpk P.C z ck0 sRef)) =
      Prod.map id (patchGameSpk P.C z ck0) <$>
        ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr (Pt :=
            Pt) decT encT) x).run sRef) := by
  rcases x with ⟨Q, m, r⟩
  unfold SM.transmitR SM.transmitImpl
  have hsendOK : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK (patchGameSpk P.C z ck0 sRef) Q =
      noBobSendInEpoch0 sRef Q := rfl
  have hsendOK0 : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK sRef Q = noBobSendInEpoch0 sRef Q := rfl
  have hwin : (patchGameSpk P.C z ck0 sRef).win = sRef.win := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hsendOK0]
  by_cases hs : (!noBobSendInEpoch0 sRef Q) = true
  · simp [hs, StateT.run_pure]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind, hwin]
    have hsend : noBobSendInEpoch0 sRef Q = true := by simpa using hs
    by_cases hw : sRef.win = true
    · simp [hw, StateT.run_pure]
    · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
      have hginv := gameInv_of_spkRefInv_win_false hinv hwF
      simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, patchGameSpk_epMgmt, map_bind]
      refine bind_congr fun cb => ?_
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none => simp [StateT.run_pure]
      | some s₁ =>
        dsimp only [Option.map]
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
          Prod.map_apply, id_eq]
        obtain ⟨hc1, hc2, _⟩ :=
          send_record_patchGameSpk P ℓ z ck0 spk₀ sRef s₁ qep Q m cb.1 cb.2 false hginv hsend hep
        congr 1
        exact Prod.ext (congrArg some hc1) hc2

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitR_support_spkRefInv {ℓ : ℕ}
    (P : Params Bytes PQC) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qep : ℕ) (spk₀ : PublicKey)
    (sRef : GameSt Bytes ℓ) (x : Party × CBC.Plain ℓ × Option PQC)
    (hinv : SpkRefInv P spk₀ sRef) :
    ∀ us ∈ support ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr (Pt :=
        Pt) decT encT) x).run sRef),
      SpkRefInv P spk₀ us.2 := by
  rcases x with ⟨Q, m, r⟩
  intro us hus
  unfold SM.transmitR SM.transmitImpl at hus
  have hsendOK0 : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK sRef Q = noBobSendInEpoch0 sRef Q := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK0] at hus
  by_cases hs : (!noBobSendInEpoch0 sRef Q) = true
  · simp only [hs, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
    subst hus; exact hinv
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hus
    have hsend : noBobSendInEpoch0 sRef Q = true := by simpa using hs
    by_cases hw : sRef.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
      subst hus; exact hinv
    · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
      have hginv := gameInv_of_spkRefInv_win_false hinv hwF
      simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hus
      rcases hus with ⟨cb, _, hus⟩
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none =>
        rw [hep] at hus
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
        subst hus; exact hinv
      | some s₁ =>
        rw [hep] at hus
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hus
        subst hus
        obtain ⟨_, _, hginv_next⟩ :=
          send_record_patchGameSpk P ℓ 0 0 spk₀ sRef s₁ qep Q m cb.1 cb.2 false hginv hsend hep
        obtain ⟨_, _, hst, _, _, _, _⟩ := epMgmt_epoch_pos sRef 3 qep Q cb.2 s₁ hsend hep
        refine spkRefInv_of_gameInv hginv_next ?_
        dsimp only [GameState.record]
        cases Q with
        | A =>
          rw [Function.update_of_ne (by decide), hst]
          exact hinv.2
        | B =>
          rw [Function.update_self]
          exact ((send_preserve_fields P (s₁.st .B) m.toList cb.1).1.trans
            (by rw [hst]; exact hinv.2))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challR_patchGameSpk {ℓ : ℕ}
    (P : Params Bytes PQC) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qep : ℕ) (z ck0 : BitVec 256) (spk₀ : PublicKey)
    (sRef : GameSt Bytes ℓ) (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (hinv : SpkRefInv P spk₀ sRef) :
    ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x).run
        (patchGameSpk P.C z ck0 sRef)) =
      Prod.map id (patchGameSpk P.C z ck0) <$>
        ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr (Pt := Pt) decT encT) x).run sRef) := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  unfold SM.challR SM.challImpl
  have hsendOK : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK (patchGameSpk P.C z ck0 sRef) Q =
      noBobSendInEpoch0 sRef Q := rfl
  have hsendOK0 : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK sRef Q = noBobSendInEpoch0 sRef Q := rfl
  have hwin : (patchGameSpk P.C z ck0 sRef).win = sRef.win := rfl
  have hb : (patchGameSpk P.C z ck0 sRef).b = sRef.b := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hsendOK0]
  by_cases hs : (!noBobSendInEpoch0 sRef Q) = true
  · simp [hs, StateT.run_pure]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
      hwin, hb]
    have hsend : noBobSendInEpoch0 sRef Q = true := by simpa using hs
    by_cases hw : sRef.win = true
    · simp [hw, StateT.run_pure]
    · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
      have hginv := gameInv_of_spkRefInv_win_false hinv hwF
      simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, patchGameSpk_epMgmt, map_bind]
      refine bind_congr fun cb => ?_
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none => simp [StateT.run_pure]
      | some s₁ =>
        have hsafe : (patchGameSpk P.C z ck0 s₁).safeCh 3 Q = s₁.safeCh 3 Q := rfl
        have hep1 : (patchGameSpk P.C z ck0 s₁).epoch Q = s₁.epoch Q := rfl
        dsimp only [Option.map]
        simp only [hsafe, hep1]
        by_cases hch : (!s₁.safeCh 3 Q || !(configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg :=
            CBC.Plain ℓ) decT encT).base.challAllowedIn (s₁.epoch Q)) = true
        · simp [hch, StateT.run_pure]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, map_pure, Prod.map_apply, id_eq]
          let m := ((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg :=
              CBC.Plain ℓ) decT encT).base.challMsg (s₁.epoch Q)).getD
            (if sRef.b then m₁ else m₀)
          obtain ⟨hc1, hc2, _⟩ :=
            send_record_patchGameSpk P ℓ z ck0 spk₀ sRef s₁ qep Q m cb.1 cb.2 true hginv hsend hep
          rw [hep1] at hc2
          congr 1
          exact Prod.ext (congrArg some hc1) hc2

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challR_support_spkRefInv {ℓ : ℕ}
    (P : Params Bytes PQC) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qep : ℕ) (spk₀ : PublicKey)
    (sRef : GameSt Bytes ℓ) (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (hinv : SpkRefInv P spk₀ sRef) :
    ∀ us ∈ support ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr (Pt :=
        Pt) decT encT) x).run sRef),
      SpkRefInv P spk₀ us.2 := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  intro us hus
  unfold SM.challR SM.challImpl at hus
  have hsendOK0 : (configRefuseEarlyBobCorr (Pt := Pt) decT encT).sendOK sRef Q = noBobSendInEpoch0 sRef Q := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK0] at hus
  by_cases hs : (!noBobSendInEpoch0 sRef Q) = true
  · simp only [hs, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
    subst hus; exact hinv
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hus
    have hsend : noBobSendInEpoch0 sRef Q = true := by simpa using hs
    by_cases hw : sRef.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
      subst hus; exact hinv
    · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
      have hginv := gameInv_of_spkRefInv_win_false hinv hwF
      simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hus
      rcases hus with ⟨cb, _, hus⟩
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none =>
        rw [hep] at hus
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
        subst hus; exact hinv
      | some s₁ =>
        rw [hep] at hus
        dsimp only [] at hus
        by_cases hch : (!s₁.safeCh 3 Q || !(configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg :=
            CBC.Plain ℓ) decT encT).base.challAllowedIn (s₁.epoch Q)) = true
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
          subst hus; exact hinv
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hus
          subst hus
          let m := ((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg :=
              CBC.Plain ℓ) decT encT).base.challMsg (s₁.epoch Q)).getD
            (if sRef.b then m₁ else m₀)
          obtain ⟨_, _, hginv_next⟩ :=
            send_record_patchGameSpk P ℓ 0 0 spk₀ sRef s₁ qep Q m cb.1 cb.2 true hginv hsend hep
          obtain ⟨_, _, hst, _, _, _, _⟩ := epMgmt_epoch_pos sRef 3 qep Q cb.2 s₁ hsend hep
          refine spkRefInv_of_gameInv hginv_next ?_
          dsimp only [GameState.record]
          cases Q with
          | A =>
            rw [Function.update_of_ne (by decide), hst]
            exact hinv.2
          | B =>
            rw [Function.update_self]
            exact ((send_preserve_fields P (s₁.st .B) m.toList cb.1).1.trans
              (by rw [hst]; exact hinv.2))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrR_patchGameSpk_of_badSpkCorrA_false {ℓ : ℕ}
    (P : Params Bytes PQC) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (z ck0 : BitVec 256) (spk₀ : PublicKey)
    (sRef : GameSt Bytes ℓ) (Q : Party)
    (hinv : SpkRefInv P spk₀ sRef)
    (hbad : badSpkCorrA decT encT sRef Q = false) :
    ((SM.corrR (configRefuseEarlyBobCorr (Pt := Pt) decT encT) Q).run (patchGameSpk P.C z ck0 sRef)) =
      Prod.map id (patchGameSpk P.C z ck0) <$>
        ((SM.corrR (configRefuseEarlyBobCorr (Pt := Pt) decT encT) Q).run sRef) := by
  by_cases hw : sRef.win = true
  · unfold SM.corrR
    have hwin : (patchGameSpk P.C z ck0 sRef).win = true := hw
    simp [StateT.run_bind, StateT.run_get, pure_bind, hw, hwin, StateT.run_pure]
  · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
    have hginv := gameInv_of_spkRefInv_win_false hinv hwF
    refine corrR_patchGameSpk P ℓ decT encT z ck0 spk₀ sRef Q hginv ?_
    intro hQ hcorrOK
    subst hQ
    unfold badSpkCorrA at hbad
    simp only [hwF, Bool.not_false, beq_self_eq_true, Bool.and_self, hcorrOK, Bool.and_true,
      Bool.true_and, decide_eq_false_iff_not] at hbad
    exact hbad

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrR_support_spkRefInv {ℓ : ℕ}
    (P : Params Bytes PQC) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (spk₀ : PublicKey) (sRef : GameSt Bytes ℓ) (Q : Party)
    (hinv : SpkRefInv P spk₀ sRef) :
    ∀ us ∈ support ((SM.corrR (configRefuseEarlyBobCorr (Pt := Pt) decT encT) Q).run sRef),
      SpkRefInv P spk₀ us.2 := by
  intro us hus
  unfold SM.corrR at hus
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hus
  split at hus
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
    subst hus; exact hinv
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hus
    subst hus; exact hinv

omit [SampleableType Pt] in
theorem deliverSpkStep_patchGameSpk_of_not_spk {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s z ck0 : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes)
    (L : List (Pt × BitVec 256)) (abort : Bool)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (hnspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = false)
    (hnspk_z : isAliceSpkQuery P (KeyPair.generate P.C z).publicKey Q (sRef.st .A) c = false) :
    (deliverSpkStep P ℓ Dh encT decT s (Q, c)).run (patchGameSpk P.C z ck0 sRef, L) =
      (fun r => (r.1, (patchGameSpk P.C z ck0 r.2.1, r.2.2.1))) <$>
        (deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, abort) := by
  unfold deliverSpkStep deliverSpkRef
  rw [StateT.run_mk, StateT.run_mk]
  dsimp only []
  have hwin : (patchGameSpk P.C z ck0 sRef).win = sRef.win := rfl
  have htr : (patchGameSpk P.C z ck0 sRef).inTransit Q.other c = sRef.inTransit Q.other c := rfl
  have hch : (patchGameSpk P.C z ck0 sRef).chall = sRef.chall := rfl
  rw [hwin, htr, hch]
  by_cases hw : sRef.win = true
  · simp [hw]
  · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
    simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases sRef.inTransit Q.other c with
    | none => simp
    | some r =>
      simp only [map_bind]
      refine bind_congr fun rc => ?_
      rw [stepReceiveSpk_patchGameSpk_of_not_spk P Dh encT decT s z ck0 sRef Q c rc L hinv hwF
          hnspk_s hnspk_z]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun res => ?_
      rcases res with ⟨o, L'⟩
      cases o with
      | none => simp
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        simp only [Option.map, pure_bind, Function.comp_apply]
        rw [← patchGameSpk_accept P.C z ck0 sRef Q st' r.pos]
        rfl

omit [SampleableType Pt] in
theorem deliverSpkRef_support_spkRefInv {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes)
    (L : List (Pt × BitVec 256)) (abort : Bool)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef) :
    ∀ r ∈ support ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, abort)),
      SpkRefInv P (KeyPair.generate P.C s).publicKey r.2.1 ∧ r.2.2.2 = abort := by
  intro r hr
  unfold deliverSpkRef at hr
  rw [StateT.run_mk] at hr
  dsimp only [] at hr
  by_cases hw : sRef.win = true
  · simp only [hw, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact ⟨hinv, rfl⟩
  · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
    have hginv := gameInv_of_spkRefInv_win_false hinv hwF
    simp only [hw, Bool.false_eq_true, ↓reduceIte] at hr
    cases hin : sRef.inTransit Q.other c with
    | none =>
      rw [hin] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨hinv, rfl⟩
    | some rec' =>
      rw [hin] at hr
      simp only [support_bind, Set.mem_iUnion, exists_prop] at hr
      rcases hr with ⟨rc, _, res, hres, hr⟩
      rcases res with ⟨o, L'⟩
      cases o with
      | none =>
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨hinv, rfl⟩
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        have hmem : rec' ∈ sRef.trans := List.mem_of_find?_eq_some hin
        have hep_pos : 0 < rec'.pos.epoch := hginv.2.2.2.2 rec' hmem
        have hstep := stepReceiveRef_support_spkRefInv P Dh encT decT s sRef Q c rc L hinv hwF
          (some (st', t', i', m'), L') hres st' t' i' m' rfl
        exact ⟨hstep.2 rec'.pos (fun _ => hep_pos), rfl⟩

omit [SampleableType Pt] in
theorem injectSpkStep_patchGameSpk_of_not_spk {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s z ck0 : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes)
    (L : List (Pt × BitVec 256)) (abort : Bool)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (hnspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = false)
    (hnspk_z : isAliceSpkQuery P (KeyPair.generate P.C z).publicKey Q (sRef.st .A) c = false) :
    (injectSpkStep P ℓ Dh encT decT qep s (Q, c)).run (patchGameSpk P.C z ck0 sRef, L) =
      (fun r => (r.1, (patchGameSpk P.C z ck0 r.2.1, r.2.2.1))) <$>
        (injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, abort) := by
  unfold injectSpkStep injectSpkRef
  rw [StateT.run_mk, StateT.run_mk]
  dsimp only []
  have hguard : ((patchGameSpk P.C z ck0 sRef).win ||
      ((patchGameSpk P.C z ck0 sRef).inTransit Q.other c).isSome ||
      !((patchGameSpk P.C z ck0 sRef).safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
    (sRef.win || (sRef.inTransit Q.other c).isSome || !(sRef.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := rfl
  have htriv : ∀ pos, (patchGameSpk P.C z ck0 sRef).trivial 3 pos = sRef.trivial 3 pos :=
    fun _ => rfl
  rw [hguard]
  by_cases hg : (sRef.win || (sRef.inTransit Q.other c).isSome || !(sRef.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · simp [hg]
  · have hwF : sRef.win = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
      exact hg.1.1.1
    simp only [hg, Bool.false_eq_true, ↓reduceIte, map_bind]
    refine bind_congr fun rc => ?_
    rw [stepReceiveSpk_patchGameSpk_of_not_spk P Dh encT decT s z ck0 sRef Q c rc L hinv hwF hnspk_s
        hnspk_z]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun res => ?_
    rcases res with ⟨o, L'⟩
    cases o with
    | none => simp
    | some val =>
      rcases val with ⟨st', t', i', m'⟩
      dsimp only [Option.map]
      by_cases hcap : qep + 1 < t'
      · simp [hcap]
      · simp only [hcap, ↓reduceIte, htriv]
        by_cases htr : sRef.trivial 3 ⟨Q.other, t', i'⟩ = true
        · simp only [htr, ↓reduceIte, pure_bind, Function.comp_apply]
          rw [← patchGameSpk_accept P.C z ck0 sRef Q st' ⟨Q.other, t', i'⟩]
          rfl
        · simp [htr]
          rfl

omit [SampleableType Pt] in
theorem injectSpkRef_support_spkRefInv {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes)
    (L : List (Pt × BitVec 256)) (abort : Bool)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef) :
    ∀ r ∈ support ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, abort)),
      SpkRefInv P (KeyPair.generate P.C s).publicKey r.2.1 ∧ r.2.2.2 = abort := by
  intro r hr
  unfold injectSpkRef at hr
  rw [StateT.run_mk] at hr
  dsimp only [] at hr
  by_cases hg : (sRef.win || (sRef.inTransit Q.other c).isSome || !(sRef.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · simp only [hg, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact ⟨hinv, rfl⟩
  · have hwF : sRef.win = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
      exact hg.1.1.1
    simp only [hg, Bool.false_eq_true, ↓reduceIte, support_bind, Set.mem_iUnion, exists_prop] at hr
    rcases hr with ⟨rc, _, res, hres, hr⟩
    rcases res with ⟨o, L'⟩
    cases o with
    | none =>
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨hinv, rfl⟩
    | some val =>
      rcases val with ⟨st', t', i', m'⟩
      dsimp only [] at hr
      have hstep := stepReceiveRef_support_spkRefInv P Dh encT decT s sRef Q c rc L hinv hwF
        (some (st', t', i', m'), L') hres st' t' i' m' rfl
      by_cases hcap : qep + 1 < t'
      · simp only [hcap, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨hinv, rfl⟩
      · simp only [hcap, ↓reduceIte] at hr
        by_cases htr : sRef.trivial 3 ⟨Q.other, t', i'⟩ = true
        · simp only [htr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          exact ⟨hstep.2 ⟨Q.other, t', i'⟩ (fun _ => hstep.1), rfl⟩
        · simp only [htr, Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          exact ⟨spkRefInv_with_win_true hinv, rfl⟩

theorem transmitR_support_transShort {ℓ : ℕ}
    (P : Params Bytes PQC) (hrt : CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp P ℓ)
    (cfg : SM.ConfigR (GhostState Bytes) (CBC.Plain ℓ) Bytes) (qep : ℕ)
    (sRef : GameSt Bytes ℓ) (x : Party × CBC.Plain ℓ × Option PQC) (hts : TransShort sRef) :
    ∀ us ∈ support ((SM.transmitR (sessionSchemeU P ℓ) 3 qep cfg x).run sRef),
      TransShort us.2 := by
  rcases x with ⟨Q, m, r⟩
  intro us hus
  unfold SM.transmitR SM.transmitImpl at hus
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hus
  split at hus
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
    subst hus; exact hts
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hus
    split at hus
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
      subst hus; exact hts
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, exists_prop] at hus
      rcases hus with ⟨cb, _, hus⟩
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none =>
        rw [hep] at hus
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
        subst hus; exact hts
      | some s₁ =>
        rw [hep] at hus
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hus
        subst hus
        exact transShort_record (transShort_epMgmt hep hts) 3 Q _ _ _
          (hrt.send_length_lt _ m.toList (by simp) cb.1)

theorem challR_support_transShort {ℓ : ℕ}
    (P : Params Bytes PQC) (hrt : CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp P ℓ)
    (cfg : SM.ConfigR (GhostState Bytes) (CBC.Plain ℓ) Bytes) (qep : ℕ)
    (sRef : GameSt Bytes ℓ) (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (hts : TransShort sRef) :
    ∀ us ∈ support ((SM.challR (sessionSchemeU P ℓ) 3 qep cfg x).run sRef),
      TransShort us.2 := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  intro us hus
  unfold SM.challR SM.challImpl at hus
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hus
  split at hus
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
    subst hus; exact hts
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hus
    split at hus
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
      subst hus; exact hts
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, exists_prop] at hus
      rcases hus with ⟨cb, _, hus⟩
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none =>
        rw [hep] at hus
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
        subst hus; exact hts
      | some s₁ =>
        rw [hep] at hus
        dsimp only [] at hus
        split at hus
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
          subst hus; exact hts
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hus
          subst hus
          exact transShort_record (transShort_epMgmt hep hts) 3 Q _ _ _
            (hrt.send_length_lt _ _ (by simp) cb.1)

theorem corrR_support_transShort {ℓ : ℕ}
    (cfg : SM.ConfigR (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (sRef : GameSt Bytes ℓ) (Q : Party) (hts : TransShort sRef) :
    ∀ us ∈ support ((SM.corrR cfg Q).run sRef), TransShort us.2 := by
  intro us hus
  unfold SM.corrR at hus
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hus
  split at hus
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
    subst hus; exact hts
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hus
    subst hus; exact transShort_afterCorr hts Q

omit [SampleableType Pt] in
theorem deliverSpkRef_support_transShort {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes)
    (L : List (Pt × BitVec 256)) (abort : Bool) (hts : TransShort sRef) :
    ∀ r ∈ support ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, abort)),
      TransShort r.2.1 := by
  intro r hr
  unfold deliverSpkRef at hr
  rw [StateT.run_mk] at hr
  dsimp only [] at hr
  split at hr
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hts
  · split at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hts
    · simp only [support_bind, Set.mem_iUnion, exists_prop] at hr
      rcases hr with ⟨rc, _, res, _, hr⟩
      rcases res with ⟨o, L'⟩
      cases o with
      | none =>
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hts
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact transShort_accept hts _ _ _

omit [SampleableType Pt] in
theorem injectSpkRef_support_transShort {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes)
    (L : List (Pt × BitVec 256)) (abort : Bool) (hts : TransShort sRef) :
    ∀ r ∈ support ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, abort)),
      TransShort r.2.1 := by
  intro r hr
  unfold injectSpkRef at hr
  rw [StateT.run_mk] at hr
  dsimp only [] at hr
  split at hr
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hts
  · simp only [support_bind, Set.mem_iUnion, exists_prop] at hr
    rcases hr with ⟨rc, _, res, _, hr⟩
    rcases res with ⟨o, L'⟩
    cases o with
    | none =>
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hts
    | some val =>
      rcases val with ⟨st', t', i', m'⟩
      dsimp only [] at hr
      split at hr
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hts
      · split at hr
        · simp only [support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact transShort_accept hts _ _ _
        · simp only [support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hts

theorem evalDist_true_le_one (mx : ProbComp Bool) : 𝒟[mx] {true} ≤ 1 := by
  calc 𝒟[mx] {true} ≤ 𝒟[mx] Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
    _ = 1 := evalDist_apply_univ_eq_one _

omit [SampleableType Pt] in
/-- Couples `runSpkTab` in world `s` with uniform `ck0` to `runSpkRef`. -/
theorem evalDist_runSpkTab_s_le_runSpkRef {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem : ℕ) (hq : SM.MakesAtMostQueries oa rem)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (hcodec : P.codec = protoSignalCodec)
    (hrt : CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp P ℓ) (hts : TransShort sRef)
    (post : Bool → GameSt Bytes ℓ → Bool)
    (hpost : ∀ ck0 b' s', post b' (patchGameSpk P.C s ck0 s') = post b' s') :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      runSpkTab P Dh encT decT qep s oa (patchGameSpk P.C s ck0 sRef) L post] {true} ≤
    𝒟[runSpkRef P Dh encT decT qep s oa sRef L abort post] {true} +
      (rem : ℝ≥0∞) * eps0IdealUnit P.C.F := by
  induction oa using OracleComp.inductionOn generalizing rem sRef L abort with
  | pure a =>
    simp only [runSpkTab_pure, runSpkRef_pure, hpost,
      OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
    cases abort with
    | false =>
      simp only [Bool.false_or]
      exact le_self_add
    | true =>
      cases post a sRef <;> simp
  | query_bind t k ih =>
    cases abort with
    | true =>
      rw [evalDist_runSpkRef_true]
      exact (evalDist_true_le_one _).trans le_self_add
    | false =>
      rw [SM.MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
      simp only [runSpkTab_bind_query, runSpkRef_bind_query]
      rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
      · have hq' : ∀ a, SM.MakesAtMostQueries (k a) rem :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        dsimp only [spkStepImpl, spkRefImpl]
        simp only [stateT_lift_run_any, bind_assoc, pure_bind]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
        exact bind_evalDist_true_le_of_support _ _ _ _ fun a _ =>
          ih a rem (hq' a) sRef L false hinv hts
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkStepImpl, spkRefImpl]
        simp only [liftSpkTab_run, liftSpkRef_run, transmitR_patchGameSpk P decT encT qep s _
          (KeyPair.generate P.C s).publicKey sRef q_tr hinv,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
          ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) q_tr).run sRef)]
        refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
          (add_le_add le_rfl hrem_le)
        exact ih us.1 (rem - 1) (hq' us.1) us.2 L false
          (transmitR_support_spkRefInv P decT encT qep _ sRef q_tr hinv us hus)
          (transmitR_support_transShort P hrt _ qep sRef q_tr hts us hus)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkStepImpl, spkRefImpl]
        simp only [liftSpkTab_run, liftSpkRef_run, challR_patchGameSpk P decT encT qep s _
          (KeyPair.generate P.C s).publicKey sRef q_ch hinv,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
          ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) q_ch).run sRef)]
        refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
          (add_le_add le_rfl hrem_le)
        exact ih us.1 (rem - 1) (hq' us.1) us.2 L false
          (challR_support_spkRefInv P decT encT qep _ sRef q_ch hinv us hus)
          (challR_support_transShort P hrt _ qep sRef q_ch hts us hus)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        have hrem_eq : eps0IdealUnit P.C.F + ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F =
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F := by
          have h1 : (rem : ℝ≥0∞) = (1 : ℕ) + (rem - 1 : ℕ) := by norm_cast; omega
          rw [h1, add_mul, Nat.cast_one, one_mul]
        dsimp only [spkStepImpl, spkRefImpl]
        by_cases hspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = true
        · unfold deliverSpkStep deliverSpkRef
          simp only [StateT.run_mk]
          have hwin : ∀ ck0, (patchGameSpk P.C s ck0 sRef).win = sRef.win := fun _ => rfl
          have htr : ∀ ck0, (patchGameSpk P.C s ck0 sRef).inTransit Q.other c =
              sRef.inTransit Q.other c := fun _ => rfl
          simp only [hwin, htr]
          by_cases hw : sRef.win = true
          · simp only [hw, ↓reduceIte, pure_bind]
            exact (ih none (rem - 1) (hq' none) sRef L false hinv hts).trans (add_le_add le_rfl hrem_le)
          · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
            have hginv := gameInv_of_spkRefInv_win_false hinv hwF
            simp only [hw, Bool.false_eq_true, ↓reduceIte]
            cases h_in : sRef.inTransit Q.other c with
            | none =>
              simp only [pure_bind]
              exact (ih none (rem - 1) (hq' none) sRef L false hinv hts).trans (add_le_add le_rfl
                  hrem_le)
            | some r =>
              have hc32 : c.length < 2 ^ 32 := ct_length_lt_of_inTransit hts Q.other c r h_in
              have hQ : Q = .A := by
                unfold isAliceSpkQuery at hspk
                simp only [Bool.and_eq_true, beq_iff_eq] at hspk
                exact hspk.1.1
              subst hQ
              have hpA : (sRef.st .A).party = .A := spkRefInv_party_eq hinv .A
              have hpA_ck0 : ∀ ck0, ((patchGameSpk P.C s ck0 sRef).st .A).party = .A :=
                fun ck0 => (patchGameSpk_party_eq P.C s ck0 sRef .A).trans hpA
              have href_step : ∀ rc, stepReceiveRef P ℓ Dh encT decT s sRef .A c rc L = pure (none,
                  L) := by
                intro rc
                unfold stepReceiveRef
                rw [hpA]
                simp [hspk]
              simp only [href_step, bind_assoc, pure_bind,
                OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
              refine (bind_apply_le_add_of_evalDist_le_on_good ($ᵗ BitVec 256) _
                (fun ck0 => runSpkTab P Dh encT decT qep s (k (some .rejected))
                  (patchGameSpk P.C s ck0 sRef) L post)
                (testSpk P (sRef.st .A).session.pqRatchetState c) ?_).trans ?_
              · intro ck0 htest
                have hnone : ∀ rc,
                    stepReceiveSpk P ℓ Dh encT decT s ((patchGameSpk P.C s ck0 sRef).st .A) c rc L =
                      pure (none, L) := by
                  intro rc
                  unfold stepReceiveSpk
                  have hpAB : (((patchGameSpk P.C s ck0 sRef).st .A).party == .B) = false :=
                      by rw [hpA_ck0 ck0]; rfl
                  simp only [hpAB, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                  exact congrArg (fun o => pure (o, L))
                    (receive_patchGameSpk_of_spk_test_false P ℓ s ck0
                      (KeyPair.generate P.C s).publicKey sRef .A c rc hginv hspk htest).2
                simp only [hnone, pure_bind,
                    OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
                exact le_rfl
              · calc 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
                        runSpkTab P Dh encT decT qep s (k (some .rejected))
                          (patchGameSpk P.C s ck0 sRef) L post] {true} +
                      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
                        pure (testSpk P (sRef.st .A).session.pqRatchetState c ck0)] {true}
                    ≤ (𝒟[runSpkRef P Dh encT decT qep s (k (some .rejected)) sRef L false post]
                        {true} +
                        ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F) +
                      eps0IdealUnit P.C.F :=
                      add_le_add (ih (some .rejected) (rem - 1) (hq' (some .rejected)) sRef L false
                          hinv hts)
                        (testSpk_le_unit P (sRef.st .A).session.pqRatchetState c hc32)
                  _ = 𝒟[runSpkRef P Dh encT decT qep s (k (some .rejected)) sRef L false post]
                      {true} +
                      (rem : ℝ≥0∞) * eps0IdealUnit P.C.F := by
                      rw [add_assoc, add_comm (((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F),
                          hrem_eq]
        · have hnspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            false :=
            Bool.eq_false_iff.mpr hspk
          simp only [deliverSpkStep_patchGameSpk_of_not_spk P Dh encT decT s s _ sRef Q c L false
            hinv hnspk hnspk, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
          rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
            ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false))]
          refine (bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_).trans
            (add_le_add le_rfl hrem_le)
          have hsupp := deliverSpkRef_support_spkRefInv P Dh encT decT s sRef Q c L false hinv r hr
          rw [hsupp.2]
          exact ih r.1 (rem - 1) (hq' r.1) r.2.1 r.2.2.1 false hsupp.1
            (deliverSpkRef_support_transShort P Dh encT decT s sRef Q c L false hts r hr)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        have hrem_eq : eps0IdealUnit P.C.F + ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F =
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F := by
          have h1 : (rem : ℝ≥0∞) = (1 : ℕ) + (rem - 1 : ℕ) := by norm_cast; omega
          rw [h1, add_mul, Nat.cast_one, one_mul]
        dsimp only [spkStepImpl, spkRefImpl]
        by_cases hspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = true
        · unfold injectSpkStep injectSpkRef
          simp only [StateT.run_mk]
          have hguard : ∀ ck0, ((patchGameSpk P.C s ck0 sRef).win ||
              ((patchGameSpk P.C s ck0 sRef).inTransit Q.other c).isSome ||
              !((patchGameSpk P.C s ck0 sRef).safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
            (sRef.win || (sRef.inTransit Q.other c).isSome || !(sRef.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := fun _ => rfl
          simp only [hguard]
          by_cases hg : (sRef.win || (sRef.inTransit Q.other c).isSome || !(sRef.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
          · simp only [hg, ↓reduceIte, pure_bind]
            exact (ih none (rem - 1) (hq' none) sRef L false hinv hts).trans (add_le_add le_rfl hrem_le)
          · have hwF : sRef.win = false := by
              simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
              exact hg.1.1.1
            have hginv := gameInv_of_spkRefInv_win_false hinv hwF
            have hc32 : c.length < 2 ^ 32 := by
              cases htry : SignalMessage.tryFrom P.codec c with
              | error _ =>
                unfold isAliceSpkQuery at hspk; rw [htry] at hspk; simp at hspk
              | ok msg =>
                refine ratchetKeyAdmissible_length_lt_of_tryFrom P.codec decT encT c msg ?_ htry
                rw [hcodec]
                simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hg
                exact hg.2
            simp only [hg, Bool.false_eq_true, ↓reduceIte]
            have hQ : Q = .A := by
              unfold isAliceSpkQuery at hspk
              simp only [Bool.and_eq_true, beq_iff_eq] at hspk
              exact hspk.1.1
            subst hQ
            have hpA : (sRef.st .A).party = .A := spkRefInv_party_eq hinv .A
            have hpA_ck0 : ∀ ck0, ((patchGameSpk P.C s ck0 sRef).st .A).party = .A :=
              fun ck0 => (patchGameSpk_party_eq P.C s ck0 sRef .A).trans hpA
            have href_step : ∀ rc, stepReceiveRef P ℓ Dh encT decT s sRef .A c rc L = pure (none,
                L) := by
              intro rc
              unfold stepReceiveRef
              rw [hpA]
              simp [hspk]
            simp only [href_step, bind_assoc, pure_bind,
              OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
            refine (bind_apply_le_add_of_evalDist_le_on_good ($ᵗ BitVec 256) _
              (fun ck0 => runSpkTab P Dh encT decT qep s (k (some .rejected))
                (patchGameSpk P.C s ck0 sRef) L post)
              (testSpk P (sRef.st .A).session.pqRatchetState c) ?_).trans ?_
            · intro ck0 htest
              have hnone : ∀ rc,
                  stepReceiveSpk P ℓ Dh encT decT s ((patchGameSpk P.C s ck0 sRef).st .A) c rc L =
                    pure (none, L) := by
                intro rc
                unfold stepReceiveSpk
                have hpAB : (((patchGameSpk P.C s ck0 sRef).st .A).party == .B) = false :=
                    by rw [hpA_ck0 ck0]; rfl
                simp only [hpAB, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                exact congrArg (fun o => pure (o, L))
                  (receive_patchGameSpk_of_spk_test_false P ℓ s ck0
                    (KeyPair.generate P.C s).publicKey sRef .A c rc hginv hspk htest).2
              simp only [hnone, pure_bind,
                  OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
              exact le_rfl
            · calc 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
                      runSpkTab P Dh encT decT qep s (k (some .rejected))
                        (patchGameSpk P.C s ck0 sRef) L post] {true} +
                    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
                      pure (testSpk P (sRef.st .A).session.pqRatchetState c ck0)] {true}
                  ≤ (𝒟[runSpkRef P Dh encT decT qep s (k (some .rejected)) sRef L false post] {true}
                      +
                      ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F) +
                    eps0IdealUnit P.C.F :=
                    add_le_add (ih (some .rejected) (rem - 1) (hq' (some .rejected)) sRef L false
                        hinv hts)
                      (testSpk_le_unit P (sRef.st .A).session.pqRatchetState c hc32)
                _ = 𝒟[runSpkRef P Dh encT decT qep s (k (some .rejected)) sRef L false post] {true}
                    +
                    (rem : ℝ≥0∞) * eps0IdealUnit P.C.F := by
                    rw [add_assoc, add_comm (((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F), hrem_eq]
        · have hnspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            false :=
            Bool.eq_false_iff.mpr hspk
          simp only [injectSpkStep_patchGameSpk_of_not_spk P Dh encT decT qep s s _ sRef Q c L false
            hinv hnspk hnspk, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
          rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
            ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false))]
          refine (bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_).trans
            (add_le_add le_rfl hrem_le)
          have hsupp :=
              injectSpkRef_support_spkRefInv P Dh encT decT qep s sRef Q c L false hinv r hr
          rw [hsupp.2]
          exact ih r.1 (rem - 1) (hq' r.1) r.2.1 r.2.2.1 false hsupp.1
            (injectSpkRef_support_transShort P Dh encT decT qep s sRef Q c L false hts r hr)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * eps0IdealUnit P.C.F ≤
            (rem : ℝ≥0∞) * eps0IdealUnit P.C.F :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkStepImpl, spkRefImpl]
        by_cases hbad : badSpkCorrA decT encT sRef q_corr = true
        · unfold corrSpkRef
          rw [StateT.run_mk]
          dsimp only []
          rw [hbad, Bool.false_or]
          simp only [bind_assoc, pure_bind]
          have h1 : 𝒟[do
              let a ← (SM.corrR (configRefuseEarlyBobCorr decT encT) q_corr).run sRef
              runSpkRef P Dh encT decT qep s (k a.1) a.2 L true post] {true} = 1 :=
            bind_eq_of_support _ _ (measurableSet_singleton _) fun us _ =>
              evalDist_runSpkRef_true P Dh encT decT qep s (k us.1) us.2 L post
          rw [h1]
          exact (evalDist_true_le_one _).trans le_self_add
        · have hbadF : badSpkCorrA decT encT sRef q_corr = false :=
            Bool.eq_false_iff.mpr hbad
          unfold corrSpkRef
          rw [StateT.run_mk]
          dsimp only []
          rw [hbadF, Bool.false_or]
          simp only [liftSpkTab_run, corrR_patchGameSpk_of_badSpkCorrA_false P decT encT s _
            (KeyPair.generate P.C s).publicKey sRef q_corr hinv hbadF,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
          rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
            ((SM.corrR (configRefuseEarlyBobCorr decT encT) q_corr).run sRef)]
          refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
            (add_le_add le_rfl hrem_le)
          exact ih us.1 (rem - 1) (hq' us.1) us.2 L false
            (corrR_support_spkRefInv P decT encT _ sRef q_corr hinv us hus)
            (corrR_support_transShort _ sRef q_corr hts us hus)

theorem patchAlice_chainEpochs (ck0 : BitVec 256) (g : GhostState Bytes) :
    (patchAlice ck0 g).chainEpochs = g.chainEpochs := by
  unfold patchAlice; split <;> rfl

theorem patchBob_party (ck0 : BitVec 256) (g : GhostState Bytes) :
    (patchBob ck0 g).party = g.party := by
  unfold patchBob; split <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem badSpkCorrA_patchGameSpk {ℓ : ℕ} (decT : PublicKey → Option Pt) (encT : Pt →
    PublicKey)
    (C : Crypto) (z ck0 : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) :
    badSpkCorrA decT encT (patchGameSpk C z ck0 sRef) Q = badSpkCorrA decT encT sRef Q := by
  dsimp only [badSpkCorrA, patchGameSpk, patchGameState, patchParty, patchGamePub]
  rw [patchAlice_chainEpochs, patchAlicePub_chainEpochs]
  rfl

theorem hop2BadAt_patchGameSpk_eq_isAliceSpkQuery {ℓ : ℕ}
    (P : Params Bytes PQC) (s z ck0 : BitVec 256) (sRef : GameSt Bytes ℓ) (c : Bytes)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef) :
    hop2BadAt P s ((patchGameSpk P.C z ck0 sRef).st .A) c =
      isAliceSpkQuery P (KeyPair.generate P.C s).publicKey .A (sRef.st .A) c := by
  have hA : (sRef.st .A).party = .A := spkRefInv_party_eq hinv .A
  have hAp : ((patchGameSpk P.C z ck0 sRef).st .A).party = .A := by
    simp only [patchGameSpk, patchGameState, patchGamePub,
      patchAlice_party, patchAlicePub_party, hA]
  dsimp only [hop2BadAt, isAliceSpkQuery]
  rw [hAp]
  simp only [beq_self_eq_true, Bool.true_and,
    patchGameSpk, patchGameState, patchGamePub,
    patchAlice_chainEpochs, patchAlicePub_chainEpochs, List.contains_eq_mem]
  cases SignalMessage.tryFrom P.codec c <;> simp [BEq.comm]

theorem hop2BadAt_patchGameSpk_of_not_spk {ℓ : ℕ}
    (P : Params Bytes PQC) (s z ck0 : BitVec 256) (sRef : GameSt Bytes ℓ)
    (Q : Party) (c : Bytes)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (hnspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = false) :
    hop2BadAt P s ((patchGameSpk P.C z ck0 sRef).st Q) c = false := by
  cases Q with
  | A =>
    rw [hop2BadAt_patchGameSpk_eq_isAliceSpkQuery P s z ck0 sRef c hinv]
    exact hnspk
  | B =>
    have hB : (sRef.st .B).party = .B := spkRefInv_party_eq hinv .B
    have hBp : ((patchGameSpk P.C z ck0 sRef).st .B).party = .B := by
      simp only [patchGameSpk, patchGameState, patchGamePub,
        patchBob_party, patchBobSpk_party, hB]
    unfold hop2BadAt
    rw [hBp]
    rfl

theorem bind_evalDist_true_mono {α : Type} (mx : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ a ∈ support mx, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} := by
  simpa only [add_zero] using
    bind_evalDist_true_le_of_support mx f g 0 (fun a ha => by simpa only [add_zero] using h a ha)

theorem const_le_bind_uniform (m0 : ProbComp Bool) (g : BitVec 256 → ProbComp Bool)
    (h : ∀ rc : BitVec 256, 𝒟[m0] {true} ≤ 𝒟[g rc] {true}) :
    𝒟[m0] {true} ≤ 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= g] {true} := by
  simpa only [OracleComp.evalDist_bind_const ($ᵗ BitVec 256 : ProbComp (BitVec 256))] using
    bind_evalDist_true_mono ($ᵗ BitVec 256 :
        ProbComp (BitVec 256)) (fun _ => m0) g (fun rc _ => h rc)

def deliverSpkBad (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ)))
      (StateT (SpkRefSt Pt ℓ) ProbComp) :=
  fun ⟨Q, c⟩ => StateT.mk fun ⟨st, L, b⟩ => do
    if st.win then return (none, (st, L, b))
    match st.inTransit Q.other c with
    | none => return (none, (st, L, b))
    | some r =>
      let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let (res, L') ← stepReceiveSpk P ℓ Dh encT decT s (st.st Q) c rc L
      match res with
      | none => return (some .rejected, (st, L', b))
      | some (st', t', i', m') =>
        let b' := b || hop2BadAt P s (st.st Q) c
        return (some (.accepted t' i' (if st.chall.contains r.pos then none else some m')),
          (st.accept Q st' r.pos, L', b'))

def injectSpkBad (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ)))
      (StateT (SpkRefSt Pt ℓ) ProbComp) :=
  fun ⟨Q, c⟩ => StateT.mk fun ⟨st, L, b⟩ => do
    if st.win || (st.inTransit Q.other c).isSome || !(st.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c) then
      return (none, (st, L, b))
    let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let (res, L') ← stepReceiveSpk P ℓ Dh encT decT s (st.st Q) c rc L
    match res with
    | none => return (some .rejected, (st, L', b))
    | some (st', t', i', m') =>
      let b' := b || hop2BadAt P s (st.st Q) c
      if qep + 1 < t' then return (some .rejected, (st, L', b'))
      let pos : SM.Pos := ⟨Q.other, t', i'⟩
      if st.trivial 3 pos then
        return (some (.accepted t' i' (some m')), (st.accept Q st' pos, L', b'))
      else
        return (some .rejected, ({ st with win := true }, L', b'))

def spkBadImpl (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) :
    QueryImpl (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
      (StateT (SpkRefSt Pt ℓ) ProbComp)
  | .inl u => StateT.lift (query (spec := unifSpec) u)
  | .inr (.inl (.inl (.inl (.inl x)))) =>
    liftSpkRef (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inl (.inr x)))) =>
    liftSpkRef (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inr x))) =>
    deliverSpkBad P ℓ Dh encT decT s x
  | .inr (.inl (.inr x)) =>
    injectSpkBad P ℓ Dh encT decT qep s x
  | .inr (.inr x) =>
    corrSpkRef ℓ decT encT x

def runSpkBad {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool) : ProbComp Bool := do
  let (_, (_, _, bad')) ← (simulateQ (spkBadImpl P ℓ Dh encT decT qep s) oa).run (st, L, bad)
  return bad'

def runSpkComb {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (post : β → GameSt Bytes ℓ → Bool) : ProbComp Bool := do
  let (b', (fin, _, bad')) ← (simulateQ (spkBadImpl P ℓ Dh encT decT qep s) oa).run (st, L, bad)
  return (bad' || post b' fin)

omit [SampleableType Pt] in
@[simp] theorem runSpkBad_pure {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (a : β) (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool) :
    runSpkBad P Dh encT decT qep s (pure a) st L bad = pure bad := by
  simp [runSpkBad, StateT.run_pure]

omit [SampleableType Pt] in
theorem runSpkBad_bind_query {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (k : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Range t →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool) :
    runSpkBad P Dh encT decT qep s
      (liftM (OracleSpec.query (spec := unifSpec +
          SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) t) >>= k)
      st L bad =
      ((spkBadImpl P ℓ Dh encT decT qep s t).run (st, L, bad) >>= fun r =>
        runSpkBad P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2) := by
  simp [runSpkBad, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

omit [SampleableType Pt] in
@[simp] theorem runSpkComb_pure {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (a : β) (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (post : β → GameSt Bytes ℓ → Bool) :
    runSpkComb P Dh encT decT qep s (pure a) st L bad post = pure (bad || post a st) := by
  simp [runSpkComb, StateT.run_pure]

omit [SampleableType Pt] in
theorem runSpkComb_bind_query {ℓ : ℕ} {β : Type} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (k : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Range t →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (post : β → GameSt Bytes ℓ → Bool) :
    runSpkComb P Dh encT decT qep s
      (liftM (OracleSpec.query (spec := unifSpec +
          SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) t) >>= k)
      st L bad post =
      ((spkBadImpl P ℓ Dh encT decT qep s t).run (st, L, bad) >>= fun r =>
        runSpkComb P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post) := by
  simp [runSpkComb, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

omit [SampleableType Pt] in
theorem spkBadImpl_support_bad_true {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) :
    ∀ r ∈ support ((spkBadImpl P ℓ Dh encT decT qep s t).run (st, L, true)),
      r.2.2.2 = true := by
  intro r hr
  rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
  · dsimp only [spkBadImpl] at hr
    rw [stateT_lift_run_any] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkBadImpl] at hr
    rw [liftSpkRef_run] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkBadImpl] at hr
    rw [liftSpkRef_run] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl
  · dsimp only [spkBadImpl, deliverSpkBad] at hr
    rw [StateT.run_mk] at hr
    dsimp only [] at hr
    split at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
    · split at hr
      · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
      · simp only [support_bind, Set.mem_iUnion, exists_prop] at hr
        rcases hr with ⟨rc, _, res, _, hr⟩
        rcases res with ⟨o, L'⟩
        cases o with
        | none => simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          simp only [Bool.true_or, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
  · dsimp only [spkBadImpl, injectSpkBad] at hr
    rw [StateT.run_mk] at hr
    dsimp only [] at hr
    split at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
    · simp only [support_bind, Set.mem_iUnion, exists_prop] at hr
      rcases hr with ⟨rc, _, res, _, hr⟩
      rcases res with ⟨o, L'⟩
      cases o with
      | none => simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        dsimp only [] at hr
        split at hr
        · simp only [Bool.true_or, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
        · split at hr <;>
            (simp only [Bool.true_or, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl)
  · dsimp only [spkBadImpl, corrSpkRef] at hr
    rw [StateT.run_mk] at hr
    simp only [Bool.true_or, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩; rfl


omit [SampleableType Pt] in
theorem evalDist_runSpkComb_true {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256))
    (post : β → GameSt Bytes ℓ → Bool) :
    𝒟[runSpkComb P Dh encT decT qep s oa st L true post] {true} = 1 := by
  induction oa using OracleComp.inductionOn generalizing st L with
  | pure a => simp [runSpkComb_pure]
  | query_bind t k ih =>
    rw [runSpkComb_bind_query]
    exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr => by
      rw [spkBadImpl_support_bad_true P Dh encT decT qep s t st L r hr]
      exact ih r.1 r.2.1 r.2.2.1

omit [SampleableType Pt] in
theorem spkBadImpl_run_bind_fst {ℓ : ℕ} {α : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (t : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (F : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Range t ×
      SpkTabSt Pt ℓ → ProbComp α) :
    ((spkBadImpl P ℓ Dh encT decT qep s t).run (st, L, bad) >>= fun r =>
      F (r.1, (r.2.1, r.2.2.1))) =
    ((spkStepImpl P ℓ Dh encT decT qep s t).run (st, L) >>= F) := by
  rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
  · dsimp only [spkBadImpl, spkStepImpl]
    simp [map_eq_bind_pure_comp, bind_assoc]
  · dsimp only [spkBadImpl, spkStepImpl]
    simp [liftSpkRef_run, liftSpkTab_run, map_eq_bind_pure_comp, bind_assoc]
  · dsimp only [spkBadImpl, spkStepImpl]
    simp [liftSpkRef_run, liftSpkTab_run, map_eq_bind_pure_comp, bind_assoc]
  · dsimp only [spkBadImpl, spkStepImpl, deliverSpkBad, deliverSpkStep]
    rw [StateT.run_mk, StateT.run_mk]
    dsimp only []
    by_cases hw : st.win = true
    · simp [hw]
    · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      cases st.inTransit Q.other c with
      | none => simp
      | some r =>
        simp only [bind_assoc]
        refine bind_congr fun rc => bind_congr fun res => ?_
        rcases res with ⟨o, L'⟩
        cases o with
        | none => simp
        | some val => rcases val with ⟨st', t', i', m'⟩; simp
  · dsimp only [spkBadImpl, spkStepImpl, injectSpkBad, injectSpkStep]
    rw [StateT.run_mk, StateT.run_mk]
    dsimp only []
    split
    · simp
    · simp only [bind_assoc]
      refine bind_congr fun rc => bind_congr fun res => ?_
      rcases res with ⟨o, L'⟩
      cases o with
      | none => simp
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        dsimp only []
        split
        · simp
        · split <;> simp
  · dsimp only [spkBadImpl, spkStepImpl, corrSpkRef]
    rw [StateT.run_mk, liftSpkTab_run]
    simp [map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType Pt] in
theorem simulateQ_spkBadImpl_run_bind_post {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (post : β → GameSt Bytes ℓ → Bool) :
    ((simulateQ (spkBadImpl P ℓ Dh encT decT qep s) oa).run (st, L, bad) >>= fun r =>
      pure (post r.1 r.2.1)) =
    runSpkTab P Dh encT decT qep s oa st L post := by
  induction oa using OracleComp.inductionOn generalizing st L bad with
  | pure a => simp [runSpkTab_pure, StateT.run_pure]
  | query_bind t k ih =>
    rw [runSpkTab_bind_query]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
    rw [← spkBadImpl_run_bind_fst P Dh encT decT qep s t st L bad
      (fun r => runSpkTab P Dh encT decT qep s (k r.1) r.2.1 r.2.2 post)]
    refine bind_congr fun r => ih r.1 r.2.1 r.2.2.1 r.2.2.2

omit [SampleableType Pt] in
theorem evalDist_runSpkComb_le_add {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (fSt : BitVec 256 → GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (bad : Bool)
    (post : β → GameSt Bytes ℓ → Bool) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkComb P Dh encT decT qep s oa (fSt x) L bad post] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkTab P Dh encT decT qep s oa (fSt x) L post] {true} +
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkBad P Dh encT decT qep s oa (fSt x) L bad] {true} := by
  set mx := ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
    (simulateQ (spkBadImpl P ℓ Dh encT decT qep s) oa).run (fSt x, L, bad)
  have hcomb : (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkComb P Dh encT decT qep s oa (fSt x) L bad post) =
    (mx >>= fun r => pure (post r.1 r.2.1 || r.2.2.2)) := by
    dsimp only [mx, runSpkComb]
    rw [bind_assoc]
    refine bind_congr fun x => bind_congr fun r => by simp [Bool.or_comm]
  have htab : (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkTab P Dh encT decT qep s oa (fSt x) L post) =
    (mx >>= fun r => pure (post r.1 r.2.1)) := by
    dsimp only [mx]
    rw [bind_assoc]
    refine bind_congr fun x => (simulateQ_spkBadImpl_run_bind_post P Dh encT decT qep s oa (fSt x) L
        bad post).symm
  have hbad : (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkBad P Dh encT decT qep s oa (fSt x) L bad) =
    (mx >>= fun r => pure r.2.2.2) := by
    dsimp only [mx, runSpkBad]
    rw [bind_assoc]
  rw [hcomb, htab, hbad]
  exact bind_or_evalDist_true_le mx (fun r => post r.1 r.2.1) (fun r => r.2.2.2)

omit [SampleableType Pt] in
theorem deliverSpkBad_patchGameSpk_of_not_spk {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s z ck0 : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes)
    (L : List (Pt × BitVec 256)) (abort : Bool)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (hnspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = false)
    (hnspk_z : isAliceSpkQuery P (KeyPair.generate P.C z).publicKey Q (sRef.st .A) c = false) :
    (deliverSpkBad P ℓ Dh encT decT s (Q, c)).run (patchGameSpk P.C z ck0 sRef, L, abort) =
      (fun r => (r.1, (patchGameSpk P.C z ck0 r.2.1, r.2.2.1, r.2.2.2))) <$>
        (deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, abort) := by
  unfold deliverSpkBad deliverSpkRef
  rw [StateT.run_mk, StateT.run_mk]
  dsimp only []
  have hwin : (patchGameSpk P.C z ck0 sRef).win = sRef.win := rfl
  have htr : (patchGameSpk P.C z ck0 sRef).inTransit Q.other c = sRef.inTransit Q.other c := rfl
  have hch : (patchGameSpk P.C z ck0 sRef).chall = sRef.chall := rfl
  have hbad0 := hop2BadAt_patchGameSpk_of_not_spk P s z ck0 sRef Q c hinv hnspk_s
  rw [hwin, htr, hch, hbad0, Bool.or_false]
  by_cases hw : sRef.win = true
  · simp [hw]
  · have hwF : sRef.win = false := Bool.eq_false_iff.mpr hw
    simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases sRef.inTransit Q.other c with
    | none => simp
    | some r =>
      simp only [map_bind]
      refine bind_congr fun rc => ?_
      rw [stepReceiveSpk_patchGameSpk_of_not_spk P Dh encT decT s z ck0 sRef Q c rc L hinv hwF
          hnspk_s hnspk_z]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun res => ?_
      rcases res with ⟨o, L'⟩
      cases o with
      | none => simp
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        simp only [Option.map, pure_bind, Function.comp_apply]
        rw [← patchGameSpk_accept P.C z ck0 sRef Q st' r.pos]
        rfl

omit [SampleableType Pt] in
theorem injectSpkBad_patchGameSpk_of_not_spk {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s z ck0 : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes)
    (L : List (Pt × BitVec 256)) (abort : Bool)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (hnspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = false)
    (hnspk_z : isAliceSpkQuery P (KeyPair.generate P.C z).publicKey Q (sRef.st .A) c = false) :
    (injectSpkBad P ℓ Dh encT decT qep s (Q, c)).run (patchGameSpk P.C z ck0 sRef, L, abort) =
      (fun r => (r.1, (patchGameSpk P.C z ck0 r.2.1, r.2.2.1, r.2.2.2))) <$>
        (injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, abort) := by
  unfold injectSpkBad injectSpkRef
  rw [StateT.run_mk, StateT.run_mk]
  dsimp only []
  have hguard : ((patchGameSpk P.C z ck0 sRef).win ||
      ((patchGameSpk P.C z ck0 sRef).inTransit Q.other c).isSome ||
      !((patchGameSpk P.C z ck0 sRef).safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
    (sRef.win || (sRef.inTransit Q.other c).isSome || !(sRef.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := rfl
  have htriv : ∀ pos, (patchGameSpk P.C z ck0 sRef).trivial 3 pos = sRef.trivial 3 pos :=
    fun _ => rfl
  have hbad0 := hop2BadAt_patchGameSpk_of_not_spk P s z ck0 sRef Q c hinv hnspk_s
  rw [hguard, hbad0, Bool.or_false]
  by_cases hg : (sRef.win || (sRef.inTransit Q.other c).isSome || !(sRef.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · simp [hg]
  · have hwF : sRef.win = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
      exact hg.1.1.1
    simp only [hg, Bool.false_eq_true, ↓reduceIte, map_bind]
    refine bind_congr fun rc => ?_
    rw [stepReceiveSpk_patchGameSpk_of_not_spk P Dh encT decT s z ck0 sRef Q c rc L hinv hwF hnspk_s
        hnspk_z]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun res => ?_
    rcases res with ⟨o, L'⟩
    cases o with
    | none => simp
    | some val =>
      rcases val with ⟨st', t', i', m'⟩
      dsimp only [Option.map]
      by_cases hcap : qep + 1 < t'
      · simp [hcap]
      · simp only [hcap, ↓reduceIte, htriv]
        by_cases htr : sRef.trivial 3 ⟨Q.other, t', i'⟩ = true
        · simp only [htr, ↓reduceIte, pure_bind, Function.comp_apply]
          rw [← patchGameSpk_accept P.C z ck0 sRef Q st' ⟨Q.other, t', i'⟩]
          rfl
        · simp [htr]
          rfl

theorem evalDist_runSpkRef_le_runSpkComb_x {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (s ck0 : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem : ℕ) (hq : SM.MakesAtMostQueries oa rem)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (post : Bool → GameSt Bytes ℓ → Bool)
    (hpost : ∀ x b' s', post b' (patchGameSpk P.C x ck0 s') = post b' s') :
    𝒟[runSpkRef P Dh encT decT qep s oa sRef L abort post] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkComb P Dh encT decT qep s oa (patchGameSpk P.C x ck0 sRef) L abort post] {true} +
      (rem : ℝ≥0∞) * hop2GuessUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem sRef L abort with
  | pure a =>
    simp only [runSpkRef_pure, runSpkComb_pure, hpost,
      OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
    exact le_self_add
  | query_bind t k ih =>
    cases abort with
    | true =>
      have h1 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
          runSpkComb P Dh encT decT qep s (liftM (OracleSpec.query t) >>= k)
            (patchGameSpk P.C x ck0 sRef) L true post] {true} = 1 :=
        bind_eq_of_support _ _ (measurableSet_singleton _) fun x _ =>
          evalDist_runSpkComb_true P Dh encT decT qep s _ (patchGameSpk P.C x ck0 sRef) L post
      rw [h1]
      exact (evalDist_true_le_one _).trans le_self_add
    | false =>
      rw [SM.MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
      rw [runSpkRef_bind_query]
      simp only [runSpkComb_bind_query]
      rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
      · have hq' : ∀ a, SM.MakesAtMostQueries (k a) rem :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        dsimp only [spkRefImpl, spkBadImpl]
        simp only [stateT_lift_run_any, bind_assoc, pure_bind
            ]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
        exact bind_evalDist_true_le_of_support _ _ _ _ fun a _ => ih a rem (hq' a) sRef L false hinv
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkRefImpl, spkBadImpl]
        simp only [liftSpkRef_run, transmitR_patchGameSpk P decT encT qep _ ck0
          (KeyPair.generate P.C s).publicKey sRef q_tr hinv,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
          ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) q_tr).run sRef)]
        refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
          (add_le_add le_rfl hrem_le)
        exact ih us.1 (rem - 1) (hq' us.1) us.2 L false
          (transmitR_support_spkRefInv P decT encT qep _ sRef q_tr hinv us hus)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkRefImpl, spkBadImpl]
        simp only [liftSpkRef_run, challR_patchGameSpk P decT encT qep _ ck0
          (KeyPair.generate P.C s).publicKey sRef q_ch hinv,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
          ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) q_ch).run sRef)]
        refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
          (add_le_add le_rfl hrem_le)
        exact ih us.1 (rem - 1) (hq' us.1) us.2 L false
          (challR_support_spkRefInv P decT encT qep _ sRef q_ch hinv us hus)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        have hrem_eq : hop2GuessUnit Dh + ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh =
            (rem : ℝ≥0∞) * hop2GuessUnit Dh := by
          have hr1 : (1 : ℝ≥0∞) + ((rem - 1 : ℕ) : ℝ≥0∞) = (rem : ℝ≥0∞) := by
            exact_mod_cast (by omega : 1 + (rem - 1) = rem)
          calc hop2GuessUnit Dh + ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh
              = (1 + ((rem - 1 : ℕ) : ℝ≥0∞)) * hop2GuessUnit Dh := by rw [add_mul, one_mul]
            _ = (rem : ℝ≥0∞) * hop2GuessUnit Dh := by rw [hr1]
        dsimp only [spkRefImpl, spkBadImpl]
        by_cases hspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            true
        · have hQ : Q = .A := by
            cases Q with
            | A => rfl
            | B => simp [isAliceSpkQuery] at hspk_s
          subst hQ
          unfold deliverSpkRef deliverSpkBad
          rw [StateT.run_mk]
          simp only [StateT.run_mk]
          have hwin : ∀ x, (patchGameSpk P.C x ck0 sRef).win = sRef.win := fun _ => rfl
          have htr : ∀ x, (patchGameSpk P.C x ck0 sRef).inTransit Party.A.other c =
              sRef.inTransit Party.A.other c := fun _ => rfl
          simp only [hwin, htr]
          by_cases hw : sRef.win = true
          · simp only [hw, ↓reduceIte, pure_bind]
            exact (ih none (rem - 1) (hq' none) sRef L false hinv).trans (add_le_add le_rfl hrem_le)
          · simp only [hw, Bool.false_eq_true, ↓reduceIte]
            cases htr_eq : sRef.inTransit Party.A.other c with
            | none =>
              simp only [pure_bind]
              exact (ih none (rem - 1) (hq' none) sRef L false hinv).trans (add_le_add le_rfl
                  hrem_le)
            | some rec' =>
              have hAp : (sRef.st .A).party = .A := spkRefInv_party_eq hinv .A
              have hB0_ref : ((sRef.st .A).party == .B && (sRef.st .A).epoch == 0) = false := by
                simp [hAp]
              unfold stepReceiveRef
              simp only [hB0_ref, Bool.false_eq_true, ↓reduceIte,
                hspk_s, bind_assoc, pure_bind, OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
              refine (ih (some .rejected) (rem - 1) (hq' (some .rejected)) sRef L false hinv).trans
                  ?_
              refine (add_le_add (bind_evalDist_true_mono ($ᵗ BitVec 256) _ _ fun x _ => ?_)
                  le_rfl).trans
                (add_le_add le_rfl hrem_le)
              refine const_le_bind_uniform _ _ fun rc => ?_
              have hAp_x : ((patchGameSpk P.C x ck0 sRef).st .A).party = .A := by
                simp only [patchGameSpk, patchGameState, patchGamePub,
                  patchAlice_party, patchAlicePub_party, hAp]
              have hB0_x : (((patchGameSpk P.C x ck0 sRef).st .A).party == .B &&
                  ((patchGameSpk P.C x ck0 sRef).st .A).epoch == 0) = false := by
                rw [hAp_x]; rfl
              unfold stepReceiveSpk
              simp only [hB0_x, Bool.false_eq_true, ↓reduceIte, pure_bind]
              cases (sessionSchemeU P ℓ).receive ((patchGameSpk P.C x ck0 sRef).st .A) c rc with
              | none => simp only [pure_bind]; exact le_rfl
              | some val =>
                rcases val with ⟨st', t', i', m'⟩
                simp only [Bool.false_or,
                    hop2BadAt_patchGameSpk_eq_isAliceSpkQuery P s x ck0 sRef c hinv,
                  hspk_s, pure_bind, evalDist_runSpkComb_true]
                exact evalDist_true_le_one _
        · have hnspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            false :=
            Bool.eq_false_iff.mpr hspk_s
          have h1 : 𝒟[(deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
              runSpkRef P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true} ≤
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1) r.2.2.1 false
                    post] {true} +
            ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
            rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
              ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false))]
            refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
            have hsupp :=
                deliverSpkRef_support_spkRefInv P Dh encT decT s sRef Q c L false hinv r hr
            rw [hsupp.2]
            exact ih r.1 (rem - 1) (hq' r.1) r.2.1 r.2.2.1 false hsupp.1
          have h2 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1) r.2.2.1 false
                    post] {true} ≤
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (deliverSpkBad P ℓ Dh encT decT s (Q, c)).run (patchGameSpk P.C x ck0 sRef, L,
                  false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true} +
            hop2GuessUnit Dh := by
            refine (bind_apply_le_add_of_evalDist_le_on_good ($ᵗ BitVec 256 : ProbComp (BitVec 256))
              _ _ (fun x => isAliceSpkQuery P (KeyPair.generate P.C x).publicKey Q (sRef.st .A) c)
              fun x hnspk_x => ?_).trans
              (add_le_add le_rfl (isAliceSpkQuery_prob_le_hop2GuessUnit P Dh encPt decT encT hX hdec
                  Q (sRef.st .A) c))
            rw [deliverSpkBad_patchGameSpk_of_not_spk P Dh encT decT s x ck0 sRef Q c L false hinv
                hnspk_s hnspk_x]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            have heq : ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1) r.2.2.1 false
                    post) =
              ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1) r.2.2.1
                    r.2.2.2 post) :=
              bind_congr_of_support _ _ _ fun r hr => by
                rw [(deliverSpkRef_support_spkRefInv P Dh encT decT s sRef Q c L false hinv r hr).2]
            rw [heq]
          calc 𝒟[(deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkRef P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true}
              ≤ (𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
                  (deliverSpkBad P ℓ Dh encT decT s (Q, c)).run (patchGameSpk P.C x ck0 sRef, L,
                      false) >>= fun r =>
                    runSpkComb P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true} +
                  hop2GuessUnit Dh) +
                ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
                h1.trans (add_le_add h2 le_rfl)
            _ = 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
                  (deliverSpkBad P ℓ Dh encT decT s (Q, c)).run (patchGameSpk P.C x ck0 sRef, L,
                      false) >>= fun r =>
                    runSpkComb P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true} +
                (rem : ℝ≥0∞) * hop2GuessUnit Dh := by
                rw [add_assoc, hrem_eq]
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        have hrem_eq : hop2GuessUnit Dh + ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh =
            (rem : ℝ≥0∞) * hop2GuessUnit Dh := by
          have hr1 : (1 : ℝ≥0∞) + ((rem - 1 : ℕ) : ℝ≥0∞) = (rem : ℝ≥0∞) := by
            exact_mod_cast (by omega : 1 + (rem - 1) = rem)
          calc hop2GuessUnit Dh + ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh
              = (1 + ((rem - 1 : ℕ) : ℝ≥0∞)) * hop2GuessUnit Dh := by rw [add_mul, one_mul]
            _ = (rem : ℝ≥0∞) * hop2GuessUnit Dh := by rw [hr1]
        dsimp only [spkRefImpl, spkBadImpl]
        by_cases hspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            true
        · have hQ : Q = .A := by
            cases Q with
            | A => rfl
            | B => simp [isAliceSpkQuery] at hspk_s
          subst hQ
          unfold injectSpkRef injectSpkBad
          rw [StateT.run_mk]
          simp only [StateT.run_mk]
          have hguard : ∀ x, ((patchGameSpk P.C x ck0 sRef).win ||
              ((patchGameSpk P.C x ck0 sRef).inTransit Party.A.other c).isSome ||
              !((patchGameSpk P.C x ck0 sRef).safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
            (sRef.win || (sRef.inTransit Party.A.other c).isSome || !(sRef.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := fun _ => rfl
          simp only [hguard]
          by_cases hg : (sRef.win || (sRef.inTransit Party.A.other c).isSome || !(sRef.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
          · simp only [hg, ↓reduceIte, pure_bind]
            exact (ih none (rem - 1) (hq' none) sRef L false hinv).trans (add_le_add le_rfl hrem_le)
          · simp only [hg, Bool.false_eq_true, ↓reduceIte]
            have hAp : (sRef.st .A).party = .A := spkRefInv_party_eq hinv .A
            have hB0_ref : ((sRef.st .A).party == .B && (sRef.st .A).epoch == 0) = false := by
              simp [hAp]
            unfold stepReceiveRef
            simp only [hB0_ref, Bool.false_eq_true, ↓reduceIte,
              hspk_s, bind_assoc, pure_bind, OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
            refine (ih (some .rejected) (rem - 1) (hq' (some .rejected)) sRef L false hinv).trans ?_
            refine (add_le_add (bind_evalDist_true_mono ($ᵗ BitVec 256) _ _ fun x _ => ?_)
                le_rfl).trans
              (add_le_add le_rfl hrem_le)
            refine const_le_bind_uniform _ _ fun rc => ?_
            have hAp_x : ((patchGameSpk P.C x ck0 sRef).st .A).party = .A := by
              simp only [patchGameSpk, patchGameState, patchGamePub,
                patchAlice_party, patchAlicePub_party, hAp]
            have hB0_x : (((patchGameSpk P.C x ck0 sRef).st .A).party == .B &&
                ((patchGameSpk P.C x ck0 sRef).st .A).epoch == 0) = false := by
              rw [hAp_x]; rfl
            unfold stepReceiveSpk
            simp only [hB0_x, Bool.false_eq_true, ↓reduceIte, pure_bind]
            cases (sessionSchemeU P ℓ).receive ((patchGameSpk P.C x ck0 sRef).st .A) c rc with
            | none => simp only [pure_bind]; exact le_rfl
            | some val =>
              rcases val with ⟨st', t', i', m'⟩
              dsimp only []
              rw [Bool.false_or, hop2BadAt_patchGameSpk_eq_isAliceSpkQuery P s x ck0 sRef c hinv,
                  hspk_s]
              split
              · simp only [pure_bind, evalDist_runSpkComb_true]; exact evalDist_true_le_one _
              · split <;> (simp only [pure_bind,
                  evalDist_runSpkComb_true]; exact evalDist_true_le_one _)
        · have hnspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            false :=
            Bool.eq_false_iff.mpr hspk_s
          have h1 : 𝒟[(injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
              runSpkRef P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true} ≤
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1) r.2.2.1 false
                    post] {true} +
            ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
            rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
              ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false))]
            refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
            have hsupp :=
                injectSpkRef_support_spkRefInv P Dh encT decT qep s sRef Q c L false hinv r hr
            rw [hsupp.2]
            exact ih r.1 (rem - 1) (hq' r.1) r.2.1 r.2.2.1 false hsupp.1
          have h2 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1) r.2.2.1 false
                    post] {true} ≤
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (injectSpkBad P ℓ Dh encT decT qep s (Q, c)).run (patchGameSpk P.C x ck0 sRef, L,
                  false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true} +
            hop2GuessUnit Dh := by
            refine (bind_apply_le_add_of_evalDist_le_on_good ($ᵗ BitVec 256 : ProbComp (BitVec 256))
              _ _ (fun x => isAliceSpkQuery P (KeyPair.generate P.C x).publicKey Q (sRef.st .A) c)
              fun x hnspk_x => ?_).trans
              (add_le_add le_rfl (isAliceSpkQuery_prob_le_hop2GuessUnit P Dh encPt decT encT hX hdec
                  Q (sRef.st .A) c))
            rw [injectSpkBad_patchGameSpk_of_not_spk P Dh encT decT qep s x ck0 sRef Q c L false
                hinv hnspk_s hnspk_x]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            have heq : ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L,
                false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1) r.2.2.1 false
                    post) =
              ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkComb P Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1) r.2.2.1
                    r.2.2.2 post) :=
              bind_congr_of_support _ _ _ fun r hr => by
                rw [(injectSpkRef_support_spkRefInv P Dh encT decT qep s sRef Q c L false hinv r
                    hr).2]
            rw [heq]
          calc 𝒟[(injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkRef P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true}
              ≤ (𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
                  (injectSpkBad P ℓ Dh encT decT qep s (Q, c)).run (patchGameSpk P.C x ck0 sRef, L,
                      false) >>= fun r =>
                    runSpkComb P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true} +
                  hop2GuessUnit Dh) +
                ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
                h1.trans (add_le_add h2 le_rfl)
            _ = 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
                  (injectSpkBad P ℓ Dh encT decT qep s (Q, c)).run (patchGameSpk P.C x ck0 sRef, L,
                      false) >>= fun r =>
                    runSpkComb P Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 post] {true} +
                (rem : ℝ≥0∞) * hop2GuessUnit Dh := by
                rw [add_assoc, hrem_eq]
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, SM.MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [SM.MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkRefImpl, spkBadImpl]
        by_cases hbad : badSpkCorrA decT encT sRef q_corr = true
        · unfold corrSpkRef
          simp only [StateT.run_mk, badSpkCorrA_patchGameSpk,
            hbad, Bool.false_or, bind_assoc, pure_bind]
          have h1 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (SM.corrR (configRefuseEarlyBobCorr decT encT) q_corr).run (patchGameSpk P.C x ck0 sRef) >>= fun a
                  =>
                runSpkComb P Dh encT decT qep s (k a.1) a.2 L true post] {true} = 1 :=
            bind_eq_of_support _ _ (measurableSet_singleton _) fun x _ =>
              bind_eq_of_support _ _ (measurableSet_singleton _) fun us _ =>
                evalDist_runSpkComb_true P Dh encT decT qep s (k us.1) us.2 L post
          rw [h1]
          exact (evalDist_true_le_one _).trans le_self_add
        · have hbadF : badSpkCorrA decT encT sRef q_corr = false :=
            Bool.eq_false_iff.mpr hbad
          unfold corrSpkRef
          simp only [StateT.run_mk, badSpkCorrA_patchGameSpk,
            hbadF, Bool.false_or, corrR_patchGameSpk_of_badSpkCorrA_false P decT encT _ ck0
              (KeyPair.generate P.C s).publicKey sRef q_corr hinv hbadF,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
          rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
            ((SM.corrR (configRefuseEarlyBobCorr decT encT) q_corr).run sRef)]
          refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
            (add_le_add le_rfl hrem_le)
          exact ih us.1 (rem - 1) (hq' us.1) us.2 L false
            (corrR_support_spkRefInv P decT encT _ sRef q_corr hinv us hus)

/-- Couples `runSpkRef` to `runSpkTab` in world `x` plus `runSpkBad` and the guessing term. -/
theorem evalDist_runSpkRef_le_runSpkTab_x_add_bad {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (s ck0 : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem : ℕ) (hq : SM.MakesAtMostQueries oa rem)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (post : Bool → GameSt Bytes ℓ → Bool)
    (hpost : ∀ x b' s', post b' (patchGameSpk P.C x ck0 s') = post b' s') :
    𝒟[runSpkRef P Dh encT decT qep s oa sRef L abort post] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkTab P Dh encT decT qep s oa (patchGameSpk P.C x ck0 sRef) L post] {true} +
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkBad P Dh encT decT qep s oa (patchGameSpk P.C x ck0 sRef) L abort] {true} +
      (rem : ℝ≥0∞) * hop2GuessUnit Dh := by
  exact (evalDist_runSpkRef_le_runSpkComb_x P Dh encPt encT decT hX hdec qep s ck0
    oa rem hq sRef L abort hinv post hpost).trans
    (add_le_add (evalDist_runSpkComb_le_add P Dh encT decT qep s oa
      (fun x => patchGameSpk P.C x ck0 sRef) L abort post) le_rfl)
end HInit
end CryptoVerification.E2E.SpkHop1
