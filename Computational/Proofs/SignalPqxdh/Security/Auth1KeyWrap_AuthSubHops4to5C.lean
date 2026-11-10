/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `Auth` `IND-CPA` Cutoff Telescoping

Adapts the session-cutoff and creation-order slot-cutoff `IND-CPA` hybrid experiments and
telescoping bound (`abs_sub_authCpaCutoffExp_le_mul_aeadIndCpa1Key`) from `AuthSubHops4to5C`
to the single-scalar `Auth` oracle `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open Classical
open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh
  (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt
   initSessionSlotIdx_inj_of_lt RelProbUpToBad simulateQ_relProbUpToBad
   evalDist_simulateQ_eq_of_step_or_bad)

theorem stepUntilAuthCpaChallengeFixedPrim_pure1Key (idx : Nat) (S : Setup) {α : Type}
    (defaultVal a : α) (fuel : Nat) (hst : AuthHybridStateFixed S) :
    stepUntilAuthCpaChallengeFixedPrim1Key idx S defaultVal (pure a) fuel hst =
      pure (.done a hst) := rfl

@[simp]
theorem stepUntilAuthCpaChallengeFixedPrim_query_inl1Key (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α) (n : Nat)
    (cont : (unifSpec + authSpec S).Range (Sum.inl n) → OracleComp (unifSpec + authSpec S) α)
    (fuel : Nat) (hst : AuthHybridStateFixed S) :
    stepUntilAuthCpaChallengeFixedPrim1Key idx S defaultVal
        (liftM (OracleSpec.query (Sum.inl n)) >>= cont) fuel hst =
      (liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n)) >>=
        fun u => stepUntilAuthCpaChallengeFixedPrim1Key idx S defaultVal (cont u) fuel hst) := rfl

theorem aeadCpaReductionAuthFixed_prim_queries1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadCpaReductionAuthFixed1Key S b A).q_prim ≤ primQueryBudget S b := by
  unfold aeadCpaReductionAuthFixed1Key perQueryAuthPrimBudget primQueryBudget
  dsimp only
  nlinarith

private theorem bind_congr_of_mem_support_spec {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (oa : OracleComp spec α) (f g : α → OracleComp spec β)
    (h : ∀ x ∈ support oa, f x = g x) :
    oa >>= f = oa >>= g := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simpa using h x (by simp)
  | query_bind i t ih =>
    rw [bind_assoc, bind_assoc]
    apply bind_congr; intro u
    exact ih u (fun x hx => h x (MonadAttach.mem_support_bind.mpr ⟨u, by simp, hx⟩))

@[simp]
private theorem simulateQ_primQ_aeadEnc_bytes (P : Primitives) (mk : MessageKeys) (ad pt : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.aeadEnc mk ad pt)) : ProbComp Bytes) =
      pure (P.aeadEnc mk ad pt) := rfl

@[irreducible]
private def withSid {S : Setup} (sid : SessionId S) (p : AuthCpaPausePayload S) :
    AuthCpaPausePayload S :=
  { p with sid := sid }

private theorem withSid_sid {S : Setup} (sid : SessionId S) (p : AuthCpaPausePayload S) :
    (withSid sid p).sid = sid := by
  unfold withSid; rfl

@[simp]
private theorem finishAuthCpaSendFixedPure_msgPlain_irrel {S : Setup} (fresh isIdealSend : Bool)
    (p : AuthCpaPausePayload S) (msgPlain' : Bytes) (aeadCt : Bytes)
    (hst : AuthHybridStateFixed S) :
    finishAuthCpaSendFixedPure fresh isIdealSend { p with msgPlain := msgPlain' } aeadCt hst =
      finishAuthCpaSendFixedPure fresh isIdealSend p aeadCt hst := rfl

private theorem finishAuthCpaSendFixedPure_usedSendSessions {S : Setup} (fresh isIdealSend : Bool)
    (p : AuthCpaPausePayload S) (aeadCt : Bytes) (hst : AuthHybridStateFixed S) :
    (finishAuthCpaSendFixedPure fresh isIdealSend p aeadCt
      hst).2.toAuthHybridState.base.usedSendSessions =
      p.sid :: hst.toAuthHybridState.base.usedSendSessions := rfl

private theorem prepAuthCpaSendFixedPrim_map_sid (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    (Option.map
      (fun (p : Bool × Bool × AuthCpaPausePayload S) => (p.1, p.2.1, withSid sid p.2.2))) <$>
      prepAuthCpaSendFixedPrim S sid u bundle m0 m1 hst =
    prepAuthCpaSendFixedPrim S sid u bundle m0 m1 hst := by
  unfold prepAuthCpaSendFixedPrim withSid; dsimp only
  cases hst.toAuthHybridState.base.principals.find? (fun (i, _) => i == u.val) with
  | none => rfl
  | some up =>
    rcases up with ⟨_, uEntry⟩; dsimp only
    rw [map_bind]; apply bind_congr; intro peerPrincipal?
    rcases peerPrincipal? with _ | ⟨_, pEntry⟩ <;> {
      dsimp only; split
      · rfl
      · rw [map_bind]; apply bind_congr; intro koskOk; split
        · rfl
        · repeat (rw [map_bind]; apply bind_congr; intro _)
          split
          · rfl
          · rw [map_bind]; apply bind_congr; intro kemRes
            cases kemRes with
            | none => rfl
            | some kemPair =>
              rcases kemPair with ⟨ss, kemCt⟩; dsimp only
              repeat (rw [map_bind]; apply bind_congr; intro _)
              split <;> rfl }

private def setUsedSend {S : Setup} (u : List (SessionId S)) (hst : AuthHybridStateFixed S) :
    AuthHybridStateFixed S :=
  { hst with toAuthHybridState :=
    { hst.toAuthHybridState with base :=
      { hst.toAuthHybridState.base with usedSendSessions := u } } }

private theorem stepAuthCpaNonSendPrim_map_setUsedSend1Key (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    Prod.map id (setUsedSend hst.toAuthHybridState.base.usedSendSessions) <$>
      stepAuthCpaNonSendPrim1Key S q hst =
    stepAuthCpaNonSendPrim1Key S q hst := by
  unfold stepAuthCpaNonSendPrim1Key
  cases q with
  | recvOPK k j o msg =>
    dsimp only; split
    · rfl
    · split
      · rfl
      · rw [map_bind]; apply bind_congr; intro senderOk; split
        · rfl
        · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none => rfl
          | some kp =>
            rcases kp with ⟨_, kEntry⟩
            cases hst.toAuthHybridState.base.spkBundles.find?
                (fun (idx, _) => idx == (k.val, j.val)) with
            | none => rfl
            | some bp =>
              rcases bp with ⟨_, bEntry⟩
              cases hst.toAuthHybridState.base.opkEntries.find?
                  (fun (idx, _) => idx == (k.val, j.val, o.val)) with
              | none => rfl
              | some op =>
                rcases op with ⟨_, oEntry⟩; dsimp only; split
                · rfl
                · rw [map_bind]; apply bind_congr; intro isCanEk
                  rw [map_bind]; apply bind_congr; intro isCanEph; split
                  · rfl
                  · rw [map_bind]; apply bind_congr; intro ss?
                    cases ss? with
                    | none => rfl
                    | some ss =>
                      dsimp only; repeat (rw [map_bind]; apply bind_congr; intro _)
                      split
                      · rw [map_bind]; apply bind_congr; intro _; rfl
                      · rfl
  | recvNoOPK k j l msg =>
    dsimp only; split
    · rfl
    · split
      · rfl
      · rw [map_bind]; apply bind_congr; intro senderOk; split
        · rfl
        · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none => rfl
          | some kp =>
            rcases kp with ⟨_, kEntry⟩
            cases hst.toAuthHybridState.base.spkBundles.find?
                (fun (idx, _) => idx == (k.val, j.val)) with
            | none => rfl
            | some bp =>
              rcases bp with ⟨_, bEntry⟩; dsimp only
              rw [map_bind]; apply bind_congr; intro isCanEk
              rw [map_bind]; apply bind_congr; intro isCanEph; split
              · rfl
              · rw [map_bind]; apply bind_congr; intro ss?
                cases ss? with
                | none => rfl
                | some ss =>
                  dsimp only; repeat (rw [map_bind]; apply bind_congr; intro _)
                  split
                  · rw [map_bind]; apply bind_congr; intro _; rfl
                  · rfl
  | initPrin u | genOPK u _ _ | registerKey _ | roQuery _ | roRootQuery _ _ =>
    unfold stepAuthOtherPrim1Key; dsimp only; split
    · rfl
    · repeat (rw [map_bind]; apply bind_congr; intro _)
      rfl
  | corruptIK u =>
    unfold stepAuthOtherPrim1Key; dsimp only
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) <;> rfl
  | genSPK u j =>
    unfold stepAuthOtherPrim1Key; dsimp only; split
    · rfl
    · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some up =>
        rcases up with ⟨_, _⟩; dsimp only; repeat (rw [map_bind]; apply bind_congr; intro _)
        rfl
  | revealDhSecrets => unfold stepAuthOtherPrim1Key; dsimp only; split <;> rfl
  | sendOPK _ _ _ _ _ | sendNoOPK _ _ _ _ _ => rfl

private theorem stepAuthCpaNonSendPrim_usedSendSessions1Key (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    {p : AuthResponse × AuthHybridStateFixed S}
    (hp : p ∈ support (stepAuthCpaNonSendPrim1Key S q hst)) :
    p.2.toAuthHybridState.base.usedSendSessions =
      hst.toAuthHybridState.base.usedSendSessions := by
  rw [← stepAuthCpaNonSendPrim_map_setUsedSend1Key S q hst, support_map] at hp
  rcases hp with ⟨y, _, rfl⟩; rfl

private theorem tryPauseAuthCpaSendFixedPrim_subset_usedSend
    (allowPause : Bool) (cut : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) {p : AuthResponse × AuthHybridStateFixed S}
    (hp : Sum.inl p ∈
      support (tryPauseAuthCpaSendFixedPrim allowPause cut S sid u bundle m0 m1 hst)) :
    hst.toAuthHybridState.base.usedSendSessions ⊆
      p.2.toAuthHybridState.base.usedSendSessions := by
  unfold tryPauseAuthCpaSendFixedPrim at hp; dsimp only at hp; split at hp
  · simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hp
    subst hp; exact List.Subset.refl _
  · split at hp
    · simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hp
      subst hp; exact List.Subset.refl _
    · rw [MonadAttach.mem_support_bind] at hp; rcases hp with ⟨prep?, _, hp⟩
      cases prep? with
      | none =>
        simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hp
        subst hp; exact List.Subset.refl _
      | some pair =>
        rcases pair with ⟨isFreshPeer, isIdealSend, rawP⟩; dsimp only at hp; split at hp
        · split at hp
          · simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at hp
          · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff,
              Sum.inl.injEq] at hp
            rcases hp with ⟨_, _, _, _, rfl⟩
            rw [finishAuthCpaSendFixedPure_usedSendSessions]; exact List.subset_cons_self _ _
        · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff,
            Sum.inl.injEq] at hp
          rcases hp with ⟨_, _, _, _, rfl⟩
          rw [finishAuthCpaSendFixedPure_usedSendSessions]; exact List.subset_cons_self _ _

private theorem stepAuthCpaCutoffPrim_subset_usedSend1Key (cut : Nat) (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    {p : AuthResponse × AuthHybridStateFixed S}
    (hp : p ∈ support (stepAuthCpaCutoffPrim1Key cut S q hst)) :
    hst.toAuthHybridState.base.usedSendSessions ⊆
      p.2.toAuthHybridState.base.usedSendSessions := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim1Key at hp; dsimp only at hp; split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact List.Subset.refl _
    · unfold runAuthSendCpaCutoffPrim at hp; rw [MonadAttach.mem_support_bind] at hp
      rcases hp with ⟨res, hres, hp⟩
      cases res with
      | inl _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp
        exact tryPauseAuthCpaSendFixedPrim_subset_usedSend false cut S (.sendOPK u i) u bundle m0 m1 hst hres
      | inr _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact List.Subset.refl _
  | sendNoOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim1Key at hp; dsimp only at hp; split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact List.Subset.refl _
    · unfold runAuthSendCpaCutoffPrim at hp; rw [MonadAttach.mem_support_bind] at hp
      rcases hp with ⟨res, hres, hp⟩
      cases res with
      | inl _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp
        exact tryPauseAuthCpaSendFixedPrim_subset_usedSend false cut S (.sendNoOPK u i) u bundle m0 m1 hst hres
      | inr _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact List.Subset.refl _
  | _ => rw [stepAuthCpaNonSendPrim_usedSendSessions1Key S _ hst hp]

private theorem tryPauseAuthCpaSendFixedPrim_false_eq_of_mem_usedSend
    (idx cut : Nat) (S : Setup) (sid sid' : SessionId S)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hSid : initSessionSlotIdx sid = idx) (hLt : idx < S.N_send_tot)
    (hCut : ∀ sIdx, sIdx ≠ idx → decide (sIdx < idx) = decide (sIdx < cut))
    (hMem : sid ∈ hst.toAuthHybridState.base.usedSendSessions) :
    tryPauseAuthCpaSendFixedPrim false idx S sid' u bundle m0 m1 hst =
      tryPauseAuthCpaSendFixedPrim false cut S sid' u bundle m0 m1 hst := by
  unfold tryPauseAuthCpaSendFixedPrim; dsimp only; split
  · rfl
  · split
    · rfl
    · rename_i hNotCont
      have hNeSid : sid' ≠ sid := fun hEq => hNotCont (List.contains_iff_mem.mpr (hEq ▸ hMem))
      have hNeIdx : initSessionSlotIdx sid' ≠ idx := fun hEq =>
        hNeSid (initSessionSlotIdx_inj_of_lt (hEq.trans hSid.symm) (hSid.symm ▸ hLt))
      rw [hCut (initSessionSlotIdx sid') hNeIdx]; simp only [Bool.false_and]

private theorem stepAuthCpaCutoffPrim_eq_of_mem_usedSend1Key
    (idx cut : Nat) (S : Setup) (sid : SessionId S) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    (hSid : initSessionSlotIdx sid = idx) (hLt : idx < S.N_send_tot)
    (hCut : ∀ sIdx, sIdx ≠ idx → decide (sIdx < idx) = decide (sIdx < cut))
    (hMem : sid ∈ hst.toAuthHybridState.base.usedSendSessions) :
    stepAuthCpaCutoffPrim1Key idx S q hst = stepAuthCpaCutoffPrim1Key cut S q hst := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim1Key runAuthSendCpaCutoffPrim; dsimp only; split
    · rfl
    · rw [tryPauseAuthCpaSendFixedPrim_false_eq_of_mem_usedSend
        idx cut S sid (.sendOPK u i) u bundle m0 m1 hst hSid hLt hCut hMem]
  | sendNoOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim1Key runAuthSendCpaCutoffPrim; dsimp only; split
    · rfl
    · rw [tryPauseAuthCpaSendFixedPrim_false_eq_of_mem_usedSend
        idx cut S sid (.sendNoOPK u i) u bundle m0 m1 hst hSid hLt hCut hMem]
  | _ => rfl

private theorem runWithPrimStep_stepAuthCpaCutoffPrim_eq_of_mem_usedSend1Key
    (idx cut : Nat) (S : Setup) (sid : SessionId S) {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α)
    (hst : AuthHybridStateFixed S)
    (hSid : initSessionSlotIdx sid = idx) (hLt : idx < S.N_send_tot)
    (hCut : ∀ sIdx, sIdx ≠ idx → decide (sIdx < idx) = decide (sIdx < cut))
    (hMem : sid ∈ hst.toAuthHybridState.base.usedSendSessions) :
    runWithPrimStep (stepAuthCpaCutoffPrim1Key idx S) mx hst =
      runWithPrimStep (stepAuthCpaCutoffPrim1Key cut S) mx hst := by
  induction mx using OracleComp.inductionOn generalizing hst with
  | pure x => rfl
  | query_bind q cont ih =>
    cases q with
    | inl n =>
      rw [runWithPrimStep_query_inl, runWithPrimStep_query_inl]
      congr 1; funext u; exact ih u hst hMem
    | inr gq =>
      rw [runWithPrimStep_query_inr, runWithPrimStep_query_inr,
          stepAuthCpaCutoffPrim_eq_of_mem_usedSend1Key idx cut S sid gq hst hSid hLt hCut hMem]
      exact bind_congr_of_mem_support_spec (stepAuthCpaCutoffPrim1Key cut S gq hst) _ _
        (fun p hp => ih p.1 p.2 (stepAuthCpaCutoffPrim_subset_usedSend1Key cut S gq hst hp hMem))

/-- Session-cutoff `Auth` experiment over `PrimBaseSpec` (`cut = 0` encrypts `m1` on all fresh
    challenge sessions; `cut = S.N_send_tot` encrypts `m0` on all fresh challenge sessions). -/
noncomputable def authCpaCutoffExp1Key (cut : Nat) (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp Bool :=
  simulateQ (primBaseImpl P) do
    let (b', finalSt) ←
      runWithPrimStep (stepAuthCpaCutoffPrim1Key cut S) A.run (AuthHybridStateFixed.empty S true)
    finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState

noncomputable def cpaAfterStepUntil1Key (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (fuel : Nat) : AuthCpaPauseResult S Bool → ProbComp Bool
  | .done b' hst =>
    simulateQ (primBaseImpl P) (finalizeAeadCpaGameNoAuthPrim S b' hst.toAuthHybridState)
  | .paused ad m0 m1 p hst cont => do
    let mk ← sampleMessageKeys80
    let (adOut, m0Out, m1Out) :=
      if m0.length == m1.length then (ad, m0, m1) else ([], [0], [0])
    let ct := P.aeadEnc mk adOut (if secb then m1Out else m0Out)
    let (resp, hst') := finishAuthCpaSendFixedPure true true p ct hst
    let (b', finalSt) ← simulateQ (primBaseImpl P)
      (runWithPrimStepFuel false (stepAuthCpaCutoffPrim1Key idx S) (cont resp) fuel hst')
    simulateQ (primBaseImpl P)
      (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)

/-- 1-step `IND-CPA` simulation world at fixed `(idx, secb)` before comparing `== secb`. -/
noncomputable def cpaStepWorld1Key (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (fuel : Nat) (A : AuthAdversary S) : ProbComp Bool :=
  simulateQ (primBaseImpl P)
    (stepUntilAuthCpaChallengeFixedPrim1Key idx S false A.run fuel
      (AuthHybridStateFixed.empty S true)) >>=
    cpaAfterStepUntil1Key idx S P secb fuel

private theorem simulateQ_tryPause_and_cpaAfter_eq1Key
    (idx : Nat) (S : Setup) (P : Primitives) (secb : Bool) (hLt : idx < S.N_send_tot)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (cont : AuthResponse → OracleComp (unifSpec + authSpec S) Bool)
    (Q' fuel1' fuel2 : Nat)
    (h_cont : ∀ r, IsQueryBoundP (cont r) (fun q => isGameQuery q = true) Q') (h2 : Q' ≤ fuel2)
    (ih : ∀ r s',
      (simulateQ (primBaseImpl P)
        (stepUntilAuthCpaChallengeFixedPrim1Key idx S false (cont r) fuel1' s') >>=
        cpaAfterStepUntil1Key idx S P secb fuel2) =
      (simulateQ (primBaseImpl P)
        (runWithPrimStep (stepAuthCpaCutoffPrim1Key (if secb then idx else idx + 1) S) (cont r) s') >>=
        fun (b', finalSt) =>
          simulateQ (primBaseImpl P)
            (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState))) :
    (simulateQ (primBaseImpl P)
      (do
        let stepRes ← tryPauseAuthCpaSendFixedPrim true idx S sid u bundle m0 m1 hst
        match stepRes with
        | .inl (resp, s') => stepUntilAuthCpaChallengeFixedPrim1Key idx S false (cont resp) fuel1' s'
        | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
      cpaAfterStepUntil1Key idx S P secb fuel2) =
    (simulateQ (primBaseImpl P)
      (runAuthSendCpaCutoffPrim (if secb then idx else idx + 1) S sid u bundle m0 m1 hst >>=
        fun p => runWithPrimStep
          (stepAuthCpaCutoffPrim1Key (if secb then idx else idx + 1) S) (cont p.1) p.2) >>=
      fun (b', finalSt) =>
        simulateQ (primBaseImpl P)
          (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)) := by
  have hCut : ∀ sIdx, sIdx ≠ idx →
      decide (sIdx < idx) = decide (sIdx < if secb then idx else idx + 1) := by
    intro sIdx hNe; cases secb <;> simp; omega
  unfold runAuthSendCpaCutoffPrim tryPauseAuthCpaSendFixedPrim; dsimp only
  by_cases hLen : (m0.length != m1.length) = true
  · simp only [hLen, ↓reduceIte, pure_bind]; exact ih .noneResp hst
  · have hLenEq : (m0.length == m1.length) = true := by revert hLen; simp
    simp only [hLen, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid = true
    · simp only [hUsed, ↓reduceIte, pure_bind]; exact ih .noneResp hst
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      rw [← prepAuthCpaSendFixedPrim_map_sid S sid u bundle m0 m1 hst]
      simp only [map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, bind_assoc, pure_bind]
      apply bind_congr; intro prep?
      cases prep? with
      | none => simp only [Option.map_none, simulateQ_pure, pure_bind]; exact ih .noneResp hst
      | some pair =>
        rcases pair with ⟨isFreshPeer, isIdealSend, rawP⟩; simp only [Option.map_some]
        by_cases hFresh : isFreshPeer = true
        · simp only [hFresh, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.false_eq_true]
          by_cases hIdx : (initSessionSlotIdx sid == idx) = true
          · have hsIdx : initSessionSlotIdx sid = idx := beq_iff_eq.mp hIdx
            have hPlain :
                (if decide (initSessionSlotIdx sid < if secb = true then idx else idx + 1) = true
                 then m0 else m1) = (if secb = true then m1 else m0) := by
              rw [hsIdx]; cases secb <;> simp
            simp only [hIdx, ↓reduceIte, simulateQ_pure, pure_bind, cpaAfterStepUntil1Key,
              hLenEq, simulateQ_bind, simulateQ_embedUnif, bind_assoc,
              finishAuthCpaSendFixedPure_msgPlain_irrel]
            apply bind_congr; intro mk
            simp only [hPlain, simulateQ_primQ_aeadEnc_bytes, pure_bind]
            let fin := finishAuthCpaSendFixedPure true true (withSid sid rawP)
              (P.aeadEnc mk (withSid sid rawP).ad (if secb = true then m1 else m0)) hst
            have hMemSid : sid ∈ fin.2.toAuthHybridState.base.usedSendSessions := by
              rw [finishAuthCpaSendFixedPure_usedSendSessions, withSid_sid]; exact List.mem_cons_self
            have hFuel := runWithPrimStepFuel_eq_runWithPrimStep false
              (stepAuthCpaCutoffPrim1Key idx S) (cont fin.1) Q' fuel2 (h_cont _) h2 fin.2
            have hPost := runWithPrimStep_stepAuthCpaCutoffPrim_eq_of_mem_usedSend1Key
              idx (if secb = true then idx else idx + 1) S sid (cont fin.1) fin.2
              hsIdx hLt hCut hMemSid
            rw [hFuel, hPost]
          · have hCutSid := hCut (initSessionSlotIdx sid)
              (beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hIdx))
            simp only [hIdx, Bool.false_eq_true, ↓reduceIte,
              simulateQ_bind, simulateQ_embedUnif, bind_assoc]
            apply bind_congr; intro mk; rw [hCutSid]; apply bind_congr; intro aeadCt
            simp only [simulateQ_pure, pure_bind]; exact ih _ _
        · simp only [hFresh, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, bind_assoc]
          apply bind_congr; intro mk; apply bind_congr; intro aeadCt
          simp only [simulateQ_pure, pure_bind]; exact ih _ _

theorem simulateQ_stepUntil_and_cpaAfter_eq_cutoff1Key (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (hLt : idx < S.N_send_tot)
    (mx : OracleComp (unifSpec + authSpec S) Bool)
    (Q fuel1 fuel2 : Nat)
    (h_mx : IsQueryBoundP mx (fun q => isGameQuery q = true) Q)
    (h1 : Q ≤ fuel1) (h2 : Q ≤ fuel2)
    (hst : AuthHybridStateFixed S) :
    (simulateQ (primBaseImpl P) (stepUntilAuthCpaChallengeFixedPrim1Key idx S false mx fuel1 hst) >>=
      cpaAfterStepUntil1Key idx S P secb fuel2) =
    (simulateQ (primBaseImpl P)
      (runWithPrimStep (stepAuthCpaCutoffPrim1Key (if secb then idx else idx + 1) S) mx hst) >>=
      fun (b', finalSt) =>
        simulateQ (primBaseImpl P)
          (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)) := by
  induction mx using OracleComp.inductionOn generalizing Q fuel1 hst with
  | pure x =>
    rw [stepUntilAuthCpaChallengeFixedPrim_pure1Key, runWithPrimStep_pure]
    simp [cpaAfterStepUntil1Key]
  | query_bind q cont ih =>
    rw [isQueryBoundP_query_bind_iff] at h_mx
    cases q with
    | inl n =>
      rcases h_mx with ⟨_, h_cont⟩
      have hnl : ¬ (isGameQuery (Sum.inl n : ℕ ⊕ AuthQuery S) = true) := by simp [isGameQuery]
      simp only [hnl] at h_cont
      rw [stepUntilAuthCpaChallengeFixedPrim_query_inl1Key, runWithPrimStep_query_inl]
      simp only [simulateQ_bind, bind_assoc]
      congr 1; funext u
      exact ih u Q fuel1 (h_cont u) h1 h2 hst
    | inr gq =>
      rcases h_mx with ⟨h_first, h_cont⟩
      have hgr : isGameQuery (Sum.inr gq : ℕ ⊕ AuthQuery S) = true := rfl
      rcases h_first with h_abs | hQpos
      · exfalso; exact h_abs hgr
      · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
        obtain ⟨fuel1', rfl⟩ : ∃ fuel1', fuel1 = fuel1' + 1 := ⟨fuel1 - 1, by omega⟩
        simp only [hgr, ↓reduceIte, Nat.add_sub_cancel] at h_cont
        rw [runWithPrimStep_query_inr]
        cases gq with
        | sendOPK u i bundle m0 m1 =>
          change (simulateQ (primBaseImpl P)
            (if bundle.opkB?.isNone then
               stepUntilAuthCpaChallengeFixedPrim1Key idx S false (cont .noneResp) fuel1' hst
             else do
               let stepRes ←
                 tryPauseAuthCpaSendFixedPrim true idx S (.sendOPK u i) u bundle m0 m1 hst
               match stepRes with
               | .inl (resp, s') =>
                 stepUntilAuthCpaChallengeFixedPrim1Key idx S false (cont resp) fuel1' s'
               | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
            cpaAfterStepUntil1Key idx S P secb fuel2) = _
          unfold stepAuthCpaCutoffPrim1Key
          dsimp only
          split
          · exact ih .noneResp Q' fuel1' (h_cont .noneResp) (by omega) (by omega) hst
          · exact simulateQ_tryPause_and_cpaAfter_eq1Key idx S P secb hLt
              (.sendOPK u i) u bundle m0 m1 hst cont Q' fuel1' fuel2 h_cont (by omega)
              (fun r s' => ih r Q' fuel1' (h_cont r) (by omega) (by omega) s')
        | sendNoOPK u i bundle m0 m1 =>
          change (simulateQ (primBaseImpl P)
            (if bundle.opkB?.isSome then
               stepUntilAuthCpaChallengeFixedPrim1Key idx S false (cont .noneResp) fuel1' hst
             else do
               let stepRes ←
                 tryPauseAuthCpaSendFixedPrim true idx S (.sendNoOPK u i) u bundle m0 m1 hst
               match stepRes with
               | .inl (resp, s') =>
                 stepUntilAuthCpaChallengeFixedPrim1Key idx S false (cont resp) fuel1' s'
               | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
            cpaAfterStepUntil1Key idx S P secb fuel2) = _
          unfold stepAuthCpaCutoffPrim1Key
          dsimp only
          split
          · exact ih .noneResp Q' fuel1' (h_cont .noneResp) (by omega) (by omega) hst
          · exact simulateQ_tryPause_and_cpaAfter_eq1Key idx S P secb hLt
              (.sendNoOPK u i) u bundle m0 m1 hst cont Q' fuel1' fuel2 h_cont (by omega)
              (fun r s' => ih r Q' fuel1' (h_cont r) (by omega) (by omega) s')
        | _ =>
          change (simulateQ (primBaseImpl P)
            (stepAuthCpaNonSendPrim1Key S _ hst >>=
              fun p => stepUntilAuthCpaChallengeFixedPrim1Key idx S false (cont p.1) fuel1' p.2) >>=
            cpaAfterStepUntil1Key idx S P secb fuel2) = _
          dsimp only [stepAuthCpaCutoffPrim1Key]; simp only [simulateQ_bind, bind_assoc]
          congr 1; funext p; exact ih p.1 Q' fuel1' (h_cont p.1) (by omega) (by omega) p.2

theorem cpaStepWorld_eq_authCpaCutoffExp1Key (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (hLt : idx < S.N_send_tot)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    cpaStepWorld1Key idx S P secb b.q_total A.1 =
      authCpaCutoffExp1Key (if secb then idx else idx + 1) S P A.1 := by
  unfold cpaStepWorld1Key authCpaCutoffExp1Key
  rw [simulateQ_stepUntil_and_cpaAfter_eq_cutoff1Key idx S P secb hLt
    A.1.run b.q_total b.q_total b.q_total (SignalPqxdh.QueryBounded.auth_total A.property) (le_refl _) (le_refl _)
    (AuthHybridStateFixed.empty S true), simulateQ_bind]

private theorem tryPauseAuthCpaSendSlotPrim_ns_bounds (cut : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : AuthCpaSlotState S)
    {r : Sum (AuthResponse × AuthCpaSlotState S)
         (Bytes × Bytes × Bytes × AuthCpaPausePayload S × AuthCpaSlotState S)}
    (hr : r ∈ support (tryPauseAuthCpaSendSlotPrim false cut S sid u bundle m0 m1 shst)) :
    match r with
    | .inl (_, s') => shst.1 ≤ s'.1 ∧ s'.1 ≤ shst.1 + 1
    | .inr (_, _, _, _, s') => shst.1 ≤ s'.1 ∧ s'.1 ≤ shst.1 + 1 := by
  rcases shst with ⟨ns, hst⟩
  unfold tryPauseAuthCpaSendSlotPrim at hr; dsimp only at hr
  split at hr
  · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; exact ⟨le_rfl, Nat.le_succ ns⟩
  · split at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; exact ⟨le_rfl, Nat.le_succ ns⟩
    · rw [MonadAttach.mem_support_bind] at hr; rcases hr with ⟨prep?, _, hr⟩
      cases prep? with
      | none =>
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨le_rfl, Nat.le_succ ns⟩
      | some pair =>
        rcases pair with ⟨isFreshPeer, isIdealSend, rawP⟩
        cases isFreshPeer
        · simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
            support_pure, Set.mem_singleton_iff] at hr
          rcases hr with ⟨_, _, _, _, rfl⟩; exact ⟨le_rfl, Nat.le_succ ns⟩
        · simp only [↓reduceIte, Bool.false_and, Bool.false_eq_true, MonadAttach.mem_support_bind,
            support_pure, Set.mem_singleton_iff] at hr
          rcases hr with ⟨_, _, _, _, rfl⟩; exact ⟨Nat.le_succ ns, le_rfl⟩

private theorem stepAuthCpaCutoffSlotPrim_ns_bounds1Key (cut : Nat) (S : Setup)
    (gq : AuthQuery S) (shst : AuthCpaSlotState S)
    {p : (authSpec S).Range gq × AuthCpaSlotState S}
    (hp : p ∈ support (stepAuthCpaCutoffSlotPrim1Key cut S gq shst)) :
    shst.1 ≤ p.2.1 ∧
      p.2.1 ≤ shst.1 + (if isAuthSendQuery (Sum.inr gq : ℕ ⊕ AuthQuery S) then 1 else 0) := by
  unfold stepAuthCpaCutoffSlotPrim1Key runAuthSendCpaCutoffSlotPrim at hp
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthSendQuery, ↓reduceIte]; dsimp only at hp; split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
    · rw [MonadAttach.mem_support_bind] at hp; rcases hp with ⟨res, hRes, hp⟩
      have hB := tryPauseAuthCpaSendSlotPrim_ns_bounds cut S (.sendOPK u i) u bundle m0 m1 shst hRes
      cases res with
      | inl _ => simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hB
      | inr _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthSendQuery, ↓reduceIte]; dsimp only at hp; split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
    · rw [MonadAttach.mem_support_bind] at hp; rcases hp with ⟨res, hRes, hp⟩
      have hB := tryPauseAuthCpaSendSlotPrim_ns_bounds cut S (.sendNoOPK u i) u bundle m0 m1 shst hRes
      cases res with
      | inl _ => simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hB
      | inr _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
  | _ =>
    simp only [isAuthSendQuery, ↓reduceIte, Nat.add_zero]; dsimp only at hp
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
    rcases hp with ⟨_, _, rfl⟩; exact ⟨le_rfl, le_rfl⟩

private theorem tryPauseAuthCpaSendSlotPrim_false_eq_of_le (cut1 cut2 : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : AuthCpaSlotState S) (h1 : cut1 ≤ shst.1) (h2 : cut2 ≤ shst.1) :
    tryPauseAuthCpaSendSlotPrim false cut1 S sid u bundle m0 m1 shst =
      tryPauseAuthCpaSendSlotPrim false cut2 S sid u bundle m0 m1 shst := by
  rcases shst with ⟨ns, hst⟩
  have hc1 : decide (ns < cut1) = false := decide_eq_false (by omega)
  have hc2 : decide (ns < cut2) = false := decide_eq_false (by omega)
  unfold tryPauseAuthCpaSendSlotPrim; dsimp only; rw [hc1, hc2]; simp only [Bool.false_and]

private theorem stepAuthCpaCutoffSlotPrim_eq_of_le1Key (cut1 cut2 : Nat) (S : Setup)
    (gq : AuthQuery S) (shst : AuthCpaSlotState S) (h1 : cut1 ≤ shst.1) (h2 : cut2 ≤ shst.1) :
    stepAuthCpaCutoffSlotPrim1Key cut1 S gq shst =
      stepAuthCpaCutoffSlotPrim1Key cut2 S gq shst := by
  unfold stepAuthCpaCutoffSlotPrim1Key runAuthSendCpaCutoffSlotPrim
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only; split
    · rfl
    · rw [tryPauseAuthCpaSendSlotPrim_false_eq_of_le cut1 cut2 S (.sendOPK u i) u bundle m0 m1 shst h1 h2]
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only; split
    · rfl
    · rw [tryPauseAuthCpaSendSlotPrim_false_eq_of_le cut1 cut2 S (.sendNoOPK u i) u bundle m0 m1 shst h1 h2]
  | _ => rfl

private theorem runWithPrimStep_stepAuthCpaCutoffSlotPrim_eq_of_le1Key
    (cut1 cut2 : Nat) (S : Setup) {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α) (shst : AuthCpaSlotState S)
    (h1 : cut1 ≤ shst.1) (h2 : cut2 ≤ shst.1) :
    runWithPrimStep (stepAuthCpaCutoffSlotPrim1Key cut1 S) mx shst =
      runWithPrimStep (stepAuthCpaCutoffSlotPrim1Key cut2 S) mx shst := by
  induction mx using OracleComp.inductionOn generalizing shst with
  | pure x => rfl
  | query_bind q cont ih =>
    cases q with
    | inl n =>
      rw [runWithPrimStep_query_inl, runWithPrimStep_query_inl]
      congr 1; funext u; exact ih u shst h1 h2
    | inr gq =>
      rw [runWithPrimStep_query_inr, runWithPrimStep_query_inr,
          stepAuthCpaCutoffSlotPrim_eq_of_le1Key cut1 cut2 S gq shst h1 h2]
      exact bind_congr_of_mem_support_spec _ _ _ (fun p hp =>
        let hLe := (stepAuthCpaCutoffSlotPrim_ns_bounds1Key cut2 S gq shst hp).1
        ih p.1 p.2 (le_trans h1 hLe) (le_trans h2 hLe))

private theorem stepUntilAuthCpaChallengeSlotPrim_pure1Key (idx : Nat) (S : Setup) {α : Type}
    (defaultVal a : α) (fuel : Nat) (shst : AuthCpaSlotState S) :
    stepUntilAuthCpaChallengeSlotPrim1Key idx S defaultVal (pure a) fuel shst =
      pure (.done a shst) := rfl

@[simp]
private theorem stepUntilAuthCpaChallengeSlotPrim_query_inl1Key (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α) (n : Nat)
    (cont : (unifSpec + authSpec S).Range (Sum.inl n) → OracleComp (unifSpec + authSpec S) α)
    (fuel : Nat) (shst : AuthCpaSlotState S) :
    stepUntilAuthCpaChallengeSlotPrim1Key idx S defaultVal
        (liftM (OracleSpec.query (Sum.inl n)) >>= cont) fuel shst =
      (liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n)) >>=
        fun u => stepUntilAuthCpaChallengeSlotPrim1Key idx S defaultVal (cont u) fuel shst) := rfl

/-- Creation-order session-cutoff `Auth` experiment over `PrimBaseSpec`. -/
noncomputable def authCpaSlotCutoffExp1Key (cut : Nat) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  simulateQ (primBaseImpl P) do
    let (b', (_, finalSt)) ←
      runWithPrimStep (stepAuthCpaCutoffSlotPrim1Key cut S) A.run
        (0, AuthHybridStateFixed.empty S true)
    finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState

noncomputable def cpaSlotAfterStepUntil1Key (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (fuel : Nat) : AuthCpaSlotPauseResult S Bool → ProbComp Bool
  | .done b' (_, hst) =>
    simulateQ (primBaseImpl P) (finalizeAeadCpaGameNoAuthPrim S b' hst.toAuthHybridState)
  | .paused ad m0 m1 p (_, hst) cont => do
    let mk ← sampleMessageKeys80
    let (adOut, m0Out, m1Out) :=
      if m0.length == m1.length then (ad, m0, m1) else ([], [0], [0])
    let ct := P.aeadEnc mk adOut (if secb then m1Out else m0Out)
    let (resp, hst') := finishAuthCpaSendFixedPure true true p ct hst
    let (b', (_, finalSt)) ← simulateQ (primBaseImpl P)
      (runWithPrimStepFuel false (stepAuthCpaCutoffSlotPrim1Key idx S) (cont resp) fuel (idx + 1, hst'))
    simulateQ (primBaseImpl P)
      (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)

/-- 1-step creation-order `IND-CPA` simulation world at fixed `(idx, secb)` before `== secb`. -/
noncomputable def cpaSlotStepWorld1Key (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (fuel : Nat) (A : AuthAdversary S) : ProbComp Bool :=
  simulateQ (primBaseImpl P)
    (stepUntilAuthCpaChallengeSlotPrim1Key idx S false A.run fuel
      (0, AuthHybridStateFixed.empty S true)) >>=
    cpaSlotAfterStepUntil1Key idx S P secb fuel

private theorem simulateQ_tryPauseSlot_and_cpaAfter_eq1Key
    (idx : Nat) (S : Setup) (P : Primitives) (secb : Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : AuthCpaSlotState S)
    (cont : AuthResponse → OracleComp (unifSpec + authSpec S) Bool)
    (Q' fuel1' fuel2 : Nat)
    (h_cont : ∀ r, IsQueryBoundP (cont r) (fun q => isGameQuery q = true) Q') (h2 : Q' ≤ fuel2)
    (ih : ∀ r s',
      (simulateQ (primBaseImpl P)
        (stepUntilAuthCpaChallengeSlotPrim1Key idx S false (cont r) fuel1' s') >>=
        cpaSlotAfterStepUntil1Key idx S P secb fuel2) =
      (simulateQ (primBaseImpl P)
        (runWithPrimStep (stepAuthCpaCutoffSlotPrim1Key (if secb then idx else idx + 1) S)
          (cont r) s') >>=
        fun (b', (_, finalSt)) =>
          simulateQ (primBaseImpl P)
            (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState))) :
    (simulateQ (primBaseImpl P)
      (do
        let stepRes ← tryPauseAuthCpaSendSlotPrim true idx S sid u bundle m0 m1 shst
        match stepRes with
        | .inl (resp, s') => stepUntilAuthCpaChallengeSlotPrim1Key idx S false (cont resp) fuel1' s'
        | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
      cpaSlotAfterStepUntil1Key idx S P secb fuel2) =
    (simulateQ (primBaseImpl P)
      (runAuthSendCpaCutoffSlotPrim (if secb then idx else idx + 1) S sid u bundle m0 m1 shst >>=
        fun p => runWithPrimStep
          (stepAuthCpaCutoffSlotPrim1Key (if secb then idx else idx + 1) S) (cont p.1) p.2) >>=
      fun (b', (_, finalSt)) =>
        simulateQ (primBaseImpl P)
          (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)) := by
  rcases shst with ⟨ns, hst⟩
  have hCut : ∀ sIdx, sIdx ≠ idx →
      decide (sIdx < idx) = decide (sIdx < if secb then idx else idx + 1) := by
    intro sIdx hNe; cases secb <;> simp; omega
  unfold runAuthSendCpaCutoffSlotPrim tryPauseAuthCpaSendSlotPrim; dsimp only
  by_cases hLen : (m0.length != m1.length) = true
  · simp only [hLen, ↓reduceIte, pure_bind]; exact ih .noneResp (ns, hst)
  · have hLenEq : (m0.length == m1.length) = true := by revert hLen; simp
    simp only [hLen, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid = true
    · simp only [hUsed, ↓reduceIte, pure_bind]; exact ih .noneResp (ns, hst)
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      rw [← prepAuthCpaSendFixedPrim_map_sid S sid u bundle m0 m1 hst]
      simp only [map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, bind_assoc, pure_bind]
      apply bind_congr; intro prep?
      cases prep? with
      | none => simp only [Option.map_none, simulateQ_pure, pure_bind]; exact ih .noneResp (ns, hst)
      | some pair =>
        rcases pair with ⟨isFreshPeer, isIdealSend, rawP⟩; simp only [Option.map_some]
        by_cases hFresh : isFreshPeer = true
        · simp only [hFresh, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.false_eq_true]
          by_cases hIdx : (ns == idx) = true
          · obtain rfl := beq_iff_eq.mp hIdx
            have hPlain :
                (if decide (ns < if secb = true then ns else ns + 1) = true then m0 else m1) =
                (if secb = true then m1 else m0) := by cases secb <;> simp
            simp only [hIdx, ↓reduceIte, simulateQ_pure, pure_bind, cpaSlotAfterStepUntil1Key,
              hLenEq, simulateQ_bind, simulateQ_embedUnif, bind_assoc,
              finishAuthCpaSendFixedPure_msgPlain_irrel]
            apply bind_congr; intro mk
            simp only [hPlain, simulateQ_primQ_aeadEnc_bytes, pure_bind]
            let fin := finishAuthCpaSendFixedPure true true (withSid sid rawP)
              (P.aeadEnc mk (withSid sid rawP).ad (if secb = true then m1 else m0)) hst
            have hFuel := runWithPrimStepFuel_eq_runWithPrimStep false
              (stepAuthCpaCutoffSlotPrim1Key ns S) (cont fin.1) Q' fuel2 (h_cont _) h2
              (ns + 1, fin.2)
            have hPost := runWithPrimStep_stepAuthCpaCutoffSlotPrim_eq_of_le1Key
              ns (if secb = true then ns else ns + 1) S (cont fin.1) (ns + 1, fin.2)
              (Nat.le_succ ns) (by cases secb <;> simp)
            rw [hFuel, hPost]
          · have hCutSid := hCut ns (beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hIdx))
            simp only [hIdx, Bool.false_eq_true, ↓reduceIte,
              simulateQ_bind, simulateQ_embedUnif, bind_assoc]
            apply bind_congr; intro mk; rw [hCutSid]; apply bind_congr; intro aeadCt
            simp only [simulateQ_pure, pure_bind]; exact ih _ _
        · simp only [hFresh, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, bind_assoc]
          apply bind_congr; intro mk; apply bind_congr; intro aeadCt
          simp only [simulateQ_pure, pure_bind]; exact ih _ _

private theorem simulateQ_stepUntilSlot_and_cpaAfter_eq_cutoff1Key
    (idx : Nat) (S : Setup) (P : Primitives) (secb : Bool)
    (mx : OracleComp (unifSpec + authSpec S) Bool) (Q fuel1 fuel2 : Nat)
    (h_mx : IsQueryBoundP mx (fun q => isGameQuery q = true) Q) (h1 : Q ≤ fuel1) (h2 : Q ≤ fuel2)
    (shst : AuthCpaSlotState S) :
    (simulateQ (primBaseImpl P)
      (stepUntilAuthCpaChallengeSlotPrim1Key idx S false mx fuel1 shst) >>=
      cpaSlotAfterStepUntil1Key idx S P secb fuel2) =
    (simulateQ (primBaseImpl P)
      (runWithPrimStep (stepAuthCpaCutoffSlotPrim1Key (if secb then idx else idx + 1) S) mx shst) >>=
      fun (b', (_, finalSt)) =>
        simulateQ (primBaseImpl P)
          (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)) := by
  induction mx using OracleComp.inductionOn generalizing Q fuel1 shst with
  | pure x =>
    rw [stepUntilAuthCpaChallengeSlotPrim_pure1Key, runWithPrimStep_pure]
    rcases shst with ⟨ns, hst⟩; simp [cpaSlotAfterStepUntil1Key]
  | query_bind q cont ih =>
    rw [isQueryBoundP_query_bind_iff] at h_mx
    cases q with
    | inl n =>
      rcases h_mx with ⟨_, h_cont⟩
      have hnl : ¬ (isGameQuery (Sum.inl n : ℕ ⊕ AuthQuery S) = true) := by simp [isGameQuery]
      simp only [hnl] at h_cont
      rw [stepUntilAuthCpaChallengeSlotPrim_query_inl1Key, runWithPrimStep_query_inl]
      simp only [simulateQ_bind, bind_assoc]
      congr 1; funext u; exact ih u Q fuel1 (h_cont u) h1 h2 shst
    | inr gq =>
      rcases h_mx with ⟨h_first, h_cont⟩
      have hgr : isGameQuery (Sum.inr gq : ℕ ⊕ AuthQuery S) = true := rfl
      rcases h_first with h_abs | hQpos
      · exfalso; exact h_abs hgr
      · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
        obtain ⟨fuel1', rfl⟩ : ∃ fuel1', fuel1 = fuel1' + 1 := ⟨fuel1 - 1, by omega⟩
        simp only [hgr, ↓reduceIte, Nat.add_sub_cancel] at h_cont
        rw [runWithPrimStep_query_inr]
        cases gq with
        | sendOPK u i bundle m0 m1 =>
          change (simulateQ (primBaseImpl P)
            (if bundle.opkB?.isNone then
               stepUntilAuthCpaChallengeSlotPrim1Key idx S false (cont .noneResp) fuel1' shst
             else do
               let stepRes ←
                 tryPauseAuthCpaSendSlotPrim true idx S (.sendOPK u i) u bundle m0 m1 shst
               match stepRes with
               | .inl (resp, s') =>
                 stepUntilAuthCpaChallengeSlotPrim1Key idx S false (cont resp) fuel1' s'
               | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
            cpaSlotAfterStepUntil1Key idx S P secb fuel2) = _
          unfold stepAuthCpaCutoffSlotPrim1Key; dsimp only; split
          · exact ih .noneResp Q' fuel1' (h_cont .noneResp) (by omega) (by omega) shst
          · exact simulateQ_tryPauseSlot_and_cpaAfter_eq1Key idx S P secb
              (.sendOPK u i) u bundle m0 m1 shst cont Q' fuel1' fuel2 h_cont (by omega)
              (fun r s' => ih r Q' fuel1' (h_cont r) (by omega) (by omega) s')
        | sendNoOPK u i bundle m0 m1 =>
          change (simulateQ (primBaseImpl P)
            (if bundle.opkB?.isSome then
               stepUntilAuthCpaChallengeSlotPrim1Key idx S false (cont .noneResp) fuel1' shst
             else do
               let stepRes ←
                 tryPauseAuthCpaSendSlotPrim true idx S (.sendNoOPK u i) u bundle m0 m1 shst
               match stepRes with
               | .inl (resp, s') =>
                 stepUntilAuthCpaChallengeSlotPrim1Key idx S false (cont resp) fuel1' s'
               | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
            cpaSlotAfterStepUntil1Key idx S P secb fuel2) = _
          unfold stepAuthCpaCutoffSlotPrim1Key; dsimp only; split
          · exact ih .noneResp Q' fuel1' (h_cont .noneResp) (by omega) (by omega) shst
          · exact simulateQ_tryPauseSlot_and_cpaAfter_eq1Key idx S P secb
              (.sendNoOPK u i) u bundle m0 m1 shst cont Q' fuel1' fuel2 h_cont (by omega)
              (fun r s' => ih r Q' fuel1' (h_cont r) (by omega) (by omega) s')
        | _ =>
          change (simulateQ (primBaseImpl P)
            (stepAuthCpaNonSendPrim1Key S _ shst.2 >>=
              fun p =>
                stepUntilAuthCpaChallengeSlotPrim1Key idx S false (cont p.1) fuel1' (shst.1, p.2)) >>=
            cpaSlotAfterStepUntil1Key idx S P secb fuel2) = _
          dsimp only [stepAuthCpaCutoffSlotPrim1Key]
          simp only [simulateQ_bind, bind_assoc, pure_bind]
          congr 1; funext p; exact ih p.1 Q' fuel1' (h_cont p.1) (by omega) (by omega) (shst.1, p.2)

private theorem cpaSlotStepWorld_eq_authCpaSlotCutoffExp1Key (idx : Nat) (S : Setup)
    (P : Primitives) (secb : Bool) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    cpaSlotStepWorld1Key idx S P secb b.q_total A.1 =
      authCpaSlotCutoffExp1Key (if secb then idx else idx + 1) S P A.1 := by
  unfold cpaSlotStepWorld1Key authCpaSlotCutoffExp1Key
  rw [simulateQ_stepUntilSlot_and_cpaAfter_eq_cutoff1Key idx S P secb
    A.1.run b.q_total b.q_total b.q_total (SignalPqxdh.QueryBounded.auth_total A.property) (le_refl _) (le_refl _)
    (0, AuthHybridStateFixed.empty S true), simulateQ_bind]

private theorem evalDist_cpaSlotInner_eq_cpaSlotAfterStepUntil1Key
    (idx : Nat) (S : Setup) (P : Primitives) (secb : Bool) (fuel : Nat)
    (res : AuthCpaSlotPauseResult S Bool) :
    𝒟[(do
      let mk ← sampleMessageKeys80
      let (ad, m0, m1, res') ←
        simulateQ (primBaseImpl P)
          (match res with
           | .paused ad m0 m1 _ _ _ =>
             if m0.length == m1.length then pure (ad, m0, m1, res)
             else pure ([], [0], [0], res)
           | .done _ _ => pure ([], [0], [0], res))
      if m0.length != m1.length then do let coin ← $ᵗ Bool; return coin
      let ct := P.aeadEnc mk ad (if secb then m1 else m0)
      let b' ← simulateQ (primBaseImpl P)
        (resumeAuthCpaAfterChallengeSlotPrim1Key idx S fuel res' (some ct))
      return (b' == secb))] =
    𝒟[cpaSlotAfterStepUntil1Key idx S P secb fuel res >>= fun z => pure (z == secb)] := by
  cases res with
  | done b' shst =>
    rcases shst with ⟨ns, hst⟩
    simp only [simulateQ_pure, pure_bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      resumeAuthCpaAfterChallengeSlotPrim1Key, cpaSlotAfterStepUntil1Key,
      OracleComp.evalDist_bind_const]
  | paused ad m0 m1 p shst cont =>
    rcases shst with ⟨ns, hst⟩
    by_cases hLen : (m0.length == m1.length) = true
    · have hBne : (m0.length != m1.length) = false := by revert hLen; simp
      simp only [hLen, hBne, ↓reduceIte, Bool.false_eq_true, simulateQ_pure, pure_bind,
        resumeAuthCpaAfterChallengeSlotPrim1Key, cpaSlotAfterStepUntil1Key, Option.getD_some,
        simulateQ_bind, bind_assoc]
    · have hLenF : (m0.length == m1.length) = false := Bool.eq_false_iff.mpr hLen
      simp only [hLenF, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, pure_bind,
        bne_self_eq_false, resumeAuthCpaAfterChallengeSlotPrim1Key, cpaSlotAfterStepUntil1Key,
        Option.getD_some, simulateQ_bind, bind_assoc]

theorem evalDist_aeadIndCpaExp_aeadCpaReductionAuthFixed_eq1Key
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[aeadIndCpaExp P (aeadCpaReductionAuthFixed1Key S b A)] =
      𝒟[(do
        let secb ← $ᵗ Bool
        let z ← if secb then
          (sampleIndexRange (min b.q_total S.N_send_tot) >>=
            fun idx => cpaSlotStepWorld1Key idx S P true b.q_total A.1)
        else
          (sampleIndexRange (min b.q_total S.N_send_tot) >>=
            fun idx => cpaSlotStepWorld1Key idx S P false b.q_total A.1)
        return (secb == z))] := by
  unfold aeadIndCpaExp aeadCpaReductionAuthFixed1Key aeadCpaReductionAuthSlotChoose1Key
    aeadCpaReductionAuthSlotAtChoose1Key aeadCpaReductionAuthSlotDist1Key cpaSlotStepWorld1Key
    BoundedAdv at *
  dsimp only
  simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  rw [OracleComp.evalDist_bind_bind_swap sampleMessageKeys80
    (sampleIndexRange (min b.q_total S.N_send_tot))]
  trans 𝒟[(sampleIndexRange (min b.q_total S.N_send_tot) >>= fun idx =>
      simulateQ (primBaseImpl P)
        (stepUntilAuthCpaChallengeSlotPrim1Key idx S false A.1.run b.q_total
          (0, AuthHybridStateFixed.empty S true)) >>= fun res =>
        cpaSlotAfterStepUntil1Key idx S P secb b.q_total res >>= fun z => pure (z == secb))]
  · refine OracleComp.evalDist_bind_congr_of_support
      (sampleIndexRange (min b.q_total S.N_send_tot)) _ _ (fun idx _ => ?_)
    rw [OracleComp.evalDist_bind_bind_swap sampleMessageKeys80
      (simulateQ (primBaseImpl P)
        (stepUntilAuthCpaChallengeSlotPrim1Key idx S false A.1.run b.q_total
          (0, AuthHybridStateFixed.empty S true)))]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun res _ => ?_)
    exact evalDist_cpaSlotInner_eq_cpaSlotAfterStepUntil1Key idx S P secb b.q_total res
  · cases secb <;> simp [Bool.beq_comm]

private theorem map_snd_runAuthSendCpaCutoffSlotPrim_of_decide_eq
    (cutS cutF : Nat) (S : Setup) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (m0 m1 : Bytes) (shst : AuthCpaSlotState S)
    (hDec : decide (shst.1 < cutS) = decide (initSessionSlotIdx sid < cutF)) :
    Prod.map id Prod.snd <$> runAuthSendCpaCutoffSlotPrim cutS S sid u bundle m0 m1 shst =
      runAuthSendCpaCutoffPrim cutF S sid u bundle m0 m1 shst.2 := by
  rcases shst with ⟨ns, hst⟩; dsimp only at hDec ⊢
  unfold runAuthSendCpaCutoffSlotPrim runAuthSendCpaCutoffPrim
    tryPauseAuthCpaSendSlotPrim tryPauseAuthCpaSendFixedPrim
  dsimp only; split
  · simp [Prod.map]
  · split
    · simp [Prod.map]
    · rw [map_bind, bind_assoc, bind_assoc]; apply bind_congr; intro prep?
      cases prep? with
      | none => simp [Prod.map]
      | some pair =>
        rcases pair with ⟨isFreshPeer, isIdealSend, rawP⟩
        cases isFreshPeer
        · simp only [Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc,
            Function.comp_def, pure_bind, Prod.map, id_eq, Prod.mk.eta]
        · rw [hDec]
          simp only [↓reduceIte, Bool.false_and, Bool.false_eq_true, map_eq_bind_pure_comp,
            bind_assoc, Function.comp_def, pure_bind, Prod.map, id_eq, Prod.mk.eta]

private theorem map_snd_stepAuthCpaCutoffSlotPrim_zero1Key (S : Setup) (gq : AuthQuery S)
    (shst : AuthCpaSlotState S) :
    Prod.map id Prod.snd <$> stepAuthCpaCutoffSlotPrim1Key 0 S gq shst =
      stepAuthCpaCutoffPrim1Key 0 S gq shst.2 := by
  unfold stepAuthCpaCutoffSlotPrim1Key stepAuthCpaCutoffPrim1Key
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only; split <;> [simp [Prod.map]; exact
      map_snd_runAuthSendCpaCutoffSlotPrim_of_decide_eq 0 0 S (.sendOPK u i) u bundle m0 m1 shst (by simp)]
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only; split <;> [simp [Prod.map]; exact
      map_snd_runAuthSendCpaCutoffSlotPrim_of_decide_eq 0 0 S (.sendNoOPK u i) u bundle m0 m1 shst (by simp)]
  | _ => dsimp only; rw [map_bind]; simp [Prod.map]

private theorem map_snd_runWithPrimStep_stepAuthCpaCutoffSlotPrim_zero1Key
    (S : Setup) {α : Type} (mx : OracleComp (unifSpec + authSpec S) α) (shst : AuthCpaSlotState S) :
    Prod.map id Prod.snd <$> runWithPrimStep (stepAuthCpaCutoffSlotPrim1Key 0 S) mx shst =
      runWithPrimStep (stepAuthCpaCutoffPrim1Key 0 S) mx shst.2 := by
  induction mx using OracleComp.inductionOn generalizing shst with
  | pure x => simp [runWithPrimStep_pure, Prod.map]
  | query_bind q cont ih =>
    cases q with
    | inl n =>
      rw [runWithPrimStep_query_inl, runWithPrimStep_query_inl, map_bind]
      congr 1; funext u; exact ih u shst
    | inr gq =>
      rw [runWithPrimStep_query_inr, runWithPrimStep_query_inr, map_bind,
          ← map_snd_stepAuthCpaCutoffSlotPrim_zero1Key S gq shst]
      conv_rhs =>
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map, id_eq]
      congr 1; funext p; exact ih p.1 p.2

private theorem authCpaSlotCutoffExp_zero_eq1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    authCpaSlotCutoffExp1Key 0 S P A = authCpaCutoffExp1Key 0 S P A := by
  unfold authCpaSlotCutoffExp1Key authCpaCutoffExp1Key; congr 1
  rw [← map_snd_runWithPrimStep_stepAuthCpaCutoffSlotPrim_zero1Key S A.run
    (0, AuthHybridStateFixed.empty S true)]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map, id_eq]

private theorem map_snd_stepAuthCpaCutoffSlotPrim_min1Key
    (S : Setup) (b : QueryBudget) (gq : AuthQuery S) (shst : AuthCpaSlotState S)
    (hLt : isAuthSendQuery (Sum.inr gq : ℕ ⊕ AuthQuery S) → shst.1 < min b.q_total S.N_send_tot) :
    Prod.map id Prod.snd <$>
        stepAuthCpaCutoffSlotPrim1Key (min b.q_total S.N_send_tot) S gq shst =
      stepAuthCpaCutoffPrim1Key S.N_send_tot S gq shst.2 := by
  unfold stepAuthCpaCutoffSlotPrim1Key stepAuthCpaCutoffPrim1Key
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only; split
    · simp [Prod.map]
    · have h1 := hLt (by simp [isAuthSendQuery])
      have h2 : initSessionSlotIdx (.sendOPK u i) < S.N_send_tot :=
        Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)
      exact map_snd_runAuthSendCpaCutoffSlotPrim_of_decide_eq
        (min b.q_total S.N_send_tot) S.N_send_tot S (.sendOPK u i) u bundle m0 m1 shst
        (by rw [decide_eq_true h1, decide_eq_true h2])
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only; split
    · simp [Prod.map]
    · have h1 := hLt (by simp [isAuthSendQuery])
      have h2 := initSessionSlotIdx_sendNoOPK_lt u i
      exact map_snd_runAuthSendCpaCutoffSlotPrim_of_decide_eq
        (min b.q_total S.N_send_tot) S.N_send_tot S (.sendNoOPK u i) u bundle m0 m1 shst
        (by rw [decide_eq_true h1, decide_eq_true h2])
  | _ => dsimp only; rw [map_bind]; simp [Prod.map]

private theorem map_snd_runWithPrimStep_stepAuthCpaCutoffSlotPrim_min1Key
    (S : Setup) (b : QueryBudget) {α : Type} (mx : OracleComp (unifSpec + authSpec S) α)
    (Qtot Qsend : Nat)
    (hTot : IsQueryBoundP mx (fun q => isGameQuery q = true) Qtot)
    (hSend : IsQueryBoundP mx isAuthSendQuery Qsend)
    (shst : AuthCpaSlotState S)
    (hBtot : shst.1 + Qtot ≤ b.q_total) (hBsend : shst.1 + Qsend ≤ S.N_send_tot) :
    Prod.map id Prod.snd <$>
        runWithPrimStep (stepAuthCpaCutoffSlotPrim1Key (min b.q_total S.N_send_tot) S) mx shst =
      runWithPrimStep (stepAuthCpaCutoffPrim1Key S.N_send_tot S) mx shst.2 := by
  induction mx using OracleComp.inductionOn generalizing Qtot Qsend shst with
  | pure x => simp [runWithPrimStep_pure, Prod.map]
  | query_bind q cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hTot hSend
    cases q with
    | inl n =>
      rcases hTot with ⟨_, hTotC⟩; rcases hSend with ⟨_, hSendC⟩
      have hnlG : ¬ (isGameQuery (Sum.inl n : ℕ ⊕ AuthQuery S) = true) := by simp [isGameQuery]
      have hnlS : ¬ isAuthSendQuery (Sum.inl n : ℕ ⊕ AuthQuery S) := by simp [isAuthSendQuery]
      simp only [hnlG] at hTotC; simp only [hnlS, ↓reduceIte] at hSendC
      rw [runWithPrimStep_query_inl, runWithPrimStep_query_inl, map_bind]
      congr 1; funext u; exact ih u Qtot Qsend (hTotC u) (hSendC u) shst hBtot hBsend
    | inr gq =>
      rcases hTot with ⟨hFirstG, hTotC⟩; rcases hSend with ⟨hFirstS, hSendC⟩
      have hgr : isGameQuery (Sum.inr gq : ℕ ⊕ AuthQuery S) = true := rfl
      rcases hFirstG with hAbs | _
      · exfalso; exact hAbs hgr
      · obtain ⟨Qtot', rfl⟩ : ∃ Qtot', Qtot = Qtot' + 1 := ⟨Qtot - 1, by omega⟩
        simp only [hgr, ↓reduceIte, Nat.add_sub_cancel] at hTotC
        have hSendLt : isAuthSendQuery (Sum.inr gq : ℕ ⊕ AuthQuery S) →
            shst.1 < min b.q_total S.N_send_tot := by
          intro hS; cases hFirstS with
          | inl hAbsS => exact (hAbsS hS).elim
          | inr _ => omega
        rw [runWithPrimStep_query_inr, runWithPrimStep_query_inr, map_bind,
            ← map_snd_stepAuthCpaCutoffSlotPrim_min1Key S b gq shst hSendLt]
        conv_rhs =>
          simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map, id_eq]
        refine bind_congr_of_mem_support_spec _ _ _ (fun p hp => ?_)
        have hStepB :=
          (stepAuthCpaCutoffSlotPrim_ns_bounds1Key (min b.q_total S.N_send_tot) S gq shst hp).2
        by_cases hS : isAuthSendQuery (Sum.inr gq : ℕ ⊕ AuthQuery S)
        · rcases hFirstS with hAbsS | _
          · exfalso; exact hAbsS hS
          · obtain ⟨Qsend', rfl⟩ : ∃ Qsend', Qsend = Qsend' + 1 := ⟨Qsend - 1, by omega⟩
            simp only [hS, ↓reduceIte, Nat.add_sub_cancel] at hSendC hStepB
            exact ih p.1 Qtot' Qsend' (hTotC p.1) (hSendC p.1) p.2 (by omega) (by omega)
        · simp only [hS, ↓reduceIte, Nat.add_zero] at hSendC hStepB
          exact ih p.1 Qtot' Qsend (hTotC p.1) (hSendC p.1) p.2 (by omega) (by omega)

private theorem authCpaSlotCutoffExp_min_eq1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    authCpaSlotCutoffExp1Key (min b.q_total S.N_send_tot) S P A.1 =
      authCpaCutoffExp1Key S.N_send_tot S P A.1 := by
  unfold authCpaSlotCutoffExp1Key authCpaCutoffExp1Key; congr 1
  rw [← map_snd_runWithPrimStep_stepAuthCpaCutoffSlotPrim_min1Key S b A.1.run
    b.q_total S.N_send_tot (QueryBounded.auth_total A.2) (QueryBounded.auth_send A.2)
    (0, AuthHybridStateFixed.empty S true) (by simp) (by simp)]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map, id_eq]

private theorem abs_sub_authCpaSlotCutoffExp_eq_mul_aeadIndCpa1Key
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authCpaSlotCutoffExp1Key 0 S P A.1] {true}).toReal -
     (𝒟[authCpaSlotCutoffExp1Key (min b.q_total S.N_send_tot) S P A.1] {true}).toReal| =
      ((min b.q_total S.N_send_tot : Nat) : ℝ) *
        AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) := by
  let M := min b.q_total S.N_send_tot
  have hSumT :
      (M : ℝ) * (𝒟[sampleIndexRange M >>=
        fun idx => cpaSlotStepWorld1Key idx S P true b.q_total A.1] {true}).toReal =
      ∑ idx ∈ Finset.range M, (𝒟[authCpaSlotCutoffExp1Key idx S P A.1] {true}).toReal := by
    rw [mul_toReal_sampleIndexRange_bind_eq_sum]
    refine Finset.sum_congr rfl (fun idx _ => ?_)
    rw [cpaSlotStepWorld_eq_authCpaSlotCutoffExp1Key idx S P true b A]; rfl
  have hSumF :
      (M : ℝ) * (𝒟[sampleIndexRange M >>=
        fun idx => cpaSlotStepWorld1Key idx S P false b.q_total A.1] {true}).toReal =
      ∑ idx ∈ Finset.range M, (𝒟[authCpaSlotCutoffExp1Key (idx + 1) S P A.1] {true}).toReal := by
    rw [mul_toReal_sampleIndexRange_bind_eq_sum]
    refine Finset.sum_congr rfl (fun idx _ => ?_)
    rw [cpaSlotStepWorld_eq_authCpaSlotCutoffExp1Key idx S P false b A]; rfl
  have hTel :
      ∑ idx ∈ Finset.range M, (𝒟[authCpaSlotCutoffExp1Key idx S P A.1] {true}).toReal -
        ∑ idx ∈ Finset.range M, (𝒟[authCpaSlotCutoffExp1Key (idx + 1) S P A.1] {true}).toReal =
      (𝒟[authCpaSlotCutoffExp1Key 0 S P A.1] {true}).toReal -
        (𝒟[authCpaSlotCutoffExp1Key M S P A.1] {true}).toReal := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_range_sub' (fun idx => (𝒟[authCpaSlotCutoffExp1Key idx S P A.1] {true}).toReal) M
  have hDiff :
      (𝒟[authCpaSlotCutoffExp1Key 0 S P A.1] {true}).toReal -
        (𝒟[authCpaSlotCutoffExp1Key M S P A.1] {true}).toReal =
      (M : ℝ) *
        ((𝒟[sampleIndexRange M >>=
            fun idx => cpaSlotStepWorld1Key idx S P true b.q_total A.1] {true}).toReal -
         (𝒟[sampleIndexRange M >>=
            fun idx => cpaSlotStepWorld1Key idx S P false b.q_total A.1] {true}).toReal) := by
    linarith
  have hAdv :
      AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) =
      |(𝒟[sampleIndexRange M >>=
          fun idx => cpaSlotStepWorld1Key idx S P true b.q_total A.1] {true}).toReal -
       (𝒟[sampleIndexRange M >>=
          fun idx => cpaSlotStepWorld1Key idx S P false b.q_total A.1] {true}).toReal| := by
    unfold AeadIndCpaReal AeadIndCpa
    rw [evalDist_aeadIndCpaExp_aeadCpaReductionAuthFixed_eq1Key S P b A,
        evalDist_boolBias_bind_uniformBool, MeasureTheory.Measure.toReal_boolDist]
  rw [hDiff, abs_mul, abs_of_nonneg (Nat.cast_nonneg M), hAdv]

/-- Sum/average telescoping identity for `authCpaCutoffExp1Key` (`0 .. S.N_send_tot`) via
    creation-order fresh-send slot clamp `min b.q_total S.N_send_tot`. -/
theorem abs_sub_authCpaCutoffExp_eq_mul_aeadIndCpa1Key
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authCpaCutoffExp1Key 0 S P A.1] {true}).toReal -
     (𝒟[authCpaCutoffExp1Key S.N_send_tot S P A.1] {true}).toReal| =
      ((min b.q_total S.N_send_tot : Nat) : ℝ) *
        AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) := by
  rw [← authCpaSlotCutoffExp_zero_eq1Key S P A.1, ← authCpaSlotCutoffExp_min_eq1Key S P b A]
  exact abs_sub_authCpaSlotCutoffExp_eq_mul_aeadIndCpa1Key S P b A

/-- Upper bound form `M_send * Adv ≤ S.N_send_tot * Adv` for `authCpaCutoffExp1Key`. -/
theorem abs_sub_authCpaCutoffExp_le_mul_aeadIndCpa1Key
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authCpaCutoffExp1Key 0 S P A.1] {true}).toReal -
     (𝒟[authCpaCutoffExp1Key S.N_send_tot S P A.1] {true}).toReal| ≤
      (S.N_send_tot : ℝ) * AeadIndCpaReal P (aeadCpaReductionAuthFixed1Key S b A) := by
  rw [abs_sub_authCpaCutoffExp_eq_mul_aeadIndCpa1Key S P b A]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.min_le_right _ _))
    (aeadIndCpa_nonneg _ _)

end SignalPqxdh.Security
