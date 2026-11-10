/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.CryptoFoundations.SecExp.Measure
import VCVio.EvalDist.Monad.Basic

/-!
# `Auth` `IND-CPA` Cutoff Hybrid and Telescoping Bound

Defines the `IND-CPA` state projection (`eraseAuthCpaFixed`) and session-cutoff / creation-order
slot-cutoff hybrid experiments (`authCpaCutoffExp`, `authCpaSlotCutoffExp`), and proves the
telescoping bound `abs_sub_authCpaCutoffExp_le_mul_aeadIndCpa`.
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

def eraseIdealSessionAead {S : Setup} (s : IdealAuthSession S) : IdealAuthSession S :=
  { s with msgPlain := [], deriveMessageKeys := (default : MessageKeys) }

/-- State projection of the `Auth` `IND-CPA` hop (`G4 → G5`): sets `secb := true`, canonicalizes
    `advKeys` with `P.pow8`, and erases the `sent`/`recvd` logs and `msgPlain`/`deriveMessageKeys` in
    `idealSessions`. -/
def eraseAuthCpa (P : Primitives) {S : Setup} (hst : AuthHybridState S) : AuthHybridState S :=
  let hst1 :=
    eraseAuthEvents (cacheAuthAdvKeys P { hst with base := { hst.base with secb := true } })
  { hst1 with idealSessions := hst1.idealSessions.map eraseIdealSessionAead }

def eraseAuthCpaFixed (P : Primitives) {S : Setup} (hst : AuthHybridStateFixed S) :
    AuthHybridStateFixed S :=
  { toAuthHybridState := eraseAuthCpa P hst.toAuthHybridState, recvCount := hst.recvCount,
    mkSaltCache := hst.mkSaltCache }
@[simp]
theorem eraseAuthCpa_empty (P : Primitives) (S : Setup) (secb : Bool) :
    eraseAuthCpa P (AuthHybridState.empty S secb) = AuthHybridState.empty S true := rfl

@[simp]
theorem eraseAuthCpaFixed_empty (P : Primitives) (S : Setup) (secb : Bool) :
    eraseAuthCpaFixed P (AuthHybridStateFixed.empty S secb) =
      AuthHybridStateFixed.empty S true := rfl

@[simp]
theorem eraseIdealSessionAead_idem {S : Setup} (s : IdealAuthSession S) :
    eraseIdealSessionAead (eraseIdealSessionAead s) = eraseIdealSessionAead s := rfl

theorem validAdvKeysPow8_eraseAuthCpa (P : Primitives)
    {S : Setup} (hst : AuthHybridState S) :
    ValidAdvKeysPow8 P (eraseAuthCpa P hst).base.advKeys := by
  intro e he
  rcases List.mem_map.mp he with ⟨⟨_, pk⟩, _, rfl⟩
  rfl

theorem simulateQ_checkBundleSpkHonIdealFromPeerPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (hSpk : spkBundles.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (checkBundleSpkHonIdealFromPeerPrim S
        (findHonestPrincipal P principals bundle.ikB) spkBundles bundle) =
      pure (checkBundleSpkHonIdeal P principals spkBundles bundle) := by
  unfold checkBundleSpkHonIdealFromPeerPrim checkBundleSpkHonIdeal
  cases findHonestPrincipal P principals bundle.ikB with
  | none => rfl
  | some kp =>
    rcases kp with ⟨k, pEntry⟩
    dsimp only
    rw [List.take_of_length_le hSpk,
        simulateQ_anyMPrim P _
          (fun ((u, _), b) =>
            u == k && ((pEntry.corrupted && P.pow8 b.spkPk == P.pow8 bundle.spkB) ||
              b.spkPk == bundle.spkB))
          (fun _ => rfl) spkBundles]

theorem stepUntilAuthCpaChallengeFixedPrim_pure (idx : Nat) (S : Setup) {α : Type}
    (defaultVal a : α) (fuel : Nat) (hst : AuthHybridStateFixed S) :
    stepUntilAuthCpaChallengeFixedPrim idx S defaultVal (pure a) fuel hst =
      pure (.done a hst) := rfl

@[simp]
theorem stepUntilAuthCpaChallengeFixedPrim_query_inl (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α) (n : Nat)
    (cont : (unifSpec + authSpec S).Range (Sum.inl n) → OracleComp (unifSpec + authSpec S) α)
    (fuel : Nat) (hst : AuthHybridStateFixed S) :
    stepUntilAuthCpaChallengeFixedPrim idx S defaultVal
        (liftM (OracleSpec.query (Sum.inl n)) >>= cont) fuel hst =
      (liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n)) >>=
        fun u => stepUntilAuthCpaChallengeFixedPrim idx S defaultVal (cont u) fuel hst) := rfl

@[simp]
theorem stepUntilAuthCpaChallengeFixedPrim_query_inr_zero (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α) (gq : AuthQuery S)
    (cont : (unifSpec + authSpec S).Range (Sum.inr gq) → OracleComp (unifSpec + authSpec S) α)
    (hst : AuthHybridStateFixed S) :
    stepUntilAuthCpaChallengeFixedPrim idx S defaultVal
        (liftM (OracleSpec.query (Sum.inr gq)) >>= cont) 0 hst =
      pure (.done defaultVal hst) := rfl

theorem aeadCpaReductionAuthFixed_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadCpaReductionAuthFixed S b A).q_prim ≤ primQueryBudget S b := by
  unfold aeadCpaReductionAuthFixed perQueryAuthPrimBudget primQueryBudget
  dsimp only
  nlinarith

private theorem bind_congr_of_mem_support_spec {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (oa : OracleComp spec α) (f g : α → OracleComp spec β) (h : ∀ x ∈ support oa, f x = g x) :
    oa >>= f = oa >>= g := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using h x (by simp)
  | query_bind i t ih =>
    rw [bind_assoc, bind_assoc]; apply bind_congr; intro u
    exact ih u (fun x hx => h x (MonadAttach.mem_support_bind.mpr ⟨u, by simp, hx⟩))
@[simp]
private theorem simulateQ_primQ_aeadEnc_bytes (P : Primitives) (mk : MessageKeys) (ad pt : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.aeadEnc mk ad pt)) : ProbComp Bytes) =
      pure (P.aeadEnc mk ad pt) := rfl
@[irreducible]
private def withSid {S : Setup} (sid : SessionId S) (p : AuthCpaPausePayload S) :
    AuthCpaPausePayload S := { p with sid := sid }
private theorem withSid_sid {S : Setup} (sid : SessionId S) (p : AuthCpaPausePayload S) :
    (withSid sid p).sid = sid := by unfold withSid; rfl
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
    rcases up with ⟨_, uEntry⟩; dsimp only; rw [map_bind]; apply bind_congr; intro peerPrincipal?
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
    { hst.toAuthHybridState with base := { hst.toAuthHybridState.base with usedSendSessions := u } } }

private theorem stepAuthCpaNonSendPrim_map_setUsedSend (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    Prod.map id (setUsedSend hst.toAuthHybridState.base.usedSendSessions) <$>
      stepAuthCpaNonSendPrim S q hst = stepAuthCpaNonSendPrim S q hst := by
  unfold stepAuthCpaNonSendPrim; cases q with
  | recvOPK k j o msg =>
    dsimp only; split
    · rfl
    · split
      · rfl
      · rw [map_bind]; apply bind_congr; intro _; split
        · rfl
        · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none => rfl
          | some kp =>
            rcases kp with ⟨_, _⟩
            cases hst.toAuthHybridState.base.spkBundles.find?
                (fun (idx, _) => idx == (k.val, j.val)) with
            | none => rfl
            | some bp =>
              rcases bp with ⟨_, _⟩
              cases hst.toAuthHybridState.base.opkEntries.find?
                  (fun (idx, _) => idx == (k.val, j.val, o.val)) with
              | none => rfl
              | some op =>
                rcases op with ⟨_, _⟩; dsimp only; split
                · rfl
                · rw [map_bind]; apply bind_congr; intro _; rw [map_bind]; apply bind_congr; intro _
                  split
                  · rfl
                  · rw [map_bind]; apply bind_congr; rintro (_ | _)
                    · rfl
                    · dsimp only; repeat (rw [map_bind]; apply bind_congr; intro _)
                      split
                      · rw [map_bind]; apply bind_congr; intro _; rfl
                      · rfl
  | recvNoOPK k j l msg =>
    dsimp only; split
    · rfl
    · split
      · rfl
      · rw [map_bind]; apply bind_congr; intro _; split
        · rfl
        · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none => rfl
          | some kp =>
            rcases kp with ⟨_, _⟩
            cases hst.toAuthHybridState.base.spkBundles.find?
                (fun (idx, _) => idx == (k.val, j.val)) with
            | none => rfl
            | some bp =>
              rcases bp with ⟨_, _⟩; dsimp only; rw [map_bind]; apply bind_congr; intro _
              rw [map_bind]; apply bind_congr; intro _; split
              · rfl
              · rw [map_bind]; apply bind_congr; rintro (_ | _)
                · rfl
                · dsimp only; repeat (rw [map_bind]; apply bind_congr; intro _)
                  split
                  · rw [map_bind]; apply bind_congr; intro _; rfl
                  · rfl
  | corruptIK u =>
    unfold stepAuthOtherPrim; dsimp only
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) <;> rfl
  | genSPK u j =>
    unfold stepAuthOtherPrim; dsimp only; split
    · rfl
    · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some up =>
        rcases up with ⟨_, _⟩; dsimp only; repeat (rw [map_bind]; apply bind_congr; intro _)
        rfl
  | sendOPK _ _ _ _ _ | sendNoOPK _ _ _ _ _ => rfl
  | _ =>
    unfold stepAuthOtherPrim; dsimp only; split
    · rfl
    · repeat (rw [map_bind]; apply bind_congr; intro _)
      rfl

private theorem stepAuthCpaNonSendPrim_usedSendSessions (S : Setup) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) {p : AuthResponse × AuthHybridStateFixed S}
    (hp : p ∈ support (stepAuthCpaNonSendPrim S q hst)) :
    p.2.toAuthHybridState.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions := by
  rw [← stepAuthCpaNonSendPrim_map_setUsedSend S q hst, support_map] at hp
  rcases hp with ⟨_, _, rfl⟩; rfl

private theorem tryPauseAuthCpaSendFixedPrim_subset_usedSend (allowPause : Bool) (cut : Nat)
    (S : Setup) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) {p : AuthResponse × AuthHybridStateFixed S}
    (hp : Sum.inl p ∈
      support (tryPauseAuthCpaSendFixedPrim allowPause cut S sid u bundle m0 m1 hst)) :
    hst.toAuthHybridState.base.usedSendSessions ⊆ p.2.toAuthHybridState.base.usedSendSessions := by
  unfold tryPauseAuthCpaSendFixedPrim at hp; dsimp only at hp; split at hp
  · simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hp; subst hp
    exact List.Subset.refl _
  · split at hp
    · simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hp; subst hp
      exact List.Subset.refl _
    · rw [MonadAttach.mem_support_bind] at hp; rcases hp with ⟨prep?, _, hp⟩
      cases prep? with
      | none =>
        simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hp; subst hp
        exact List.Subset.refl _
      | some sendPair =>
        rcases sendPair with ⟨isFreshPeer, isIdealSend, rawP⟩; dsimp only at hp; split at hp
        · split at hp
          · simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at hp
          · rw [MonadAttach.mem_support_bind] at hp; rcases hp with ⟨mk, _, hp⟩
            rw [MonadAttach.mem_support_bind] at hp; rcases hp with ⟨aeadCt, _, hp⟩
            simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hp; subst hp
            rw [finishAuthCpaSendFixedPure_usedSendSessions]; exact List.subset_cons_self _ _
        · rw [MonadAttach.mem_support_bind] at hp; rcases hp with ⟨mk, _, hp⟩
          rw [MonadAttach.mem_support_bind] at hp; rcases hp with ⟨aeadCt, _, hp⟩
          simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hp; subst hp
          rw [finishAuthCpaSendFixedPure_usedSendSessions]; exact List.subset_cons_self _ _

private theorem stepAuthCpaCutoffPrim_subset_usedSend (cut : Nat) (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) {p : AuthResponse × AuthHybridStateFixed S}
    (hp : p ∈ support (stepAuthCpaCutoffPrim cut S q hst)) :
    hst.toAuthHybridState.base.usedSendSessions ⊆ p.2.toAuthHybridState.base.usedSendSessions := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim at hp; dsimp only at hp; split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact List.Subset.refl _
    · unfold runAuthSendCpaCutoffPrim at hp; rw [MonadAttach.mem_support_bind] at hp
      rcases hp with ⟨res, hres, hp⟩; cases res with
      | inl _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp
        exact tryPauseAuthCpaSendFixedPrim_subset_usedSend false cut S (.sendOPK u i) u bundle
          m0 m1 hst hres
      | inr _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact List.Subset.refl _
  | sendNoOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim at hp; dsimp only at hp; split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact List.Subset.refl _
    · unfold runAuthSendCpaCutoffPrim at hp; rw [MonadAttach.mem_support_bind] at hp
      rcases hp with ⟨res, hres, hp⟩; cases res with
      | inl _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp
        exact tryPauseAuthCpaSendFixedPrim_subset_usedSend false cut S (.sendNoOPK u i) u bundle
          m0 m1 hst hres
      | inr _ =>
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact List.Subset.refl _
  | _ => rw [stepAuthCpaNonSendPrim_usedSendSessions S _ hst hp]

private theorem tryPauseAuthCpaSendFixedPrim_false_eq_of_mem_usedSend
    (idx cut : Nat) (S : Setup) (sid sid' : SessionId S)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S)
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

private theorem stepAuthCpaCutoffPrim_eq_of_mem_usedSend
    (idx cut : Nat) (S : Setup) (sid : SessionId S) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hSid : initSessionSlotIdx sid = idx) (hLt : idx < S.N_send_tot)
    (hCut : ∀ sIdx, sIdx ≠ idx → decide (sIdx < idx) = decide (sIdx < cut))
    (hMem : sid ∈ hst.toAuthHybridState.base.usedSendSessions) :
    stepAuthCpaCutoffPrim idx S q hst = stepAuthCpaCutoffPrim cut S q hst := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim runAuthSendCpaCutoffPrim; dsimp only; split
    · rfl
    · rw [tryPauseAuthCpaSendFixedPrim_false_eq_of_mem_usedSend
        idx cut S sid (.sendOPK u i) u bundle m0 m1 hst hSid hLt hCut hMem]
  | sendNoOPK u i bundle m0 m1 =>
    unfold stepAuthCpaCutoffPrim runAuthSendCpaCutoffPrim; dsimp only; split
    · rfl
    · rw [tryPauseAuthCpaSendFixedPrim_false_eq_of_mem_usedSend
        idx cut S sid (.sendNoOPK u i) u bundle m0 m1 hst hSid hLt hCut hMem]
  | _ => rfl

private theorem runWithPrimStep_stepAuthCpaCutoffPrim_eq_of_mem_usedSend
    (idx cut : Nat) (S : Setup) (sid : SessionId S) {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α)
    (hst : AuthHybridStateFixed S)
    (hSid : initSessionSlotIdx sid = idx) (hLt : idx < S.N_send_tot)
    (hCut : ∀ sIdx, sIdx ≠ idx → decide (sIdx < idx) = decide (sIdx < cut))
    (hMem : sid ∈ hst.toAuthHybridState.base.usedSendSessions) :
    runWithPrimStep (stepAuthCpaCutoffPrim idx S) mx hst =
      runWithPrimStep (stepAuthCpaCutoffPrim cut S) mx hst := by
  induction mx using OracleComp.inductionOn generalizing hst with
  | pure x => rfl
  | query_bind q cont ih =>
    cases q with
    | inl n =>
      rw [runWithPrimStep_query_inl, runWithPrimStep_query_inl]
      congr 1; funext u
      exact ih u hst hMem
    | inr gq =>
      rw [runWithPrimStep_query_inr, runWithPrimStep_query_inr,
          stepAuthCpaCutoffPrim_eq_of_mem_usedSend idx cut S sid gq hst hSid hLt hCut hMem]
      exact bind_congr_of_mem_support_spec (stepAuthCpaCutoffPrim cut S gq hst) _ _
        (fun p hp => ih p.1 p.2 (stepAuthCpaCutoffPrim_subset_usedSend cut S gq hst hp hMem))

/-- Session-cutoff `Auth` experiment over `PrimBaseSpec` (`cut = 0` encrypts `m1` on all fresh
    challenge sessions; `cut = S.N_send_tot` encrypts `m0` on all fresh challenge sessions). -/
noncomputable def authCpaCutoffExp (cut : Nat) (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp Bool :=
  simulateQ (primBaseImpl P) do
    let (b', finalSt) ←
      runWithPrimStep (stepAuthCpaCutoffPrim cut S) A.run (AuthHybridStateFixed.empty S true)
    finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState

noncomputable def cpaAfterStepUntil (idx : Nat) (S : Setup) (P : Primitives)
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
      (runWithPrimStepFuel false (stepAuthCpaCutoffPrim idx S) (cont resp) fuel hst')
    simulateQ (primBaseImpl P)
      (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)

/-- 1-step `IND-CPA` simulation world at fixed `(idx, secb)` before comparing `== secb`. -/
noncomputable def cpaStepWorld (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (fuel : Nat) (A : AuthAdversary S) : ProbComp Bool :=
  simulateQ (primBaseImpl P)
    (stepUntilAuthCpaChallengeFixedPrim idx S false A.run fuel
      (AuthHybridStateFixed.empty S true)) >>=
    cpaAfterStepUntil idx S P secb fuel

private theorem simulateQ_tryPause_and_cpaAfter_eq
    (idx : Nat) (S : Setup) (P : Primitives) (secb : Bool) (hLt : idx < S.N_send_tot)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (cont : AuthResponse → OracleComp (unifSpec + authSpec S) Bool)
    (Q' fuel1' fuel2 : Nat)
    (h_cont : ∀ r, IsQueryBoundP (cont r) (fun q => isGameQuery q = true) Q') (h2 : Q' ≤ fuel2)
    (ih : ∀ r s',
      (simulateQ (primBaseImpl P)
        (stepUntilAuthCpaChallengeFixedPrim idx S false (cont r) fuel1' s') >>=
        cpaAfterStepUntil idx S P secb fuel2) =
      (simulateQ (primBaseImpl P)
        (runWithPrimStep (stepAuthCpaCutoffPrim (if secb then idx else idx + 1) S) (cont r) s') >>=
        fun (b', finalSt) =>
          simulateQ (primBaseImpl P)
            (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState))) :
    (simulateQ (primBaseImpl P)
      (do
        let stepRes ← tryPauseAuthCpaSendFixedPrim true idx S sid u bundle m0 m1 hst
        match stepRes with
        | .inl (resp, s') => stepUntilAuthCpaChallengeFixedPrim idx S false (cont resp) fuel1' s'
        | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
      cpaAfterStepUntil idx S P secb fuel2) =
    (simulateQ (primBaseImpl P)
      (runAuthSendCpaCutoffPrim (if secb then idx else idx + 1) S sid u bundle m0 m1 hst >>=
        fun p => runWithPrimStep
          (stepAuthCpaCutoffPrim (if secb then idx else idx + 1) S) (cont p.1) p.2) >>=
      fun (b', finalSt) =>
        simulateQ (primBaseImpl P)
          (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)) := by
  have hCut : ∀ sIdx, sIdx ≠ idx →
      decide (sIdx < idx) = decide (sIdx < if secb then idx else idx + 1) := fun sIdx hNe => by
    cases secb
    · simp; omega
    · rfl
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
      apply bind_congr; intro prep?; cases prep? with
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
            simp only [hIdx, ↓reduceIte, simulateQ_pure, pure_bind, cpaAfterStepUntil, hLenEq,
              simulateQ_bind, simulateQ_embedUnif, bind_assoc, finishAuthCpaSendFixedPure_msgPlain_irrel]
            apply bind_congr; intro mk; simp only [hPlain, simulateQ_primQ_aeadEnc_bytes, pure_bind]
            let fin := finishAuthCpaSendFixedPure true true (withSid sid rawP)
              (P.aeadEnc mk (withSid sid rawP).ad (if secb = true then m1 else m0)) hst
            have hMemSid : sid ∈ fin.2.toAuthHybridState.base.usedSendSessions := by
              dsimp [fin]; rw [finishAuthCpaSendFixedPure_usedSendSessions, withSid_sid]
              exact List.mem_cons_self
            rw [runWithPrimStepFuel_eq_runWithPrimStep false (stepAuthCpaCutoffPrim idx S)
                  (cont fin.1) Q' fuel2 (h_cont _) h2 fin.2,
                runWithPrimStep_stepAuthCpaCutoffPrim_eq_of_mem_usedSend idx
                  (if secb = true then idx else idx + 1) S sid (cont fin.1) fin.2 hsIdx hLt hCut
                  hMemSid]
          · have hCutSid := hCut (initSessionSlotIdx sid)
              (beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hIdx))
            simp only [hIdx, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
              bind_assoc]
            apply bind_congr; intro mk; rw [hCutSid]; apply bind_congr; intro aeadCt
            simp only [simulateQ_pure, pure_bind]; exact ih _ _
        · simp only [hFresh, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, bind_assoc]
          apply bind_congr; intro mk; apply bind_congr; intro aeadCt
          simp only [simulateQ_pure, pure_bind]; exact ih _ _

private theorem stepUntilFixed_nonSend (idx : Nat) (S : Setup) {α : Type} (dflt : α)
    (gq : AuthQuery S) (h : ¬ isAuthSendQuery (Sum.inr gq))
    (cont : (unifSpec + authSpec S).Range (Sum.inr gq) → OracleComp (unifSpec + authSpec S) α)
    (f : Nat) (hst : AuthHybridStateFixed S) :
    stepUntilAuthCpaChallengeFixedPrim idx S dflt (liftM (OracleSpec.query (Sum.inr gq)) >>= cont)
      (f + 1) hst =
    (stepAuthCpaNonSendPrim S gq hst >>=
      fun p => stepUntilAuthCpaChallengeFixedPrim idx S dflt (cont p.1) f p.2) := by
  cases gq <;> first | exact False.elim (h trivial) | rfl

theorem simulateQ_stepUntil_and_cpaAfter_eq_cutoff (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (hLt : idx < S.N_send_tot)
    (mx : OracleComp (unifSpec + authSpec S) Bool)
    (Q fuel1 fuel2 : Nat)
    (h_mx : IsQueryBoundP mx (fun q => isGameQuery q = true) Q)
    (h1 : Q ≤ fuel1) (h2 : Q ≤ fuel2)
    (hst : AuthHybridStateFixed S) :
    (simulateQ (primBaseImpl P) (stepUntilAuthCpaChallengeFixedPrim idx S false mx fuel1 hst) >>=
      cpaAfterStepUntil idx S P secb fuel2) =
    (simulateQ (primBaseImpl P)
      (runWithPrimStep (stepAuthCpaCutoffPrim (if secb then idx else idx + 1) S) mx hst) >>=
      fun (b', finalSt) =>
        simulateQ (primBaseImpl P)
          (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)) := by
  induction mx using OracleComp.inductionOn generalizing Q fuel1 hst with
  | pure x =>
    rw [stepUntilAuthCpaChallengeFixedPrim_pure, runWithPrimStep_pure]; simp [cpaAfterStepUntil]
  | query_bind q cont ih =>
    rw [isQueryBoundP_query_bind_iff] at h_mx; cases q with
    | inl n =>
      rcases h_mx with ⟨_, h_cont⟩
      have hnl : ¬ (isGameQuery (Sum.inl n : ℕ ⊕ AuthQuery S) = true) := by simp [isGameQuery]
      simp only [hnl] at h_cont
      rw [stepUntilAuthCpaChallengeFixedPrim_query_inl, runWithPrimStep_query_inl]
      simp only [simulateQ_bind, bind_assoc]; congr 1; funext u
      exact ih u Q fuel1 (h_cont u) h1 h2 hst
    | inr gq =>
      rcases h_mx with ⟨h_first, h_cont⟩
      have hgr : isGameQuery (Sum.inr gq : ℕ ⊕ AuthQuery S) = true := rfl
      rcases h_first with h_abs | hQpos
      · exact False.elim (h_abs hgr)
      · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
        obtain ⟨fuel1', rfl⟩ : ∃ fuel1', fuel1 = fuel1' + 1 := ⟨fuel1 - 1, by omega⟩
        simp only [hgr, ↓reduceIte, Nat.add_sub_cancel] at h_cont; rw [runWithPrimStep_query_inr]
        cases gq with
        | sendOPK u i bundle m0 m1 =>
          change (simulateQ (primBaseImpl P) (if bundle.opkB?.isNone then
              stepUntilAuthCpaChallengeFixedPrim idx S false (cont .noneResp) fuel1' hst
            else do
              let stepRes ← tryPauseAuthCpaSendFixedPrim true idx S (.sendOPK u i) u bundle m0 m1 hst
              match stepRes with
              | .inl (resp, s') =>
                stepUntilAuthCpaChallengeFixedPrim idx S false (cont resp) fuel1' s'
              | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
            cpaAfterStepUntil idx S P secb fuel2) = _
          unfold stepAuthCpaCutoffPrim; dsimp only; split
          · exact ih .noneResp Q' fuel1' (h_cont .noneResp) (by omega) (by omega) hst
          · exact simulateQ_tryPause_and_cpaAfter_eq idx S P secb hLt (.sendOPK u i) u bundle m0 m1
              hst cont Q' fuel1' fuel2 h_cont (by omega)
              (fun r s' => ih r Q' fuel1' (h_cont r) (by omega) (by omega) s')
        | sendNoOPK u i bundle m0 m1 =>
          change (simulateQ (primBaseImpl P) (if bundle.opkB?.isSome then
              stepUntilAuthCpaChallengeFixedPrim idx S false (cont .noneResp) fuel1' hst
            else do
              let stepRes ←
                tryPauseAuthCpaSendFixedPrim true idx S (.sendNoOPK u i) u bundle m0 m1 hst
              match stepRes with
              | .inl (resp, s') =>
                stepUntilAuthCpaChallengeFixedPrim idx S false (cont resp) fuel1' s'
              | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
            cpaAfterStepUntil idx S P secb fuel2) = _
          unfold stepAuthCpaCutoffPrim; dsimp only; split
          · exact ih .noneResp Q' fuel1' (h_cont .noneResp) (by omega) (by omega) hst
          · exact simulateQ_tryPause_and_cpaAfter_eq idx S P secb hLt (.sendNoOPK u i) u bundle
              m0 m1 hst cont Q' fuel1' fuel2 h_cont (by omega)
              (fun r s' => ih r Q' fuel1' (h_cont r) (by omega) (by omega) s')
        | _ =>
          rw [stepUntilFixed_nonSend idx S false _ (by simp [isAuthSendQuery]) cont fuel1' hst]
          dsimp only [stepAuthCpaCutoffPrim]; simp only [simulateQ_bind, bind_assoc]
          congr 1; funext p; exact ih p.1 Q' fuel1' (h_cont p.1) (by omega) (by omega) p.2

theorem cpaStepWorld_eq_authCpaCutoffExp (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (hLt : idx < S.N_send_tot)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    cpaStepWorld idx S P secb b.q_total A.1 =
      authCpaCutoffExp (if secb then idx else idx + 1) S P A.1 := by
  unfold cpaStepWorld authCpaCutoffExp
  rw [simulateQ_stepUntil_and_cpaAfter_eq_cutoff idx S P secb hLt
    A.1.run b.q_total b.q_total b.q_total (SignalPqxdh.QueryBounded.auth_total A.property) (le_refl _) (le_refl _)
    (AuthHybridStateFixed.empty S true), simulateQ_bind]

private theorem tryPauseAuthCpaSendSlotPrim_ns_le (cut : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : AuthCpaSlotState S)
    {r : Sum (AuthResponse × AuthCpaSlotState S)
         (Bytes × Bytes × Bytes × AuthCpaPausePayload S × AuthCpaSlotState S)}
    (hr : r ∈ support (tryPauseAuthCpaSendSlotPrim false cut S sid u bundle m0 m1 shst)) :
    match r with
    | .inl (_, s') => shst.1 ≤ s'.1 ∧ s'.1 ≤ shst.1 + 1
    | .inr (_, _, _, _, s') => shst.1 ≤ s'.1 ∧ s'.1 ≤ shst.1 + 1 := by
  rcases shst with ⟨ns, hst⟩; unfold tryPauseAuthCpaSendSlotPrim at hr; dsimp only at hr; split at hr
  · simp at hr; subst hr; exact ⟨le_rfl, Nat.le_succ ns⟩
  · split at hr
    · simp at hr; subst hr; exact ⟨le_rfl, Nat.le_succ ns⟩
    · rw [mem_support_bind_iff] at hr; rcases hr with ⟨prep?, _, hr⟩; cases prep? with
      | none => simp at hr; subst hr; exact ⟨le_rfl, Nat.le_succ ns⟩
      | some pair =>
        rcases pair with ⟨isFreshPeer, isIdealSend, rawP⟩; cases isFreshPeer
        · simp only [Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hr
          rcases hr with ⟨_, _, _, _, hr⟩; simp at hr; subst hr; exact ⟨le_rfl, Nat.le_succ ns⟩
        · simp only [↓reduceIte, Bool.false_and, Bool.false_eq_true, mem_support_bind_iff] at hr
          rcases hr with ⟨_, _, _, _, hr⟩; simp at hr; subst hr; exact ⟨Nat.le_succ ns, le_rfl⟩
private theorem stepAuthCpaCutoffSlotPrim_ns_le (cut : Nat) (S : Setup)
    (gq : AuthQuery S) (shst : AuthCpaSlotState S) {p : (authSpec S).Range gq × AuthCpaSlotState S}
    (hp : p ∈ support (stepAuthCpaCutoffSlotPrim cut S gq shst)) :
    shst.1 ≤ p.2.1 ∧ p.2.1 ≤ shst.1 + (if isAuthSendQuery (Sum.inr gq) then 1 else 0) := by
  unfold stepAuthCpaCutoffSlotPrim runAuthSendCpaCutoffSlotPrim at hp; cases gq with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthSendQuery, ↓reduceIte]; dsimp only at hp; split at hp
    · simp at hp; subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
    · rw [mem_support_bind_iff] at hp; rcases hp with ⟨res, hRes, hp⟩
      have hLe := tryPauseAuthCpaSendSlotPrim_ns_le cut S (.sendOPK u i) u bundle m0 m1 shst hRes
      cases res with
      | inl _ => simp at hp; subst hp; exact hLe
      | inr _ => simp at hp; subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthSendQuery, ↓reduceIte]; dsimp only at hp; split at hp
    · simp at hp; subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
    · rw [mem_support_bind_iff] at hp; rcases hp with ⟨res, hRes, hp⟩
      have hLe := tryPauseAuthCpaSendSlotPrim_ns_le cut S (.sendNoOPK u i) u bundle m0 m1 shst hRes
      cases res with
      | inl _ => simp at hp; subst hp; exact hLe
      | inr _ => simp at hp; subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
  | _ =>
    simp only [isAuthSendQuery, ↓reduceIte, Nat.add_zero]; dsimp only at hp
    rw [mem_support_bind_iff] at hp; rcases hp with ⟨_, _, hp⟩; simp at hp; subst hp
    exact ⟨le_rfl, le_rfl⟩
private theorem tryPauseAuthCpaSendSlotPrim_false_eq_of_le (cut1 cut2 : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : AuthCpaSlotState S) (h1 : cut1 ≤ shst.1) (h2 : cut2 ≤ shst.1) :
    tryPauseAuthCpaSendSlotPrim false cut1 S sid u bundle m0 m1 shst =
      tryPauseAuthCpaSendSlotPrim false cut2 S sid u bundle m0 m1 shst := by
  rcases shst with ⟨ns, hst⟩
  have hc1 : decide (ns < cut1) = false := decide_eq_false (by omega)
  have hc2 : decide (ns < cut2) = false := decide_eq_false (by omega)
  unfold tryPauseAuthCpaSendSlotPrim; dsimp only; rw [hc1, hc2]; simp only [Bool.false_and]
private theorem stepAuthCpaCutoffSlotPrim_eq_of_le (cut1 cut2 : Nat) (S : Setup)
    (gq : AuthQuery S) (shst : AuthCpaSlotState S) (h1 : cut1 ≤ shst.1) (h2 : cut2 ≤ shst.1) :
    stepAuthCpaCutoffSlotPrim cut1 S gq shst = stepAuthCpaCutoffSlotPrim cut2 S gq shst := by
  unfold stepAuthCpaCutoffSlotPrim runAuthSendCpaCutoffSlotPrim; cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only; split
    · rfl
    · rw [tryPauseAuthCpaSendSlotPrim_false_eq_of_le cut1 cut2 S (.sendOPK u i) u bundle m0 m1
        shst h1 h2]
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only; split
    · rfl
    · rw [tryPauseAuthCpaSendSlotPrim_false_eq_of_le cut1 cut2 S (.sendNoOPK u i) u bundle m0 m1
        shst h1 h2]
  | _ => rfl
private theorem runWithPrimStep_stepAuthCpaCutoffSlotPrim_eq_of_le (cut1 cut2 : Nat) (S : Setup)
    {α : Type} (mx : OracleComp (unifSpec + authSpec S) α) (shst : AuthCpaSlotState S)
    (h1 : cut1 ≤ shst.1) (h2 : cut2 ≤ shst.1) :
    runWithPrimStep (stepAuthCpaCutoffSlotPrim cut1 S) mx shst =
      runWithPrimStep (stepAuthCpaCutoffSlotPrim cut2 S) mx shst := by
  induction mx using OracleComp.inductionOn generalizing shst with
  | pure x => rfl
  | query_bind q cont ih =>
    cases q with
    | inl n =>
      rw [runWithPrimStep_query_inl, runWithPrimStep_query_inl]; congr 1; funext u
      exact ih u shst h1 h2
    | inr gq =>
      rw [runWithPrimStep_query_inr, runWithPrimStep_query_inr,
          stepAuthCpaCutoffSlotPrim_eq_of_le cut1 cut2 S gq shst h1 h2]
      exact bind_congr_of_mem_support_spec _ _ _ (fun p hp =>
        let hLe := (stepAuthCpaCutoffSlotPrim_ns_le cut2 S gq shst hp).1
        ih p.1 p.2 (le_trans h1 hLe) (le_trans h2 hLe))

theorem stepUntilAuthCpaChallengeSlotPrim_pure (idx : Nat) (S : Setup) {α : Type}
    (defaultVal a : α) (fuel : Nat) (shst : AuthCpaSlotState S) :
    stepUntilAuthCpaChallengeSlotPrim idx S defaultVal (pure a) fuel shst =
      pure (.done a shst) := rfl

@[simp]
theorem stepUntilAuthCpaChallengeSlotPrim_query_inl (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α) (n : Nat)
    (cont : (unifSpec + authSpec S).Range (Sum.inl n) → OracleComp (unifSpec + authSpec S) α)
    (fuel : Nat) (shst : AuthCpaSlotState S) :
    stepUntilAuthCpaChallengeSlotPrim idx S defaultVal
        (liftM (OracleSpec.query (Sum.inl n)) >>= cont) fuel shst =
      (liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n)) >>=
        fun u => stepUntilAuthCpaChallengeSlotPrim idx S defaultVal (cont u) fuel shst) := rfl

/-- Creation-order session-cutoff `Auth` experiment over `PrimBaseSpec`. -/
noncomputable def authCpaSlotCutoffExp (cut : Nat) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  simulateQ (primBaseImpl P) do
    let (b', (_, finalSt)) ←
      runWithPrimStep (stepAuthCpaCutoffSlotPrim cut S) A.run
        (0, AuthHybridStateFixed.empty S true)
    finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState

noncomputable def cpaSlotAfterStepUntil (idx : Nat) (S : Setup) (P : Primitives)
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
      (runWithPrimStepFuel false (stepAuthCpaCutoffSlotPrim idx S) (cont resp) fuel (idx + 1, hst'))
    simulateQ (primBaseImpl P)
      (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)

/-- 1-step creation-order `IND-CPA` simulation world at fixed `(idx, secb)` before `== secb`. -/
noncomputable def cpaSlotStepWorld (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool) (fuel : Nat) (A : AuthAdversary S) : ProbComp Bool :=
  simulateQ (primBaseImpl P)
    (stepUntilAuthCpaChallengeSlotPrim idx S false A.run fuel
      (0, AuthHybridStateFixed.empty S true)) >>=
    cpaSlotAfterStepUntil idx S P secb fuel

private theorem simulateQ_tryPauseSlot_and_cpaAfter_eq
    (idx : Nat) (S : Setup) (P : Primitives) (secb : Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : AuthCpaSlotState S) (cont : AuthResponse → OracleComp (unifSpec + authSpec S) Bool)
    (Q' fuel1' fuel2 : Nat)
    (h_cont : ∀ r, IsQueryBoundP (cont r) (fun q => isGameQuery q = true) Q') (h2 : Q' ≤ fuel2)
    (ih : ∀ r s',
      (simulateQ (primBaseImpl P)
        (stepUntilAuthCpaChallengeSlotPrim idx S false (cont r) fuel1' s') >>=
        cpaSlotAfterStepUntil idx S P secb fuel2) =
      (simulateQ (primBaseImpl P)
        (runWithPrimStep (stepAuthCpaCutoffSlotPrim (if secb then idx else idx + 1) S)
          (cont r) s') >>=
        fun (b', (_, finalSt)) =>
          simulateQ (primBaseImpl P)
            (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState))) :
    (simulateQ (primBaseImpl P)
      (do
        let stepRes ← tryPauseAuthCpaSendSlotPrim true idx S sid u bundle m0 m1 shst
        match stepRes with
        | .inl (resp, s') => stepUntilAuthCpaChallengeSlotPrim idx S false (cont resp) fuel1' s'
        | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
      cpaSlotAfterStepUntil idx S P secb fuel2) =
    (simulateQ (primBaseImpl P)
      (runAuthSendCpaCutoffSlotPrim (if secb then idx else idx + 1) S sid u bundle m0 m1 shst >>=
        fun p => runWithPrimStep
          (stepAuthCpaCutoffSlotPrim (if secb then idx else idx + 1) S) (cont p.1) p.2) >>=
      fun (b', (_, finalSt)) =>
        simulateQ (primBaseImpl P)
          (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)) := by
  rcases shst with ⟨ns, hst⟩
  have hCut : ∀ sIdx, sIdx ≠ idx →
      decide (sIdx < idx) = decide (sIdx < if secb then idx else idx + 1) := fun sIdx hNe => by
    cases secb
    · simp; omega
    · rfl
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
      apply bind_congr; intro prep?; cases prep? with
      | none => simp only [Option.map_none, simulateQ_pure, pure_bind]; exact ih .noneResp (ns, hst)
      | some pair =>
        rcases pair with ⟨isFreshPeer, isIdealSend, rawP⟩; simp only [Option.map_some]
        by_cases hFresh : isFreshPeer = true
        · simp only [hFresh, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.false_eq_true]
          by_cases hIdx : (ns == idx) = true
          · have hsIdx : ns = idx := beq_iff_eq.mp hIdx; subst hsIdx
            have hPlain : (if decide (ns < if secb = true then ns else ns + 1) = true
                then m0 else m1) = (if secb = true then m1 else m0) := by cases secb <;> simp
            simp only [hIdx, ↓reduceIte, simulateQ_pure, pure_bind, cpaSlotAfterStepUntil, hLenEq,
              simulateQ_bind, simulateQ_embedUnif, bind_assoc, finishAuthCpaSendFixedPure_msgPlain_irrel]
            apply bind_congr; intro mk; simp only [hPlain, simulateQ_primQ_aeadEnc_bytes, pure_bind]
            let fin := finishAuthCpaSendFixedPure true true (withSid sid rawP)
              (P.aeadEnc mk (withSid sid rawP).ad (if secb = true then m1 else m0)) hst
            rw [runWithPrimStepFuel_eq_runWithPrimStep false (stepAuthCpaCutoffSlotPrim ns S)
                  (cont fin.1) Q' fuel2 (h_cont _) h2 (ns + 1, fin.2),
                runWithPrimStep_stepAuthCpaCutoffSlotPrim_eq_of_le ns
                  (if secb = true then ns else ns + 1) S (cont fin.1) (ns + 1, fin.2)
                  (Nat.le_succ ns) (by cases secb <;> simp)]
          · have hCutSid := hCut ns (beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hIdx))
            simp only [hIdx, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
              bind_assoc]
            apply bind_congr; intro mk; rw [hCutSid]; apply bind_congr; intro aeadCt
            simp only [simulateQ_pure, pure_bind]; exact ih _ _
        · simp only [hFresh, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, bind_assoc]
          apply bind_congr; intro mk; apply bind_congr; intro aeadCt
          simp only [simulateQ_pure, pure_bind]; exact ih _ _

private theorem stepUntilSlot_nonSend (idx : Nat) (S : Setup) {α : Type} (dflt : α)
    (gq : AuthQuery S) (h : ¬ isAuthSendQuery (Sum.inr gq))
    (cont : (unifSpec + authSpec S).Range (Sum.inr gq) → OracleComp (unifSpec + authSpec S) α)
    (f : Nat) (shst : AuthCpaSlotState S) :
    stepUntilAuthCpaChallengeSlotPrim idx S dflt (liftM (OracleSpec.query (Sum.inr gq)) >>= cont)
      (f + 1) shst =
    (stepAuthCpaNonSendPrim S gq shst.2 >>=
      fun p => stepUntilAuthCpaChallengeSlotPrim idx S dflt (cont p.1) f (shst.1, p.2)) := by
  cases gq <;> first | exact False.elim (h trivial) | rfl

theorem simulateQ_stepUntilSlot_and_cpaAfter_eq_cutoff (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool)
    (mx : OracleComp (unifSpec + authSpec S) Bool)
    (Q fuel1 fuel2 : Nat)
    (h_mx : IsQueryBoundP mx (fun q => isGameQuery q = true) Q)
    (h1 : Q ≤ fuel1) (h2 : Q ≤ fuel2)
    (shst : AuthCpaSlotState S) :
    (simulateQ (primBaseImpl P) (stepUntilAuthCpaChallengeSlotPrim idx S false mx fuel1 shst) >>=
      cpaSlotAfterStepUntil idx S P secb fuel2) =
    (simulateQ (primBaseImpl P)
      (runWithPrimStep (stepAuthCpaCutoffSlotPrim (if secb then idx else idx + 1) S) mx shst) >>=
      fun (b', (_, finalSt)) =>
        simulateQ (primBaseImpl P)
          (finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState)) := by
  induction mx using OracleComp.inductionOn generalizing Q fuel1 shst with
  | pure x =>
    rw [stepUntilAuthCpaChallengeSlotPrim_pure, runWithPrimStep_pure]
    rcases shst with ⟨ns, hst⟩; simp [cpaSlotAfterStepUntil]
  | query_bind q cont ih =>
    rw [isQueryBoundP_query_bind_iff] at h_mx; cases q with
    | inl n =>
      rcases h_mx with ⟨_, h_cont⟩
      have hnl : ¬ (isGameQuery (Sum.inl n : ℕ ⊕ AuthQuery S) = true) := by simp [isGameQuery]
      simp only [hnl] at h_cont
      rw [stepUntilAuthCpaChallengeSlotPrim_query_inl, runWithPrimStep_query_inl]
      simp only [simulateQ_bind, bind_assoc]; congr 1; funext u
      exact ih u Q fuel1 (h_cont u) h1 h2 shst
    | inr gq =>
      rcases h_mx with ⟨h_first, h_cont⟩
      have hgr : isGameQuery (Sum.inr gq : ℕ ⊕ AuthQuery S) = true := rfl
      rcases h_first with h_abs | hQpos
      · exact False.elim (h_abs hgr)
      · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
        obtain ⟨fuel1', rfl⟩ : ∃ fuel1', fuel1 = fuel1' + 1 := ⟨fuel1 - 1, by omega⟩
        simp only [hgr, ↓reduceIte, Nat.add_sub_cancel] at h_cont; rw [runWithPrimStep_query_inr]
        cases gq with
        | sendOPK u i bundle m0 m1 =>
          change (simulateQ (primBaseImpl P) (if bundle.opkB?.isNone then
              stepUntilAuthCpaChallengeSlotPrim idx S false (cont .noneResp) fuel1' shst
            else do
              let stepRes ← tryPauseAuthCpaSendSlotPrim true idx S (.sendOPK u i) u bundle m0 m1 shst
              match stepRes with
              | .inl (resp, s') =>
                stepUntilAuthCpaChallengeSlotPrim idx S false (cont resp) fuel1' s'
              | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
            cpaSlotAfterStepUntil idx S P secb fuel2) = _
          unfold stepAuthCpaCutoffSlotPrim; dsimp only; split
          · exact ih .noneResp Q' fuel1' (h_cont .noneResp) (by omega) (by omega) shst
          · exact simulateQ_tryPauseSlot_and_cpaAfter_eq idx S P secb (.sendOPK u i) u bundle m0 m1
              shst cont Q' fuel1' fuel2 h_cont (by omega)
              (fun r s' => ih r Q' fuel1' (h_cont r) (by omega) (by omega) s')
        | sendNoOPK u i bundle m0 m1 =>
          change (simulateQ (primBaseImpl P) (if bundle.opkB?.isSome then
              stepUntilAuthCpaChallengeSlotPrim idx S false (cont .noneResp) fuel1' shst
            else do
              let stepRes ←
                tryPauseAuthCpaSendSlotPrim true idx S (.sendNoOPK u i) u bundle m0 m1 shst
              match stepRes with
              | .inl (resp, s') =>
                stepUntilAuthCpaChallengeSlotPrim idx S false (cont resp) fuel1' s'
              | .inr (ad, m0', m1', payload, s') => pure (.paused ad m0' m1' payload s' cont)) >>=
            cpaSlotAfterStepUntil idx S P secb fuel2) = _
          unfold stepAuthCpaCutoffSlotPrim; dsimp only; split
          · exact ih .noneResp Q' fuel1' (h_cont .noneResp) (by omega) (by omega) shst
          · exact simulateQ_tryPauseSlot_and_cpaAfter_eq idx S P secb (.sendNoOPK u i) u bundle
              m0 m1 shst cont Q' fuel1' fuel2 h_cont (by omega)
              (fun r s' => ih r Q' fuel1' (h_cont r) (by omega) (by omega) s')
        | _ =>
          rw [stepUntilSlot_nonSend idx S false _ (by simp [isAuthSendQuery]) cont fuel1' shst]
          dsimp only [stepAuthCpaCutoffSlotPrim]; simp only [simulateQ_bind, bind_assoc, pure_bind]
          congr 1; funext p; exact ih p.1 Q' fuel1' (h_cont p.1) (by omega) (by omega) (shst.1, p.2)

theorem cpaSlotStepWorld_eq_authCpaSlotCutoffExp (idx : Nat) (S : Setup) (P : Primitives)
    (secb : Bool)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    cpaSlotStepWorld idx S P secb b.q_total A.1 =
      authCpaSlotCutoffExp (if secb then idx else idx + 1) S P A.1 := by
  unfold cpaSlotStepWorld authCpaSlotCutoffExp
  rw [simulateQ_stepUntilSlot_and_cpaAfter_eq_cutoff idx S P secb
    A.1.run b.q_total b.q_total b.q_total (SignalPqxdh.QueryBounded.auth_total A.property) (le_refl _) (le_refl _)
    (0, AuthHybridStateFixed.empty S true), simulateQ_bind]

private theorem evalDist_cpaSlotInner_eq_cpaSlotAfterStepUntil
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
        (resumeAuthCpaAfterChallengeSlotPrim idx S fuel res' (some ct))
      return (b' == secb))] =
    𝒟[cpaSlotAfterStepUntil idx S P secb fuel res >>= fun z => pure (z == secb)] := by
  cases res with
  | done b' shst =>
    rcases shst with ⟨ns, hst⟩
    simp only [simulateQ_pure, pure_bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      resumeAuthCpaAfterChallengeSlotPrim, cpaSlotAfterStepUntil, OracleComp.evalDist_bind_const]
  | paused ad m0 m1 p shst cont =>
    rcases shst with ⟨ns, hst⟩
    by_cases hLen : (m0.length == m1.length) = true
    · have hBne : (m0.length != m1.length) = false := by revert hLen; simp
      simp only [hLen, hBne, ↓reduceIte, Bool.false_eq_true, simulateQ_pure, pure_bind,
        resumeAuthCpaAfterChallengeSlotPrim, cpaSlotAfterStepUntil, Option.getD_some,
        simulateQ_bind, bind_assoc]
    · have hLenF : (m0.length == m1.length) = false := Bool.eq_false_iff.mpr hLen
      simp only [hLenF, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, pure_bind,
        bne_self_eq_false, resumeAuthCpaAfterChallengeSlotPrim, cpaSlotAfterStepUntil,
        Option.getD_some, simulateQ_bind, bind_assoc]

theorem evalDist_aeadIndCpaExp_aeadCpaReductionAuthFixed_eq
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[aeadIndCpaExp P (aeadCpaReductionAuthFixed S b A)] =
      𝒟[(do
        let secb ← $ᵗ Bool
        let z ← if secb then
          (sampleIndexRange (min b.q_total S.N_send_tot) >>=
            fun idx => cpaSlotStepWorld idx S P true b.q_total A.1)
        else
          (sampleIndexRange (min b.q_total S.N_send_tot) >>=
            fun idx => cpaSlotStepWorld idx S P false b.q_total A.1)
        return (secb == z))] := by
  unfold aeadIndCpaExp aeadCpaReductionAuthFixed aeadCpaReductionAuthSlotChoose
    aeadCpaReductionAuthSlotAtChoose aeadCpaReductionAuthSlotDist cpaSlotStepWorld BoundedAdv at *
  dsimp only
  simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  rw [OracleComp.evalDist_bind_bind_swap sampleMessageKeys80
    (sampleIndexRange (min b.q_total S.N_send_tot))]
  trans 𝒟[(sampleIndexRange (min b.q_total S.N_send_tot) >>= fun idx =>
      simulateQ (primBaseImpl P)
        (stepUntilAuthCpaChallengeSlotPrim idx S false A.1.run b.q_total
          (0, AuthHybridStateFixed.empty S true)) >>= fun res =>
        cpaSlotAfterStepUntil idx S P secb b.q_total res >>= fun z => pure (z == secb))]
  · refine OracleComp.evalDist_bind_congr_of_support (sampleIndexRange (min b.q_total S.N_send_tot))
      _ _ (fun idx _ => ?_)
    rw [OracleComp.evalDist_bind_bind_swap sampleMessageKeys80
      (simulateQ (primBaseImpl P)
        (stepUntilAuthCpaChallengeSlotPrim idx S false A.1.run b.q_total
          (0, AuthHybridStateFixed.empty S true)))]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun res _ => ?_)
    exact evalDist_cpaSlotInner_eq_cpaSlotAfterStepUntil idx S P secb b.q_total res
  · cases secb <;> simp [Bool.beq_comm]

/-- Sum/average telescoping identity for creation-order `authCpaSlotCutoffExp`
    (`0 .. min b.q_total S.N_send_tot`). -/
theorem abs_sub_authCpaSlotCutoffExp_eq_mul_aeadIndCpa
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authCpaSlotCutoffExp 0 S P A.1] {true}).toReal -
     (𝒟[authCpaSlotCutoffExp (min b.q_total S.N_send_tot) S P A.1] {true}).toReal| =
      ((min b.q_total S.N_send_tot : Nat) : ℝ) *
        AeadIndCpaReal P (aeadCpaReductionAuthFixed S b A) := by
  let M := min b.q_total S.N_send_tot
  have hSumT : (M : ℝ) * (𝒟[sampleIndexRange M >>=
      fun idx => cpaSlotStepWorld idx S P true b.q_total A.1] {true}).toReal =
      ∑ idx ∈ Finset.range M, (𝒟[authCpaSlotCutoffExp idx S P A.1] {true}).toReal := by
    rw [mul_toReal_sampleIndexRange_bind_eq_sum]
    refine Finset.sum_congr rfl (fun idx _ => ?_)
    rw [cpaSlotStepWorld_eq_authCpaSlotCutoffExp idx S P true b A]; rfl
  have hSumF : (M : ℝ) * (𝒟[sampleIndexRange M >>=
      fun idx => cpaSlotStepWorld idx S P false b.q_total A.1] {true}).toReal =
      ∑ idx ∈ Finset.range M, (𝒟[authCpaSlotCutoffExp (idx + 1) S P A.1] {true}).toReal := by
    rw [mul_toReal_sampleIndexRange_bind_eq_sum]
    refine Finset.sum_congr rfl (fun idx _ => ?_)
    rw [cpaSlotStepWorld_eq_authCpaSlotCutoffExp idx S P false b A]; rfl
  have hTel : ∑ idx ∈ Finset.range M, (𝒟[authCpaSlotCutoffExp idx S P A.1] {true}).toReal -
      ∑ idx ∈ Finset.range M, (𝒟[authCpaSlotCutoffExp (idx + 1) S P A.1] {true}).toReal =
      (𝒟[authCpaSlotCutoffExp 0 S P A.1] {true}).toReal -
        (𝒟[authCpaSlotCutoffExp M S P A.1] {true}).toReal := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_range_sub' (fun idx => (𝒟[authCpaSlotCutoffExp idx S P A.1] {true}).toReal) M
  have hDiff : (𝒟[authCpaSlotCutoffExp 0 S P A.1] {true}).toReal -
      (𝒟[authCpaSlotCutoffExp M S P A.1] {true}).toReal =
      (M : ℝ) * ((𝒟[sampleIndexRange M >>=
          fun idx => cpaSlotStepWorld idx S P true b.q_total A.1] {true}).toReal -
        (𝒟[sampleIndexRange M >>=
          fun idx => cpaSlotStepWorld idx S P false b.q_total A.1] {true}).toReal) := by linarith
  have hAdv : AeadIndCpaReal P (aeadCpaReductionAuthFixed S b A) =
      |(𝒟[sampleIndexRange M >>=
          fun idx => cpaSlotStepWorld idx S P true b.q_total A.1] {true}).toReal -
       (𝒟[sampleIndexRange M >>=
          fun idx => cpaSlotStepWorld idx S P false b.q_total A.1] {true}).toReal| := by
    unfold AeadIndCpaReal AeadIndCpa
    rw [evalDist_aeadIndCpaExp_aeadCpaReductionAuthFixed_eq S P b A,
        evalDist_boolBias_bind_uniformBool, MeasureTheory.Measure.toReal_boolDist]
  rw [hDiff, abs_mul, abs_of_nonneg (Nat.cast_nonneg M), hAdv]

private theorem isQueryBoundP_mono_authSend {S : Setup} {α : Type}
    {P2 : (Nat ⊕ AuthQuery S) → Prop} [DecidablePred P2]
    (hImp : ∀ q, isAuthSendQuery q → P2 q) {mx : OracleComp (unifSpec + authSpec S) α} {m n : Nat}
    (hmn : m ≤ n) (h : IsQueryBoundP mx P2 m) : IsQueryBoundP mx isAuthSendQuery n := by
  induction mx using OracleComp.inductionOn generalizing m n with
  | pure _ => trivial
  | query_bind q cont ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢; rcases h with ⟨hFirst, hCont⟩
    refine ⟨?_, fun r => ?_⟩
    · rcases hFirst with hnP2 | _
      · exact Or.inl (fun hP1 => hnP2 (hImp q hP1))
      · exact Or.inr (by omega)
    · by_cases h1 : isAuthSendQuery q
      · have h2 : P2 q := hImp q h1; simp only [h1, h2, ↓reduceIte] at hCont ⊢
        rcases hFirst with hnP2 | _
        · exact False.elim (hnP2 h2)
        · exact ih r (by omega) (hCont r)
      · simp only [h1, ↓reduceIte]; by_cases h2 : P2 q
        · simp only [h2, ↓reduceIte] at hCont; exact ih r (by omega) (hCont r)
        · simp only [h2, ↓reduceIte] at hCont; exact ih r hmn (hCont r)

private theorem runAuthSendCpaCutoffSlotPrim_map_snd_eq (cut1 cut2 : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : AuthCpaSlotState S)
    (hDec : decide (shst.1 < cut1) = decide (initSessionSlotIdx sid < cut2)) :
    Prod.map id Prod.snd <$> runAuthSendCpaCutoffSlotPrim cut1 S sid u bundle m0 m1 shst =
      runAuthSendCpaCutoffPrim cut2 S sid u bundle m0 m1 shst.2 := by
  rcases shst with ⟨ns, hst⟩; dsimp only at hDec ⊢
  unfold runAuthSendCpaCutoffSlotPrim tryPauseAuthCpaSendSlotPrim
    runAuthSendCpaCutoffPrim tryPauseAuthCpaSendFixedPrim
  dsimp only; split
  · simp only [pure_bind, map_pure, Prod.map, id_eq]
  · split
    · simp only [pure_bind, map_pure, Prod.map, id_eq]
    · simp only [bind_assoc, map_bind]; apply bind_congr; intro prep?; cases prep? with
      | none => simp only [pure_bind, map_pure, Prod.map, id_eq]
      | some t =>
        rcases t with ⟨isFreshPeer, isIdealSend, rawP⟩; dsimp only; split
        · rw [hDec]; simp only [Bool.false_and, ↓reduceIte, Bool.false_eq_true, bind_assoc]
          apply bind_congr; intro mk; apply bind_congr; intro aeadCt
          simp only [pure_bind, map_pure, Prod.map, id_eq, Prod.mk.eta]
        · simp only [bind_assoc]; apply bind_congr; intro mk; apply bind_congr; intro aeadCt
          simp only [pure_bind, map_pure, Prod.map, id_eq, Prod.mk.eta]
private theorem stepAuthCpaCutoffSlotPrim_nonSend_map_snd_eq (cut1 cut2 : Nat) (S : Setup)
    (gq : AuthQuery S) (h : ¬ isAuthSendQuery (Sum.inr gq)) (shst : AuthCpaSlotState S) :
    Prod.map id Prod.snd <$> stepAuthCpaCutoffSlotPrim cut1 S gq shst =
      stepAuthCpaCutoffPrim cut2 S gq shst.2 := by
  cases gq <;> first | exact False.elim (h trivial) | (
    unfold stepAuthCpaCutoffSlotPrim stepAuthCpaCutoffPrim; dsimp only; rw [map_bind]
    conv_rhs => rw [← bind_pure (stepAuthCpaNonSendPrim S _ shst.2)]
    apply bind_congr; rintro ⟨_, _⟩; simp only [map_pure, Prod.map, id_eq])
private theorem stepAuthCpaCutoffSlotPrim_zero_map_snd_eq (S : Setup) (gq : AuthQuery S)
    (shst : AuthCpaSlotState S) :
    Prod.map id Prod.snd <$> stepAuthCpaCutoffSlotPrim 0 S gq shst =
      stepAuthCpaCutoffPrim 0 S gq shst.2 := by
  by_cases hSend : isAuthSendQuery (Sum.inr gq)
  · cases gq <;> try exact False.elim hSend
    · unfold stepAuthCpaCutoffSlotPrim stepAuthCpaCutoffPrim; dsimp only; split
      · simp only [map_pure, Prod.map, id_eq]
      · exact runAuthSendCpaCutoffSlotPrim_map_snd_eq 0 0 S _ _ _ _ _ shst (by simp)
    · unfold stepAuthCpaCutoffSlotPrim stepAuthCpaCutoffPrim; dsimp only; split
      · simp only [map_pure, Prod.map, id_eq]
      · exact runAuthSendCpaCutoffSlotPrim_map_snd_eq 0 0 S _ _ _ _ _ shst (by simp)
  · exact stepAuthCpaCutoffSlotPrim_nonSend_map_snd_eq 0 0 S gq hSend shst
theorem authCpaSlotCutoffExp_zero_eq (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authCpaSlotCutoffExp 0 S P A = authCpaCutoffExp 0 S P A := by
  have hRun : ∀ {α : Type} (mx : OracleComp (unifSpec + authSpec S) α) (shst : AuthCpaSlotState S),
      Prod.map id Prod.snd <$> runWithPrimStep (stepAuthCpaCutoffSlotPrim 0 S) mx shst =
        runWithPrimStep (stepAuthCpaCutoffPrim 0 S) mx shst.2 := by
    intro α mx; induction mx using OracleComp.inductionOn with
    | pure _ => intro shst; rw [runWithPrimStep_pure, runWithPrimStep_pure]; simp [Prod.map]
    | query_bind q cont ih =>
      intro shst; cases q with
      | inl n =>
        rw [runWithPrimStep_query_inl, runWithPrimStep_query_inl, map_bind]
        congr 1; funext u; exact ih u shst
      | inr gq =>
        rw [runWithPrimStep_query_inr, runWithPrimStep_query_inr, map_bind,
            ← stepAuthCpaCutoffSlotPrim_zero_map_snd_eq S gq shst, bind_map_left]
        congr 1; funext p; exact ih p.1 p.2
  unfold authCpaSlotCutoffExp authCpaCutoffExp
  rw [← hRun A.run (0, AuthHybridStateFixed.empty S true), bind_map_left]; rfl
theorem authCpaSlotCutoffExp_min_eq (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    authCpaSlotCutoffExp (min b.q_total S.N_send_tot) S P A.1 =
      authCpaCutoffExp S.N_send_tot S P A.1 := by
  let M := min b.q_total S.N_send_tot
  have hRun : ∀ {α : Type} (mx : OracleComp (unifSpec + authSpec S) α)
      (Qs : Nat) (h_mx : IsQueryBoundP mx isAuthSendQuery Qs)
      (shst : AuthCpaSlotState S) (hInv : shst.1 + Qs ≤ M),
      Prod.map id Prod.snd <$> runWithPrimStep (stepAuthCpaCutoffSlotPrim M S) mx shst =
        runWithPrimStep (stepAuthCpaCutoffPrim S.N_send_tot S) mx shst.2 := by
    intro α mx; induction mx using OracleComp.inductionOn with
    | pure _ => intros; rw [runWithPrimStep_pure, runWithPrimStep_pure]; simp [Prod.map]
    | query_bind q cont ih =>
      intro Qs h_mx shst hInv; rw [isQueryBoundP_query_bind_iff] at h_mx
      rcases h_mx with ⟨hFirst, hCont⟩; cases q with
      | inl n =>
        have hFalse : ¬ isAuthSendQuery (Sum.inl n : Nat ⊕ AuthQuery S) := id
        simp only [hFalse, ↓reduceIte] at hCont
        rw [runWithPrimStep_query_inl, runWithPrimStep_query_inl, map_bind]
        congr 1; funext u; exact ih u Qs (hCont u) shst hInv
      | inr gq =>
        rw [runWithPrimStep_query_inr, runWithPrimStep_query_inr, map_bind]
        by_cases hSend : isAuthSendQuery (Sum.inr gq)
        · rcases hFirst with hAbs | hPos
          · exact False.elim (hAbs hSend)
          · simp only [hSend, ↓reduceIte] at hCont
            have hStep : Prod.map id Prod.snd <$> stepAuthCpaCutoffSlotPrim M S gq shst =
                stepAuthCpaCutoffPrim S.N_send_tot S gq shst.2 := by
              cases gq <;> try exact False.elim hSend
              · rename_i u i bundle m0 m1
                have hSidLt : initSessionSlotIdx (.sendOPK u i) < S.N_send_tot := by
                  have h1 := initSessionSlotIdx_sendOPK_lt u i; unfold Setup.N_send_tot; omega
                unfold stepAuthCpaCutoffSlotPrim stepAuthCpaCutoffPrim; dsimp only; split
                · simp only [map_pure, Prod.map, id_eq]
                · exact runAuthSendCpaCutoffSlotPrim_map_snd_eq M S.N_send_tot S
                    (.sendOPK u i) u bundle m0 m1 shst
                    (by rw [decide_eq_true (by omega), decide_eq_true hSidLt])
              · rename_i u i bundle m0 m1
                have hSidLt := initSessionSlotIdx_sendNoOPK_lt u i
                unfold stepAuthCpaCutoffSlotPrim stepAuthCpaCutoffPrim; dsimp only; split
                · simp only [map_pure, Prod.map, id_eq]
                · exact runAuthSendCpaCutoffSlotPrim_map_snd_eq M S.N_send_tot S
                    (.sendNoOPK u i) u bundle m0 m1 shst
                    (by rw [decide_eq_true (by omega), decide_eq_true hSidLt])
            rw [← hStep, bind_map_left]
            refine bind_congr_of_mem_support_spec _ _ _ (fun p hp => ?_)
            have hB := (stepAuthCpaCutoffSlotPrim_ns_le M S gq shst hp).2
            simp only [hSend, ↓reduceIte] at hB
            exact ih p.1 (Qs - 1) (hCont p.1) p.2 (by omega)
        · simp only [hSend, ↓reduceIte] at hCont
          rw [← stepAuthCpaCutoffSlotPrim_nonSend_map_snd_eq M S.N_send_tot S gq hSend shst,
              bind_map_left]
          refine bind_congr_of_mem_support_spec _ _ _ (fun p hp => ?_)
          have hB := (stepAuthCpaCutoffSlotPrim_ns_le M S gq shst hp).2
          simp only [hSend, ↓reduceIte, Nat.add_zero] at hB
          exact ih p.1 Qs (hCont p.1) p.2 (by omega)
  have hSendTot : IsQueryBoundP A.1.run isAuthSendQuery b.q_total :=
    isQueryBoundP_mono_authSend (P2 := fun q => isGameQuery q = true)
      (fun q h => by cases q with | inl _ => exact h.elim | inr _ => rfl) (le_refl _)
      (SignalPqxdh.QueryBounded.auth_total A.property)
  have hSendMin : IsQueryBoundP A.1.run isAuthSendQuery M := by
    by_cases h : b.q_total ≤ S.N_send_tot
    · dsimp [M]; rw [Nat.min_eq_left h]; exact hSendTot
    · dsimp [M]; rw [Nat.min_eq_right (Nat.le_of_not_le h)]; exact A.property.2.1
  unfold authCpaSlotCutoffExp authCpaCutoffExp
  rw [← hRun A.1.run M hSendMin (0, AuthHybridStateFixed.empty S true) (by dsimp [M]; omega),
      bind_map_left]; rfl

/-- Sum/average telescoping identity for `authCpaCutoffExp` (`0 .. S.N_send_tot`) via
    creation-order fresh-send slot clamp `min b.q_total S.N_send_tot`. -/
theorem abs_sub_authCpaCutoffExp_eq_mul_aeadIndCpa (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authCpaCutoffExp 0 S P A.1] {true}).toReal -
     (𝒟[authCpaCutoffExp S.N_send_tot S P A.1] {true}).toReal| =
      ((min b.q_total S.N_send_tot : Nat) : ℝ) *
        AeadIndCpaReal P (aeadCpaReductionAuthFixed S b A) := by
  rw [← authCpaSlotCutoffExp_zero_eq S P A.1, ← authCpaSlotCutoffExp_min_eq S P b A]
  exact abs_sub_authCpaSlotCutoffExp_eq_mul_aeadIndCpa S P b A

/-- Upper bound form `M_send * Adv ≤ S.N_send_tot * Adv` for `authCpaCutoffExp`. -/
theorem abs_sub_authCpaCutoffExp_le_mul_aeadIndCpa
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authCpaCutoffExp 0 S P A.1] {true}).toReal -
     (𝒟[authCpaCutoffExp S.N_send_tot S P A.1] {true}).toReal| ≤
      (S.N_send_tot : ℝ) * AeadIndCpaReal P (aeadCpaReductionAuthFixed S b A) := by
  rw [abs_sub_authCpaCutoffExp_eq_mul_aeadIndCpa S P b A]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.min_le_right _ _))
    (aeadIndCpa_nonneg _ _)

end SignalPqxdh.Security
