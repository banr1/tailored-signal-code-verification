/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyShCr -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfCk -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyAeadCpa -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfHmac -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK -- proof-setup: allow-public-import

/-!
# Shared Base Simulation Contracts for `Auth` Kind-Split Reductions

Shared predicates, query-count bounds, online list bounds, AVL random-oracle shadow relations,
and unified `StepSim` / `StepSimTwoStage` invariants (`AuthCoreInv`, `AuthCorePauseInv`) for the
kind-split `Auth` reductions (`shcr`, `ck`, `mk`, `int`, and `cpa`), together with their atomic
reference reductions and 12-way query dispatch lemma.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface CostedReduction TwoStageCostedReduction
   pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.ReductionDsl.StepSim (isGamePred bumpPred)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy embedVal compRename tlAuthPrim tlPrfMk tlPrfHmac liftAuth1Stage liftAuth2Stage)
open _root_.SignalPqxdh
  (Setup QueryBudget AuthQuery AuthAdversary AuthState HasQueryBound authSpec
   isAuthOnlineQuery isAuthRoQuery isAuthRoRootQuery)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface pqPrfMkIface pqPrfHmacIface)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy authStateToVal)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (shcrStTy pauseTy shcrAuth1KeyDslProg AuthBaseListsBounded)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (authHybridStateFixedTy prfCkStTy prfMkStTy prfCkRedProg1Key prfMsgKeysRedProg1Key)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
  (cpaStTy cpaPayloadTy aeadCpaRedProg1Key)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
  (hmStTy prfHmacRedProg1Key)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy roListAtomicTy roRootListAtomicTy
   authBaseAtomicTy authFixedAtomicTy authBaseShadowStTy authFixedShadowStTy
   forgetAuthBaseShadow forgetAuthFixedShadow AuthRoBothValid
   authQueryAtomicTy authSendQAtomicTy authRecvQAtomicTy dispatchAuthQ)

/-- Four-slot query predicate family on `AuthQuery S` (`0` = online, `1` = `.roQuery`,
    `2` = `.roRootQuery`, `3` = total). -/
@[expose] def authSimPred (S : Setup) : Fin 4 → AuthQuery S → Prop
  | ⟨0, _⟩ => fun q => isAuthOnlineQuery (S := S) (.inr q)
  | ⟨1, _⟩ => fun q => isAuthRoQuery (S := S) (.inr q)
  | ⟨2, _⟩ => fun q => isAuthRoRootQuery (S := S) (.inr q)
  | ⟨3, _⟩ => fun _ => True

instance instDecidablePredAuthSimPred (S : Setup) (j : Fin 4) :
    DecidablePred (authSimPred S j) := fun q => by
  rcases j with ⟨_ | _ | _ | _ | n, hj⟩
  · dsimp [authSimPred]; infer_instance
  · dsimp [authSimPred]; infer_instance
  · dsimp [authSimPred]; infer_instance
  · dsimp [authSimPred]; exact isTrue trivial
  · omega

/-- Clamped per-slot query bounds for `authSimPred`. -/
@[expose] def authSimBounds (b : QueryBudget) : Fin 4 → ℕ
  | ⟨0, _⟩ => min b.q_on b.q_total
  | ⟨1, _⟩ => min b.q_ro b.q_total
  | ⟨2, _⟩ => min b.q_roRoot b.q_total
  | ⟨3, _⟩ => b.q_total

/-- Every `AuthQuery S` satisfies exactly one of the online, `.roQuery`, or `.roRootQuery` predicates. -/
theorem authSimPred_partition {S : Setup} (t : AuthQuery S) :
    (if authSimPred S 0 t then 1 else 0) +
      (if authSimPred S 1 t then 1 else 0) +
      (if authSimPred S 2 t then 1 else 0) = 1 := by
  cases t <;> rfl

private theorem isQueryBoundP_imp {ι₀ : Type} {spec : OracleSpec ι₀} {α : Type}
    {oa : OracleComp spec α} {p p₁ : ι₀ → Prop} [DecidablePred p] [DecidablePred p₁]
    (hImp : ∀ q, p q → p₁ q) {m : ℕ} (h₁ : oa.IsQueryBoundP p₁ m) :
    oa.IsQueryBoundP p m := by
  induction oa using OracleComp.inductionOn generalizing m with
  | pure x => exact isQueryBoundP_pure p x m
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases hp : p t
      · exact Or.inr (h₁.1.resolve_left (not_not.mpr (hImp t hp)))
      · exact Or.inl hp
    · refine (ih u (h₁.2 u)).mono ?_
      by_cases hp : p t
      · simp only [hp, hImp t hp, ite_true, le_refl]
      · simp only [hp, ite_false]; split <;> omega

/-- Bridges `HasQueryBound.QueryBounded A b` to per-slot `IsQueryBoundP` bounds under `authSimBounds`. -/
theorem authSimPred_bounded {S : Setup} (A : AuthAdversary S) (b : QueryBudget)
    (hQB : HasQueryBound.QueryBounded A b) :
    ∀ j : Fin 4,
      A.run.IsQueryBoundP (isGamePred (G := authSpec S) (authSimPred S j)) (authSimBounds b j) := by
  obtain ⟨hRo, _, _, hRoRoot, hTot, hOn⟩ := hQB
  intro j
  have hTotJ : A.run.IsQueryBoundP (isGamePred (G := authSpec S) (authSimPred S j)) b.q_total :=
    isQueryBoundP_imp (fun | .inl _, h => nomatch h | .inr _, _ => rfl) hTot
  rcases j with ⟨_ | _ | _ | _ | n, hj⟩
  · exact Computational.Proofs.ReductionDsl.StepSim.isQueryBoundP_min
      (isQueryBoundP_imp (fun | .inl _, h => nomatch h | .inr _, h => h) hOn) hTotJ
  · exact Computational.Proofs.ReductionDsl.StepSim.isQueryBoundP_min
      (isQueryBoundP_imp (fun | .inl _, h => nomatch h | .inr _, h => h) hRo) hTotJ
  · exact Computational.Proofs.ReductionDsl.StepSim.isQueryBoundP_min
      (isQueryBoundP_imp (fun | .inl _, h => nomatch h | .inr _, h => h) hRoRoot) hTotJ
  · exact hTotJ
  · omega

/-- Query-count invariant relating per-kind counts (`c 0`, `c 1`, `c 2`) and total count (`c 3`) to `b`. -/
structure AuthCounterInv (b : QueryBudget) (c : Fin 4 → ℕ) : Prop where
  sum_eq    : c 0 + c 1 + c 2 = c 3
  on_le     : c 0 ≤ min b.q_on b.q_total
  ro_le     : c 1 ≤ min b.q_ro b.q_total
  roRoot_le : c 2 ≤ min b.q_roRoot b.q_total
  tot_le    : c 3 ≤ b.q_total

theorem AuthCounterInv.zero (b : QueryBudget) : AuthCounterInv b 0 :=
  ⟨rfl, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem AuthCounterInv.bump {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    (t : AuthQuery S) (hInv : AuthCounterInv b c)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j) :
    AuthCounterInv b (bumpPred (authSimPred S) c t) := by
  have hPart := authSimPred_partition t
  have h0 := hroom 0; have h1 := hroom 1; have h2 := hroom 2
  have h3 : c 3 + 1 ≤ b.q_total := hroom 3 trivial
  have hP3 : authSimPred S 3 t := trivial
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [bumpPred, hP3, ↓reduceIte]; have := hInv.sum_eq; omega
  · simp only [bumpPred]
    split_ifs with hp
    · exact h0 hp
    · simpa using hInv.on_le
  · simp only [bumpPred]
    split_ifs with hp
    · exact h1 hp
    · simpa using hInv.ro_le
  · simp only [bumpPred]
    split_ifs with hp
    · exact h2 hp
    · simpa using hInv.roRoot_le
  · simp only [bumpPred, hP3, ↓reduceIte]; exact h3

theorem AuthCounterInv.online_step_bounds {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {t : AuthQuery S} (hInv : AuthCounterInv b c) (hOn : authSimPred S 0 t)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j) :
    let F := AuthKindFuels.ofBudget S b
    c 0 + 1 ≤ F.K_on ∧ (c 0 + 1) + c 1 ≤ F.K_ro ∧ (c 0 + 1) + c 2 ≤ F.K_ro ∧ F.K_ro ≤ F.K_cap := by
  have h0 : c 0 + 1 ≤ min b.q_on b.q_total := hroom 0 hOn
  have h3 : c 3 + 1 ≤ b.q_total := hroom 3 trivial
  have := hInv.ro_le; have := hInv.roRoot_le; have := hInv.sum_eq
  dsimp only [AuthKindFuels.ofBudget]; omega

theorem AuthCounterInv.ro_step_bounds {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {t : AuthQuery S} (hInv : AuthCounterInv b c) (hRo : authSimPred S 1 t)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j) :
    let F := AuthKindFuels.ofBudget S b
    c 0 + (c 1 + 1) ≤ F.K_ro ∧ c 0 + (c 1 + 1) ≤ b.q_total ∧ F.K_ro ≤ F.K_cap := by
  have h1 : c 1 + 1 ≤ min b.q_ro b.q_total := hroom 1 hRo
  have h3 : c 3 + 1 ≤ b.q_total := hroom 3 trivial
  have := hInv.on_le; have := hInv.sum_eq
  dsimp only [AuthKindFuels.ofBudget]; omega

theorem AuthCounterInv.roRoot_step_bounds {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {t : AuthQuery S} (hInv : AuthCounterInv b c) (hRt : authSimPred S 2 t)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j) :
    let F := AuthKindFuels.ofBudget S b
    c 0 + (c 2 + 1) ≤ F.K_ro ∧ c 0 + (c 2 + 1) ≤ b.q_total ∧ F.K_ro ≤ F.K_cap := by
  have h2 : c 2 + 1 ≤ min b.q_roRoot b.q_total := hroom 2 hRt
  have h3 : c 3 + 1 ≤ b.q_total := hroom 3 trivial
  have := hInv.on_le; have := hInv.sum_eq
  dsimp only [AuthKindFuels.ofBudget]; omega

/-- Online list-length bound on `authStateTy.denote`. -/
structure AuthBaseValOnlineBounded (n : ℕ) (st : authStateTy.denote) : Prop where
  principals_le        : st.2.2.1.length ≤ n
  spkBundles_le        : st.2.2.2.1.length ≤ n
  opkEntries_le        : st.2.2.2.2.1.length ≤ n
  sessions_le          : st.2.2.2.2.2.1.length ≤ n
  usedSendSessions_le  : st.2.2.2.2.2.2.1.length ≤ n
  usedRecvOPK_le       : st.2.2.2.2.2.2.2.1.length ≤ n
  usedRecvNoOPK_le     : st.2.2.2.2.2.2.2.2.1.length ≤ n
  seenKyberBaseKeys_le : st.2.2.2.2.2.2.2.2.2.1.length ≤ n
  sentOPKEvents_le     : st.2.2.2.2.2.2.2.2.2.2.1.length ≤ n
  sentNoOPKEvents_le   : st.2.2.2.2.2.2.2.2.2.2.2.1.length ≤ n
  recvdOPKEvents_le    : st.2.2.2.2.2.2.2.2.2.2.2.2.1.length ≤ n
  recvdNoOPKEvents_le  : st.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length ≤ n
  advKeys_le           : st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.length ≤ n

/-- Online list-length bound on `authBaseAtomicTy.denote`. -/
structure AuthBaseAtomOnlineBounded (n : ℕ) (st : authBaseAtomicTy.denote) : Prop where
  principals_le        : st.2.2.1.length ≤ n
  spkBundles_le        : st.2.2.2.1.length ≤ n
  opkEntries_le        : st.2.2.2.2.1.length ≤ n
  sessions_le          : st.2.2.2.2.2.1.length ≤ n
  usedSendSessions_le  : st.2.2.2.2.2.2.1.length ≤ n
  usedRecvOPK_le       : st.2.2.2.2.2.2.2.1.length ≤ n
  usedRecvNoOPK_le     : st.2.2.2.2.2.2.2.2.1.length ≤ n
  seenKyberBaseKeys_le : st.2.2.2.2.2.2.2.2.2.1.length ≤ n
  sentOPKEvents_le     : st.2.2.2.2.2.2.2.2.2.2.1.length ≤ n
  sentNoOPKEvents_le   : st.2.2.2.2.2.2.2.2.2.2.2.1.length ≤ n
  recvdOPKEvents_le    : st.2.2.2.2.2.2.2.2.2.2.2.2.1.length ≤ n
  recvdNoOPKEvents_le  : st.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length ≤ n
  advKeys_le           : st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.length ≤ n

theorem AuthBaseValOnlineBounded.mono {m n : ℕ} (h : m ≤ n) {st : authStateTy.denote}
    (hb : AuthBaseValOnlineBounded m st) : AuthBaseValOnlineBounded n st where
  principals_le        := Nat.le_trans hb.principals_le h
  spkBundles_le        := Nat.le_trans hb.spkBundles_le h
  opkEntries_le        := Nat.le_trans hb.opkEntries_le h
  sessions_le          := Nat.le_trans hb.sessions_le h
  usedSendSessions_le  := Nat.le_trans hb.usedSendSessions_le h
  usedRecvOPK_le       := Nat.le_trans hb.usedRecvOPK_le h
  usedRecvNoOPK_le     := Nat.le_trans hb.usedRecvNoOPK_le h
  seenKyberBaseKeys_le := Nat.le_trans hb.seenKyberBaseKeys_le h
  sentOPKEvents_le     := Nat.le_trans hb.sentOPKEvents_le h
  sentNoOPKEvents_le   := Nat.le_trans hb.sentNoOPKEvents_le h
  recvdOPKEvents_le    := Nat.le_trans hb.recvdOPKEvents_le h
  recvdNoOPKEvents_le  := Nat.le_trans hb.recvdNoOPKEvents_le h
  advKeys_le           := Nat.le_trans hb.advKeys_le h

theorem AuthBaseAtomOnlineBounded.mono {m n : ℕ} (h : m ≤ n) {st : authBaseAtomicTy.denote}
    (hb : AuthBaseAtomOnlineBounded m st) : AuthBaseAtomOnlineBounded n st where
  principals_le        := Nat.le_trans hb.principals_le h
  spkBundles_le        := Nat.le_trans hb.spkBundles_le h
  opkEntries_le        := Nat.le_trans hb.opkEntries_le h
  sessions_le          := Nat.le_trans hb.sessions_le h
  usedSendSessions_le  := Nat.le_trans hb.usedSendSessions_le h
  usedRecvOPK_le       := Nat.le_trans hb.usedRecvOPK_le h
  usedRecvNoOPK_le     := Nat.le_trans hb.usedRecvNoOPK_le h
  seenKyberBaseKeys_le := Nat.le_trans hb.seenKyberBaseKeys_le h
  sentOPKEvents_le     := Nat.le_trans hb.sentOPKEvents_le h
  sentNoOPKEvents_le   := Nat.le_trans hb.sentNoOPKEvents_le h
  recvdOPKEvents_le    := Nat.le_trans hb.recvdOPKEvents_le h
  recvdNoOPKEvents_le  := Nat.le_trans hb.recvdNoOPKEvents_le h
  advKeys_le           := Nat.le_trans hb.advKeys_le h

private theorem embedVal_fst {a b : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (x : (Ty.prod a b).denote) : (embedVal (.prod a b) x).1 = embedVal a x.1 := rfl

private theorem embedVal_snd {a b : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (x : (Ty.prod a b).denote) : (embedVal (.prod a b) x).2 = embedVal b x.2 := rfl

private theorem embedVal_list {a : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (xs : (Ty.list a).denote) :
    embedVal (.list a) xs = List.map (embedVal a) xs := rfl

theorem AuthBaseAtomOnlineBounded.iff_embedVal {n : ℕ} (st : authStateTy.denote) :
    AuthBaseAtomOnlineBounded n (embedVal authStateTy st) ↔ AuthBaseValOnlineBounded n st := by
  constructor <;> intro h
  · exact
      { principals_le        := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.principals_le
        spkBundles_le        := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.spkBundles_le
        opkEntries_le        := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.opkEntries_le
        sessions_le          := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.sessions_le
        usedSendSessions_le  := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.usedSendSessions_le
        usedRecvOPK_le       := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.usedRecvOPK_le
        usedRecvNoOPK_le     := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.usedRecvNoOPK_le
        seenKyberBaseKeys_le := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.seenKyberBaseKeys_le
        sentOPKEvents_le     := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.sentOPKEvents_le
        sentNoOPKEvents_le   := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.sentNoOPKEvents_le
        recvdOPKEvents_le    := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.recvdOPKEvents_le
        recvdNoOPKEvents_le  := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.recvdNoOPKEvents_le
        advKeys_le           := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.advKeys_le }
  · exact
      { principals_le        := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.principals_le
        spkBundles_le        := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.spkBundles_le
        opkEntries_le        := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.opkEntries_le
        sessions_le          := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.sessions_le
        usedSendSessions_le  := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.usedSendSessions_le
        usedRecvOPK_le       := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.usedRecvOPK_le
        usedRecvNoOPK_le     := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.usedRecvNoOPK_le
        seenKyberBaseKeys_le := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.seenKyberBaseKeys_le
        sentOPKEvents_le     := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.sentOPKEvents_le
        sentNoOPKEvents_le   := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.sentNoOPKEvents_le
        recvdOPKEvents_le    := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.recvdOPKEvents_le
        recvdNoOPKEvents_le  := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.recvdNoOPKEvents_le
        advKeys_le           := by simpa only [authStateTy, embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.advKeys_le }

theorem AuthBaseValOnlineBounded.of_authStateToVal {S : Setup} {n : ℕ} {s : AuthState S}
    (h : AuthBaseListsBounded n s)
    (hSOE : s.sentOPKEvents.length ≤ n) (hSNE : s.sentNoOPKEvents.length ≤ n)
    (hROE : s.recvdOPKEvents.length ≤ n) (hRNE : s.recvdNoOPKEvents.length ≤ n) :
    AuthBaseValOnlineBounded n (authStateToVal s) where
  principals_le        := by simpa only [authStateToVal, List.length_map] using h.principals_le
  spkBundles_le        := by simpa only [authStateToVal, List.length_map] using h.spkBundles_le
  opkEntries_le        := by simpa only [authStateToVal, List.length_map] using h.opkEntries_le
  sessions_le          := by simpa only [authStateToVal, List.length_map] using h.sessions_le
  usedSendSessions_le  := by simpa only [authStateToVal, List.length_map] using h.usedSendSessions_le
  usedRecvOPK_le       := by simpa only [authStateToVal, List.length_map] using h.usedRecvOPK_le
  usedRecvNoOPK_le     := by simpa only [authStateToVal, List.length_map] using h.usedRecvNoOPK_le
  seenKyberBaseKeys_le := by simpa only [authStateToVal, List.length_map] using h.usedKyberTriples_le
  sentOPKEvents_le     := by simpa only [authStateToVal, List.length_map] using hSOE
  sentNoOPKEvents_le   := by simpa only [authStateToVal, List.length_map] using hSNE
  recvdOPKEvents_le    := by simpa only [authStateToVal, List.length_map] using hROE
  recvdNoOPKEvents_le  := by simpa only [authStateToVal, List.length_map] using hRNE
  advKeys_le           := by simpa only [authStateToVal] using h.advKeys_le

/-- Online list-length bound on `authHybridStateFixedTy.denote`. -/
structure AuthFixedValOnlineBounded (n : ℕ)
    (fhst : authHybridStateFixedTy.denote) : Prop where
  base_le          : AuthBaseValOnlineBounded n fhst.1.1
  initKemRecs_le   : fhst.1.2.1.length ≤ n
  recvKemRecs_le   : fhst.1.2.2.1.length ≤ n
  idealSessions_le : fhst.1.2.2.2.length ≤ n
  mkSaltCache_le   : fhst.2.2.1.length ≤ n

/-- Online list-length bound on `authFixedAtomicTy.denote`. -/
structure AuthFixedAtomOnlineBounded (n : ℕ)
    (fhst : authFixedAtomicTy.denote) : Prop where
  base_le          : AuthBaseAtomOnlineBounded n fhst.1.1
  initKemRecs_le   : fhst.1.2.1.length ≤ n
  recvKemRecs_le   : fhst.1.2.2.1.length ≤ n
  idealSessions_le : fhst.1.2.2.2.length ≤ n
  mkSaltCache_le   : fhst.2.2.1.length ≤ n

theorem AuthFixedValOnlineBounded.mono {m n : ℕ} (h : m ≤ n)
    {fhst : authHybridStateFixedTy.denote}
    (hb : AuthFixedValOnlineBounded m fhst) : AuthFixedValOnlineBounded n fhst where
  base_le          := hb.base_le.mono h
  initKemRecs_le   := Nat.le_trans hb.initKemRecs_le h
  recvKemRecs_le   := Nat.le_trans hb.recvKemRecs_le h
  idealSessions_le := Nat.le_trans hb.idealSessions_le h
  mkSaltCache_le   := Nat.le_trans hb.mkSaltCache_le h

theorem AuthFixedAtomOnlineBounded.mono {m n : ℕ} (h : m ≤ n)
    {fhst : authFixedAtomicTy.denote}
    (hb : AuthFixedAtomOnlineBounded m fhst) : AuthFixedAtomOnlineBounded n fhst where
  base_le          := hb.base_le.mono h
  initKemRecs_le   := Nat.le_trans hb.initKemRecs_le h
  recvKemRecs_le   := Nat.le_trans hb.recvKemRecs_le h
  idealSessions_le := Nat.le_trans hb.idealSessions_le h
  mkSaltCache_le   := Nat.le_trans hb.mkSaltCache_le h

theorem AuthFixedAtomOnlineBounded.iff_embedVal {n : ℕ} (fhst : authHybridStateFixedTy.denote) :
    AuthFixedAtomOnlineBounded n (embedVal authHybridStateFixedTy fhst) ↔
      AuthFixedValOnlineBounded n fhst := by
  constructor <;> intro h
  · exact ⟨(AuthBaseAtomOnlineBounded.iff_embedVal fhst.1.1).mp h.base_le,
      by simpa only [embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.initKemRecs_le,
      by simpa only [embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.recvKemRecs_le,
      by simpa only [embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.idealSessions_le,
      by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authMkSaltCacheTy,
        embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.mkSaltCache_le⟩
  · exact ⟨(AuthBaseAtomOnlineBounded.iff_embedVal fhst.1.1).mpr h.base_le,
      by simpa only [embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.initKemRecs_le,
      by simpa only [embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.recvKemRecs_le,
      by simpa only [embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.idealSessions_le,
      by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authMkSaltCacheTy,
        embedVal_fst, embedVal_snd, embedVal_list, List.length_map] using h.mkSaltCache_le⟩

@[expose] def valRoCache (st : authStateTy.denote) := st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[expose] def valRootRoCache (st : authStateTy.denote) := st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[expose] def atomRoCache (st : authBaseAtomicTy.denote) : roListAtomicTy.denote :=
  st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[expose] def atomRootRoCache (st : authBaseAtomicTy.denote) : roRootListAtomicTy.denote :=
  st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Dual AVL random-oracle shadow relation combining `AuthRoBothValid` with key uniqueness on both caches. -/
structure RoBothShadowRel (cap : ℕ)
    (st : authBaseAtomicTy.denote) (avls : roBothAvlTy.denote) : Prop where
  both_valid : AuthRoBothValid cap avls (atomRoCache st) (atomRootRoCache st)
  ro_nodup   : ((atomRoCache st).map Prod.fst).Nodup
  root_nodup : ((atomRootRoCache st).map Prod.fst).Nodup

/-- Single-step relation asserting that a cache either stays unchanged or prepends one fresh key-value entry. -/
@[expose] def CacheStepAtMostOne {K V : Type} [BEq K] (l l' : List (K × V)) : Prop :=
  l' = l ∨ ∃ k v, (l.find? (fun p => p.1 == k)).isNone = true ∧ l' = (k, v) :: l

theorem CacheStepAtMostOne.refl {K V : Type} [BEq K] (l : List (K × V)) :
    CacheStepAtMostOne l l :=
  Or.inl rfl

theorem CacheStepAtMostOne.length_le {K V : Type} [BEq K] {l l' : List (K × V)}
    (h : CacheStepAtMostOne l l') : l'.length ≤ l.length + 1 := by
  rcases h with rfl | ⟨_, _, _, rfl⟩ <;> simp

abbrev authShcrShadowStTy : Ty pqAtomicSig := .prod (embedTy shcrStTy) roBothAvlTy
abbrev authCkShadowStTy   : Ty pqAtomicSig := .prod (embedTy prfCkStTy) roBothAvlTy
abbrev authMkShadowStTy   : Ty pqAtomicSig := .prod (embedTy prfMkStTy) roBothAvlTy
abbrev authHmShadowStTy   : Ty pqAtomicSig := .prod (embedTy hmStTy) roBothAvlTy
abbrev authCpaShadowStTy  : Ty pqAtomicSig := .prod (embedTy cpaStTy) roBothAvlTy

@[expose] def forgetShcr (s' : authShcrShadowStTy.denote) : (embedTy shcrStTy).denote := s'.1
@[expose] def forgetCk   (s' : authCkShadowStTy.denote)   : (embedTy prfCkStTy).denote := s'.1
@[expose] def forgetMk   (s' : authMkShadowStTy.denote)   : (embedTy prfMkStTy).denote := s'.1
@[expose] def forgetHm   (s' : authHmShadowStTy.denote)   : (embedTy hmStTy).denote := s'.1
@[expose] def forgetCpa  (s' : authCpaShadowStTy.denote)  : (embedTy cpaStTy).denote := s'.1

@[expose] def shcrOldAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
      (.prod (PB 32) (PB 1568)) (PB 1568) :=
  liftAuth2Stage tlAuthPrim S (shcrAuth1KeyDslProg S b)

@[expose] def prfCkOldAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool .bool :=
  liftAuth1Stage tlAuthPrim S (prfCkRedProg1Key S b.q_total)

@[expose] def prfMkOldAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqPrfMkIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool :=
  liftAuth1Stage tlPrfMk S (prfMsgKeysRedProg1Key S b.q_total)

abbrev prfMsgKeysOldAtomicProg := prfMkOldAtomicProg

@[expose] def aeadCpaOldAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      .unit .unit .bool (.prod (PB 158) (.prod (PB 32) (PB 32)))
      (.opt (PB 32)) .bool :=
  liftAuth2Stage tlAuthPrim S (aeadCpaRedProg1Key S b.q_total)

@[expose] def prfHmacOldAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqPrfHmacIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool :=
  liftAuth1Stage tlPrfHmac S (prfHmacRedProg1Key S b.q_total)

/-- Combined online-list and AVL random-oracle shadow invariant on `authBaseShadowStTy.denote`. -/
structure AuthBaseShadowAt (S : Setup) (b : QueryBudget)
    (nOn nRo nRoot : ℕ) (bs : authBaseShadowStTy.denote) : Prop where
  online_le   : AuthBaseAtomOnlineBounded nOn bs.1
  ro_len_le   : (atomRoCache bs.1).length ≤ nRo
  root_len_le : (atomRootRoCache bs.1).length ≤ nRoot
  ro_shadow   : RoBothShadowRel (AuthKindFuels.ofBudget S b).K_cap bs.1 bs.2

/-- Combined online-list and AVL random-oracle shadow invariant on `authFixedShadowStTy.denote`. -/
structure AuthFixedShadowAt (S : Setup) (b : QueryBudget)
    (nOn nRo nRoot : ℕ) (fs : authFixedShadowStTy.denote) : Prop where
  online_le   : AuthFixedAtomOnlineBounded nOn fs.1
  ro_len_le   : (atomRoCache fs.1.1.1).length ≤ nRo
  root_len_le : (atomRootRoCache fs.1.1.1).length ≤ nRoot
  ro_shadow   : RoBothShadowRel (AuthKindFuels.ofBudget S b).K_cap fs.1.1.1 fs.2

theorem AuthBaseShadowAt.mono {S : Setup} {b : QueryBudget}
    {nOn nOn' nRo nRo' nRoot nRoot' : ℕ} (hOn : nOn ≤ nOn') (hRo : nRo ≤ nRo') (hRt : nRoot ≤ nRoot')
    {bs : authBaseShadowStTy.denote} (h : AuthBaseShadowAt S b nOn nRo nRoot bs) :
    AuthBaseShadowAt S b nOn' nRo' nRoot' bs :=
  ⟨h.online_le.mono hOn, Nat.le_trans h.ro_len_le hRo, Nat.le_trans h.root_len_le hRt, h.ro_shadow⟩

theorem AuthFixedShadowAt.mono {S : Setup} {b : QueryBudget}
    {nOn nOn' nRo nRo' nRoot nRoot' : ℕ} (hOn : nOn ≤ nOn') (hRo : nRo ≤ nRo') (hRt : nRoot ≤ nRoot')
    {fs : authFixedShadowStTy.denote} (h : AuthFixedShadowAt S b nOn nRo nRoot fs) :
    AuthFixedShadowAt S b nOn' nRo' nRoot' fs :=
  ⟨h.online_le.mono hOn, Nat.le_trans h.ro_len_le hRo, Nat.le_trans h.root_len_le hRt, h.ro_shadow⟩

/-- Unified `StepSim` and `StepSimTwoStage` state invariant pairing `AuthCounterInv` with a per-reduction shadow relation. -/
structure AuthCoreInv (b : QueryBudget) {σ' : Type}
    (ShadowAt : ℕ → ℕ → ℕ → σ' → Prop) (c : Fin 4 → ℕ) (s' : σ') : Prop where
  counter_inv : AuthCounterInv b c
  shadow_ok   : ShadowAt (c 0) (c 0 + c 1) (c 0 + c 2) s'

/-- Unified `StepSimTwoStage` pause invariant pairing `AuthCounterInv` with pre-resume shadow and payload relations. -/
structure AuthCorePauseInv (b : QueryBudget) {π' σ' : Type}
    (ShadowAt : ℕ → ℕ → ℕ → σ' → Prop) (PayloadOk : ℕ → ℕ → ℕ → π' → σ' → Prop)
    (c : Fin 4 → ℕ) (p' : π') (s' : σ') : Prop where
  counter_inv : AuthCounterInv b c
  one_le_on   : 1 ≤ c 0
  shadow_pre  : ShadowAt (c 0 - 1) ((c 0 - 1) + c 1) ((c 0 - 1) + c 2) s'
  payload_ok  : PayloadOk (c 0 - 1) (c 1) (c 2) p' s'

@[expose] def shcrShadowBase (s' : authShcrShadowStTy.denote) : authBaseShadowStTy.denote := (s'.1.1, s'.2)
@[expose] def ckShadowFixed  (s' : authCkShadowStTy.denote)   : authFixedShadowStTy.denote := (s'.1.2.2.2, s'.2)
@[expose] def mkShadowFixed  (s' : authMkShadowStTy.denote)   : authFixedShadowStTy.denote := (s'.1.2.2.2.2, s'.2)
@[expose] def hmShadowFixed  (s' : authHmShadowStTy.denote)   : authFixedShadowStTy.denote := (s'.1.2.1, s'.2)
@[expose] def cpaShadowFixed (s' : authCpaShadowStTy.denote)  : authFixedShadowStTy.denote := (s'.1.2.2, s'.2)
@[expose] def cpaPayloadRoCache (p' : (embedTy cpaPayloadTy).denote) : roListAtomicTy.denote :=
  p'.2.2.2.2.2.2.2.2.2.2.2.2.1
@[expose] def cpaPayloadRootRoCache (p' : (embedTy cpaPayloadTy).denote) : roRootListAtomicTy.denote :=
  p'.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Shadow state invariant for the `shcr` reduction extending `AuthBaseShadowAt` with KEM record bounds. -/
structure AuthShcrShadowAt (S : Setup) (b : QueryBudget)
    (nOn nRo nRoot : ℕ) (s' : authShcrShadowStTy.denote) : Prop where
  base_ok : AuthBaseShadowAt S b nOn nRo nRoot (shcrShadowBase s')
  ir_le   : s'.1.2.2.2.2.2.1.length ≤ nOn
  rr_le   : s'.1.2.2.2.2.2.2.1.length ≤ nOn

/-- Shadow state invariant for the `prfHmac` reduction extending `AuthFixedShadowAt` with multi-user list bounds. -/
structure AuthHmShadowAt (S : Setup) (b : QueryBudget)
    (nOn nRo nRoot : ℕ) (s' : authHmShadowStTy.denote) : Prop where
  fixed_ok   : AuthFixedShadowAt S b nOn nRo nRoot (hmShadowFixed s')
  mu_keys_le : s'.1.2.2.1.length ≤ nOn
  mu_chal_le : s'.1.2.2.2.1.length ≤ nOn
  mu_pend_le : s'.1.2.2.2.2.1.length ≤ nOn

/-- Pause-payload invariant for `aeadCpa` equating the saved payload RO caches with the shadow state caches. -/
structure CpaPausePayloadOk (_nOn _nRo _nRoot : ℕ)
    (p' : (embedTy cpaPayloadTy).denote) (s' : authCpaShadowStTy.denote) : Prop where
  ro_eq   : cpaPayloadRoCache p' = atomRoCache (cpaShadowFixed s').1.1.1
  root_eq : cpaPayloadRootRoCache p' = atomRootRoCache (cpaShadowFixed s').1.1.1

abbrev AuthShcrInv (S : Setup) (b : QueryBudget) := AuthCoreInv b (AuthShcrShadowAt S b)
abbrev AuthShcrPauseInv (S : Setup) (b : QueryBudget) :=
  AuthCorePauseInv b (AuthShcrShadowAt S b)
    (fun _ _ _ (_ : (embedTy pauseTy).denote) (_ : authShcrShadowStTy.denote) => True)
abbrev AuthCkInv (S : Setup) (b : QueryBudget) :=
  AuthCoreInv b (fun nOn nRo nRoot (s' : authCkShadowStTy.denote) =>
    AuthFixedShadowAt S b nOn nRo nRoot (ckShadowFixed s'))
abbrev AuthMkInv (S : Setup) (b : QueryBudget) :=
  AuthCoreInv b (fun nOn nRo nRoot (s' : authMkShadowStTy.denote) =>
    AuthFixedShadowAt S b nOn nRo nRoot (mkShadowFixed s'))
abbrev AuthHmInv (S : Setup) (b : QueryBudget) := AuthCoreInv b (AuthHmShadowAt S b)
abbrev AuthCpaInv (S : Setup) (b : QueryBudget) :=
  AuthCoreInv b (fun nOn nRo nRoot (s' : authCpaShadowStTy.denote) =>
    AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed s'))
abbrev AuthCpaPauseInv (S : Setup) (b : QueryBudget) :=
  AuthCorePauseInv b
    (fun nOn nRo nRoot (s' : authCpaShadowStTy.denote) =>
      AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed s'))
    CpaPausePayloadOk

@[expose] def dispatchAuthQEval {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {S : Setup} {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    (ρ : Env Γ) (t : AuthQuery S)
    (armInitPrin armCorrupt : Comp pqAtomicOps I (.nat :: Γ) out)
    (armGenSpk : Comp pqAtomicOps I (.prod .nat .nat :: Γ) out)
    (armGenOpk : Comp pqAtomicOps I (.prod .nat (.prod .nat .nat) :: Γ) out)
    (armSendOpk armSendNoOpk : Comp pqAtomicOps I (authSendQAtomicTy :: Γ) out)
    (armRecvOpk armRecvNoOpk : Comp pqAtomicOps I (authRecvQAtomicTy :: Γ) out)
    (armRo : Comp pqAtomicOps I (PB 192 :: Γ) out)
    (armRoRoot : Comp pqAtomicOps I (.prod (PB 32) (PB 32) :: Γ) out)
    (armRevealDh : Comp pqAtomicOps I (.unit :: Γ) out)
    (armRegister : Comp pqAtomicOps I (PB 32 :: Γ) out) :
    OracleComp T out.denote :=
  match (authCodec S).qenc t with
  | .inl u => armInitPrin.eval (.cons u ρ)
  | .inr (.inl u) => armCorrupt.eval (.cons u ρ)
  | .inr (.inr (.inl x)) => armGenSpk.eval (.cons x ρ)
  | .inr (.inr (.inr (.inl x))) => armGenOpk.eval (.cons x ρ)
  | .inr (.inr (.inr (.inr (.inl x)))) => armSendOpk.eval (.cons x ρ)
  | .inr (.inr (.inr (.inr (.inr (.inl x))))) => armSendNoOpk.eval (.cons x ρ)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl x)))))) => armRecvOpk.eval (.cons x ρ)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl x))))))) => armRecvNoOpk.eval (.cons x ρ)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec)))))))) => armRo.eval (.cons sec ρ)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl x))))))))) => armRoRoot.eval (.cons x ρ)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl u)))))))))) => armRevealDh.eval (.cons u ρ)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr sk)))))))))) => armRegister.eval (.cons sk ρ)

theorem dispatchAuthQ_eval_qenc {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {S : Setup} {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ authQueryAtomicTy) (ρ : Env Γ) (t : AuthQuery S)
    (hQ : qE.eval ρ = (authCodec S).qenc t)
    (armInitPrin armCorrupt : Comp pqAtomicOps I (.nat :: Γ) out)
    (armGenSpk : Comp pqAtomicOps I (.prod .nat .nat :: Γ) out)
    (armGenOpk : Comp pqAtomicOps I (.prod .nat (.prod .nat .nat) :: Γ) out)
    (armSendOpk armSendNoOpk : Comp pqAtomicOps I (authSendQAtomicTy :: Γ) out)
    (armRecvOpk armRecvNoOpk : Comp pqAtomicOps I (authRecvQAtomicTy :: Γ) out)
    (armRo : Comp pqAtomicOps I (PB 192 :: Γ) out)
    (armRoRoot : Comp pqAtomicOps I (.prod (PB 32) (PB 32) :: Γ) out)
    (armRevealDh : Comp pqAtomicOps I (.unit :: Γ) out)
    (armRegister : Comp pqAtomicOps I (PB 32 :: Γ) out) :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk
      armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk
      armRo armRoRoot armRevealDh armRegister).eval ρ =
    dispatchAuthQEval ρ t armInitPrin armCorrupt armGenSpk armGenOpk
      armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk
      armRo armRoRoot armRevealDh armRegister := by
  dsimp only [dispatchAuthQ, dispatchAuthQEval, Comp.eval]
  rw [hQ]
  cases t
  · rfl
  all_goals
    dsimp only [authCodec, Comp.eval, Expr.eval, Env.get, Expr.v0]
    exact Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval _ _ _ _
      (fun v => by cases v <;> rfl)

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
