/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PqxdhSimTypes -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.E2EStateRepr -- proof-setup: allow-public-import

/-!
# Per-Instance Epoch and Clamped Driver Invariants

Proves `SmEpochBounded` preservation across `oracleImplRSessionTracked`, promoted-session `sid`
distinctness (`DrvInstsSubsetSends`), and the per-instance driver invariant `HaltedKindSimInvInst`.
-/

public section

set_option autoImplicit false

open scoped BigOperators

namespace Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst

open OracleSpec OracleComp
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (ConfigR GameState RecvResult challImpl challR corrR deliverR injectR
  oracleImplR transmitImpl transmitR)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHModelInst BHE2EDrvState Bytes SampledSessionKey
  bhBaseMirror bhE2EFinishStartSpk bhE2EGuard bhE2EMirror configRefuseEarlyBobCorr
  paramsIdsWithSpqr sessionSchemeFixedSpk)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  bhE2ELocalStartSessionTracked bhE2EStepLocalSmSessionTracked oracleImplRSessionTracked)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp (SmEpochBounded
  smEpochBounded_corrR smEpochBounded_deliverR smEpochBounded_epMgmt_record
  smEpochBounded_initState_fixedSpk smEpochBounded_injectR)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded smReachBounded_oracleImplR)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (ValidSimTrackInv
  oracleImplRSessionTracked_step_support)

theorem isQueryBoundP_min {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) (P : ι → Prop) [DecidablePred P] {m n : ℕ}
    (hm : oa.IsQueryBoundP P m) (hn : oa.IsQueryBoundP P n) :
    oa.IsQueryBoundP P (min m n) := by
  rcases Nat.le_total m n with h | h
  · rwa [Nat.min_eq_left h]
  · rwa [Nat.min_eq_right h]

private theorem liftM_prob_state_run {σ α : Type} (m : ProbComp α) (s : σ) :
    (liftM m : StateT σ ProbComp α).run s = m >>= fun a => pure (a, s) := by
  show StateT.run (StateT.lift m) s = m >>= fun a => pure (a, s)
  rw [StateT.run_lift]

theorem smEpochBounded_oracleImplR {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (idA idB : CryptoGames.LibsignalSession.IdentityKey) (spkCoins : BitVec 256)
    (qep : ℕ) {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {k : ℕ} {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hEp : SmEpochBounded k gs)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range q ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support
      ((CryptoGames.SM.oracleImplR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          (2 + 1) qep (configRefuseEarlyBobCorr decT encT) q).run gs)) :
    SmEpochBounded (k + 1) out.2 := by
  let P_sm := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes := configRefuseEarlyBobCorr decT encT
  rcases q with (((⟨P_q, m, optR⟩ | ⟨P_q, m₀, m₁, optR⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P_q
  · change out ∈ support ((transmitR (sessionSchemeFixedSpk P_sm ℓ spkCoins) (2 + 1) qep cfg
      (P_q, m, optR)).run gs) at hout
    unfold transmitR transmitImpl at hout
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases hSend : !(cfg.sendOK gs P_q)
    · simp only [hSend, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact hEp.mono (Nat.le_succ k)
    · simp only [hSend, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hout
      by_cases hWin : gs.win
      · simp only [hWin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact hEp.mono (Nat.le_succ k)
      · simp only [hWin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftM_prob_state_run,
          bind_assoc, pure_bind, mem_support_bind_iff] at hout
        rcases hout with ⟨⟨coins, bad⟩, -, hout⟩
        cases hep : gs.epMgmt (2 + 1) qep P_q bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact hEp.mono (Nat.le_succ k)
        | some gs₁ =>
          simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact smEpochBounded_epMgmt_record P_sm ℓ spkCoins m coins hEp hep
  · change out ∈ support ((challR (sessionSchemeFixedSpk P_sm ℓ spkCoins) (2 + 1) qep cfg
      (P_q, m₀, m₁, optR)).run gs) at hout
    unfold challR challImpl at hout
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases hSend : !(cfg.sendOK gs P_q)
    · simp only [hSend, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact hEp.mono (Nat.le_succ k)
    · simp only [hSend, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hout
      by_cases hWin : gs.win
      · simp only [hWin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact hEp.mono (Nat.le_succ k)
      · simp only [hWin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftM_prob_state_run,
          bind_assoc, pure_bind, mem_support_bind_iff] at hout
        rcases hout with ⟨⟨coins, bad⟩, -, hout⟩
        cases hep : gs.epMgmt (2 + 1) qep P_q bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact hEp.mono (Nat.le_succ k)
        | some gs₁ =>
          simp only [hep] at hout
          by_cases hSafe : !(gs₁.safeCh (2 + 1) P_q) || !(cfg.base.challAllowedIn (gs₁.epoch P_q))
          · simp only [hSafe, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact hEp.mono (Nat.le_succ k)
          · simp only [hSafe, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
            subst hout
            exact smEpochBounded_epMgmt_record P_sm ℓ spkCoins _ coins hEp hep
  · exact smEpochBounded_deliverR P_sm ℓ k spkCoins cfg (Q, w) hEp hout
  · exact smEpochBounded_injectR P_sm ℓ (2 + 1) qep k spkCoins cfg (Q, w) hEp hout
  · exact smEpochBounded_corrR ℓ k cfg P_q hEp hout

theorem oracleImplRSessionTracked_step_support_full
    {τ : Type} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (qep q : ℕ) {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qry : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes} {tr₀ : τ}
    (hReach : SmReachBounded C K q gs)
    (hEp : SmEpochBounded q gs)
    (hTr : TrackInv q tr₀)
    {out : ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range qry ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes) × τ}
    (hout : out ∈ support
      (((oracleImplRSessionTracked T
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          (2 + 1) qep (configRefuseEarlyBobCorr decT encT) qry).run gs).run tr₀)) :
    TrackInv (q + 1) out.2 ∧
      SmReachBounded C K (q + 1) out.1.2 ∧
      SmEpochBounded (q + 1) out.1.2 := by
  obtain ⟨hTr', hEqOr⟩ := oracleImplRSessionTracked_step_support hT _ (2 + 1) qep q
    (configRefuseEarlyBobCorr decT encT) qry hTr hout
  rcases hEqOr with hEq | hSupp
  · rw [hEq]
    exact ⟨hTr', hReach.mono (Nat.le_succ q), hEp.mono (Nat.le_succ q)⟩
  · exact ⟨hTr',
      smReachBounded_oracleImplR C K idA idB ℓ (2 + 1) qep q spkCoins
        (configRefuseEarlyBobCorr decT encT) qry hReach hSupp,
      smEpochBounded_oracleImplR C K idA idB spkCoins qep decT encT hEp qry hSupp⟩

/-- Invariant that promoted sessions in `σ.insts` have distinct `sid`s drawn from `σ.sends`. -/
structure DrvInstsSubsetSends {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) : Prop where
  insts_nodup : (σ.insts.map (·.sid)).Nodup
  insts_sub : ∀ s ∈ σ.insts.map (·.sid), s ∈ σ.sends.map Prod.fst

theorem DrvInstsSubsetSends.insts_length_le_sends {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {σ : BHE2EDrvState S ℓ} (h : DrvInstsSubsetSends σ) :
    σ.insts.length ≤ σ.sends.length := by
  have hle := h.insts_nodup.length_le_of_subset h.insts_sub
  simpa only [List.length_map] using hle

theorem DrvInstsSubsetSends.empty {S : SignalPqxdh.Setup} {ℓ : ℕ} (secb : Bool) :
    DrvInstsSubsetSends ({ b := secb } : BHE2EDrvState S ℓ) where
  insts_nodup := List.nodup_nil
  insts_sub := by intro _ h; nomatch h

theorem DrvInstsSubsetSends.mirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {σ : BHE2EDrvState S ℓ} (h : DrvInstsSubsetSends σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    DrvInstsSubsetSends (bhE2EMirror σ kq kr) := by
  refine ⟨by cases kq <;> cases kr <;> exact h.insts_nodup, fun s hs => ?_⟩
  cases kq <;> cases kr <;>
    simp only [bhE2EMirror, bhBaseMirror, List.map_cons, List.mem_cons] at hs ⊢
  all_goals
    first
    | exact h.insts_sub s hs
    | exact Or.inr (h.insts_sub s hs)

theorem DrvInstsSubsetSends.finishStartSpk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (bm? : Option Bool) {σ : BHE2EDrvState S ℓ}
    (h : DrvInstsSubsetSends σ) (sid : SignalPqxdh.SessionId S)
    (rTest rSpk : SignalPqxdh.KeyIndResponse) (spkCoins : BitVec 256) :
    DrvInstsSubsetSends (bhE2EFinishStartSpk C K bm? σ sid rTest rSpk spkCoins).2 := by
  unfold bhE2EFinishStartSpk
  cases hg : bhE2EGuard σ sid with
  | none => exact h
  | some val =>
    rcases val with ⟨hdr, bnd, uj⟩
    dsimp only
    cases rTest <;> cases rSpk <;> dsimp only
    all_goals
      try exact h
    rename_i drKey spkSk
    split_ifs with hmatch
    · dsimp only
      unfold bhE2EGuard at hg
      by_cases hany : σ.insts.any (fun d => d.sid == sid) = true
      · simp [hany] at hg
      · simp only [hany, Bool.false_eq_true, ↓reduceIte] at hg
        cases hfind : σ.sends.find? (fun (s, _, _) => s == sid) with
        | none => simp [hfind] at hg
        | some sendEntry =>
          have hnotmem : sid ∉ σ.insts.map (·.sid) := by
            intro hmem
            rw [List.mem_map] at hmem
            rcases hmem with ⟨d, hd, rfl⟩
            exact hany (List.any_eq_true.mpr ⟨d, hd, beq_self_eq_true _⟩)
          have hinSends : sid ∈ σ.sends.map Prod.fst := by
            have hf := List.mem_of_find?_eq_some hfind
            have hbeq := List.find?_some hfind
            have heq : sendEntry.1 = sid := of_decide_eq_true hbeq
            rw [← heq]
            exact List.mem_map_of_mem (f := Prod.fst) hf
          refine ⟨?_, fun s hs => ?_⟩
          · rw [List.map_append, List.map_singleton, List.nodup_append]
            exact ⟨h.insts_nodup, List.nodup_singleton _, fun x hx y hy hxy => by
              rw [List.mem_singleton] at hy; subst hy; subst hxy; exact hnotmem hx⟩
          · rw [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hs
            rcases hs with hs | rfl
            · exact h.insts_sub s hs
            · exact hinSends
    · exact h

private theorem map_sid_set_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    ∀ (insts : List (BHModelInst S ℓ)) (i : ℕ) (d d' : BHModelInst S ℓ),
      insts[i]? = some d → d'.sid = d.sid →
      (insts.set i d').map (·.sid) = insts.map (·.sid)
  | [], _, _, _, h, _ => by simp at h
  | _ :: _, 0, _, _, h, hsid => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [hsid]
  | _ :: as, i + 1, d, d', h, hsid => by
    simp only [List.getElem?_cons_succ] at h
    simp [map_sid_set_eq as i d d' h hsid]

theorem DrvInstsSubsetSends.of_sids_sends_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {σ σ' : BHE2EDrvState S ℓ} (h : DrvInstsSubsetSends σ)
    (hInsts : σ'.insts.map (·.sid) = σ.insts.map (·.sid))
    (hSends : σ'.sends = σ.sends) :
    DrvInstsSubsetSends σ' where
  insts_nodup := hInsts ▸ h.insts_nodup
  insts_sub := by rw [hInsts, hSends]; exact h.insts_sub

theorem DrvInstsSubsetSends.setInstSameSid {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {σ σ' : BHE2EDrvState S ℓ} (h : DrvInstsSubsetSends σ)
    {i : ℕ} {d d' : BHModelInst S ℓ}
    (hi : σ.insts[i]? = some d) (hsid : d'.sid = d.sid)
    (hInsts : σ'.insts = σ.insts.set i d') (hSends : σ'.sends = σ.sends) :
    DrvInstsSubsetSends σ' :=
  h.of_sids_sends_eq (hInsts ▸ map_sid_set_eq σ.insts i d d' hi hsid) hSends

/-- Per-instance refinement of `HaltedSimInv` tracking per-slot session query counts and `DrvInstsSubsetSends`. -/
structure HaltedKindSimInvInst {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (TrackInv : ℕ → τ → Prop)
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart : ℕ) (qs : ℕ → ℕ)
    (qKiDone qSendDone qStartDone : ℕ) (qSessDone : ℕ → ℕ)
    (σH : BHE2EDrvState S ℓ × List τ) : Prop where
  ki_le : qKiDone ≤ b.q_total
  send_le : qSendDone ≤ S.N_send_tot
  start_le : qStartDone ≤ min qStart S.N_send_tot
  sess_le : ∀ j < qStart, qSessDone j ≤ qs j
  sends_le_ki : σH.1.sends.length ≤ qKiDone
  sends_le_send : σH.1.sends.length ≤ qSendDone
  insts_le_start : σH.1.insts.length ≤ qStartDone
  subsetSends : DrvInstsSubsetSends σH.1
  mirror : Computational.Proofs.E2E.Dsl.M3Interfaces.DrvQueryBounded qKiDone qStartDone σH.1
  metaAligned : Computational.Proofs.E2E.Dsl.M3Interfaces.DrvMetaAligned σH.1
  kiReach : Computational.Proofs.E2E.Dsl.M3Interfaces.KeyIndReachBounded S qKiDone σH.1.st
  tracks_len : σH.2.length = σH.1.insts.length
  slot_reach : ∀ idx (d : BHModelInst S ℓ),
    σH.1.insts[idx]? = some d →
    ∀ gs ∈ d.gs, SmReachBounded C K (qSessDone idx) gs ∧ SmEpochBounded (qSessDone idx) gs
  slot_track : ∀ idx (tr : τ),
    σH.2[idx]? = some tr → TrackInv (qSessDone idx) tr

theorem HaltedKindSimInvInst.sends_length_le {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    σH.1.sends.length ≤ min b.q_total S.N_send_tot := by
  have h1 := h.sends_le_ki
  have h2 := h.ki_le
  have h3 := h.sends_le_send
  have h4 := h.send_le
  omega

theorem HaltedKindSimInvInst.insts_length_le {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    σH.1.insts.length ≤ min qStart (min b.q_total S.N_send_tot) := by
  have hsub := h.subsetSends.insts_length_le_sends
  have hsends := h.sends_length_le
  have hinst := h.insts_le_start
  have hst := h.start_le
  omega

theorem HaltedKindSimInvInst.qSessDone_le_sup {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    {idx : ℕ} (hidx : idx < σH.1.insts.length) :
    qSessDone idx ≤ Finset.sup (Finset.range qStart) qs := by
  have hlt : idx < qStart := by
    have h1 := h.insts_le_start
    have h2 := h.start_le
    omega
  exact le_trans (h.sess_le idx hlt) (Finset.le_sup (f := qs) (Finset.mem_range.mpr hlt))

theorem HaltedKindSimInvInst.epoch_bounded {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    ∀ d ∈ σH.1.insts, ∀ gs ∈ d.gs,
      SmEpochBounded (Finset.sup (Finset.range qStart) qs) gs := by
  intro d hd gs hgs
  obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hd
  have hsome : σH.1.insts[idx]? = some σH.1.insts[idx] := List.getElem?_eq_getElem hidx
  exact (h.slot_reach idx _ hsome gs hgs).2.mono (h.qSessDone_le_sup hidx)

theorem HaltedKindSimInvInst.toHaltedSimInv {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedSimInv TrackInv C K b
      qStart (Finset.sup (Finset.range qStart) qs)
      qKiDone qStartDone (Finset.sup (Finset.range qStart) qs) σH where
  ki_le := h.ki_le
  start_le := le_trans h.start_le (Nat.min_le_left _ _)
  dr_le := le_rfl
  mirror := h.mirror
  metaAligned := h.metaAligned
  sessions := fun d hd gs hgs => by
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hd
    have hsome : σH.1.insts[idx]? = some σH.1.insts[idx] := List.getElem?_eq_getElem hidx
    exact (h.slot_reach idx _ hsome gs hgs).1.mono (h.qSessDone_le_sup hidx)
  kiReach := h.kiReach
  tracks_len := h.tracks_len
  tracks_inv := fun tr htr => by
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem htr
    have hsome : σH.2[idx]? = some σH.2[idx] := List.getElem?_eq_getElem hidx
    have hidx' : idx < σH.1.insts.length := h.tracks_len ▸ hidx
    exact hT.mono (h.qSessDone_le_sup hidx') (h.slot_track idx _ hsome)

theorem HaltedKindSimInvInst.instMeta_length_le {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    σH.1.instMeta.length ≤ min qStart (min b.q_total S.N_send_tot) := by
  have hm : σH.1.instMeta.length = σH.1.insts.length := h.metaAligned
  exact hm ▸ h.insts_length_le

theorem HaltedKindSimInvInst.tracks_length_le {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    σH.2.length ≤ min qStart (min b.q_total S.N_send_tot) :=
  h.tracks_len ▸ h.insts_length_le

theorem HaltedKindSimInvInst.empty {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (TrackInv : ℕ → τ → Prop)
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart : ℕ) (qs : ℕ → ℕ) (secb : Bool) :
    HaltedKindSimInvInst (S := S) (ℓ := ℓ) TrackInv C K b qStart qs 0 0 0 (fun _ => 0)
      (({ b := secb } : BHE2EDrvState S ℓ), ([] : List τ)) where
  ki_le := Nat.zero_le _
  send_le := Nat.zero_le _
  start_le := Nat.zero_le _
  sess_le := fun _ _ => Nat.zero_le _
  sends_le_ki := Nat.zero_le _
  sends_le_send := Nat.zero_le _
  insts_le_start := Nat.zero_le _
  subsetSends := DrvInstsSubsetSends.empty secb
  mirror := Computational.Proofs.E2E.Dsl.M3Interfaces.DrvMirrorBounded.empty 0 0 0 0 0 0 secb
  metaAligned := Computational.Proofs.E2E.Dsl.M3Interfaces.drvMetaAligned_empty secb
  kiReach := Computational.Proofs.E2E.Dsl.M3Interfaces.KeyIndReachBounded.empty S 0 false
  tracks_len := rfl
  slot_reach := by intro _ _ hd; simp at hd
  slot_track := by intro _ _ htr; simp at htr

theorem HaltedKindSimInvInst.setBit {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (flip : Bool) :
    HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone
      ({ σH.1 with b := flip }, σH.2) where
  ki_le := h.ki_le
  send_le := h.send_le
  start_le := h.start_le
  sess_le := h.sess_le
  sends_le_ki := h.sends_le_ki
  sends_le_send := h.sends_le_send
  insts_le_start := h.insts_le_start
  subsetSends := h.subsetSends.of_sids_sends_eq rfl rfl
  mirror := ⟨h.mirror.prins_le, h.mirror.bundles_le, h.mirror.opks_le,
    h.mirror.sends_le, h.mirror.corrPrins_le, h.mirror.insts_le,
    h.mirror.instMeta_le, h.mirror.revSpks_le⟩
  metaAligned := h.metaAligned
  kiReach := h.kiReach
  tracks_len := h.tracks_len
  slot_reach := h.slot_reach
  slot_track := h.slot_track

@[expose] def isSendKiQuery {S : SignalPqxdh.Setup} (kq : SignalPqxdh.KeyIndQuery S) : Bool :=
  kq matches .initiateOPK .. || kq matches .initiateNoOPK ..

@[expose] def nextSendDone {S : SignalPqxdh.Setup} (qSendDone : ℕ)
    (kq : SignalPqxdh.KeyIndQuery S) : ℕ :=
  if isSendKiQuery kq then qSendDone + 1 else qSendDone

@[expose] def nextSessDone (qStart : ℕ) (qSessDone : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  fun j => if i < qStart ∧ j = i then qSessDone i + 1 else qSessDone j

theorem HaltedKindSimInvInst.kiSkip_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (kq : SignalPqxdh.KeyIndQuery S)
    (hKiNext : qKiDone + 1 ≤ b.q_total)
    (hSendNext : nextSendDone qSendDone kq ≤ S.N_send_tot) :
    HaltedKindSimInvInst TrackInv C K b qStart qs
      (qKiDone + 1) (nextSendDone qSendDone kq) qStartDone qSessDone σH where
  ki_le := hKiNext
  send_le := hSendNext
  start_le := h.start_le
  sess_le := h.sess_le
  sends_le_ki := le_trans h.sends_le_ki (Nat.le_succ _)
  sends_le_send := by
    dsimp only [nextSendDone]
    split_ifs <;> have := h.sends_le_send <;> omega
  insts_le_start := h.insts_le_start
  subsetSends := h.subsetSends
  mirror := h.mirror.mono (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)
    (Nat.le_succ _) (Nat.le_succ _) (le_refl _)
  metaAligned := h.metaAligned
  kiReach := h.kiReach.mono (Nat.le_succ _)
  tracks_len := h.tracks_len
  slot_reach := h.slot_reach
  slot_track := h.slot_track

theorem HaltedKindSimInvInst.kiMirror_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget}
    {qStart : ℕ} {qs : ℕ → ℕ} {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σ : BHE2EDrvState S ℓ} {tracks : List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone
      (σ, tracks))
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse)
    (st' : SignalPqxdh.KeyIndState S)
    (hKiNext : qKiDone + 1 ≤ b.q_total)
    (hSendNext : nextSendDone qSendDone kq ≤ S.N_send_tot)
    (hKi' : Computational.Proofs.E2E.Dsl.M3Interfaces.KeyIndReachBounded S (qKiDone + 1) st') :
    HaltedKindSimInvInst TrackInv C K b qStart qs
      (qKiDone + 1) (nextSendDone qSendDone kq) qStartDone qSessDone
      (bhE2EMirror { σ with st := st' } kq kr, tracks) ∧
    (∀ k, Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k (σ, tracks) →
      Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k
        (bhE2EMirror { σ with st := st' } kq kr, tracks)) := by
  have hMirSt : Computational.Proofs.E2E.Dsl.M3Interfaces.DrvQueryBounded qKiDone qStartDone
      { σ with st := st' } :=
    ⟨h.mirror.prins_le, h.mirror.bundles_le, h.mirror.opks_le,
     h.mirror.sends_le, h.mirror.corrPrins_le, h.mirror.insts_le,
     h.mirror.instMeta_le, h.mirror.revSpks_le⟩
  have hMir' := Computational.Proofs.E2E.Dsl.M3Interfaces.DrvMirrorBounded.mirror hMirSt kq kr
  have hInstsEq : (bhE2EMirror { σ with st := st' } kq kr).insts = σ.insts := by
    cases kq <;> cases kr <;> rfl
  have hStEq : (bhE2EMirror { σ with st := st' } kq kr).st = st' := by
    cases kq <;> cases kr <;> rfl
  refine ⟨{
    ki_le := hKiNext
    send_le := hSendNext
    start_le := h.start_le
    sess_le := h.sess_le
    sends_le_ki := by
      have hs : σ.sends.length ≤ qKiDone := h.sends_le_ki
      cases kq <;> cases kr <;>
        simp only [bhE2EMirror, bhBaseMirror, List.length_cons] <;> omega
    sends_le_send := by
      have hs : σ.sends.length ≤ qSendDone := h.sends_le_send
      cases kq <;> cases kr <;>
        simp only [bhE2EMirror, bhBaseMirror, nextSendDone, isSendKiQuery,
          Bool.or_self, Bool.or_true, Bool.true_or, ↓reduceIte, Bool.false_eq_true,
          List.length_cons] <;> omega
    insts_le_start := by dsimp only; rw [hInstsEq]; exact h.insts_le_start
    subsetSends := (h.subsetSends.of_sids_sends_eq (σ' := { σ with st := st' }) rfl rfl).mirror kq kr
    mirror := hMir'
    metaAligned := Computational.Proofs.E2E.Dsl.M3Interfaces.drvMetaAligned_mirror
      h.metaAligned kq kr
    kiReach := hStEq ▸ hKi'
    tracks_len := by dsimp only; rw [hInstsEq]; exact h.tracks_len
    slot_reach := fun idx d hd => by
      dsimp only at hd; rw [hInstsEq] at hd; exact h.slot_reach idx d hd
    slot_track := h.slot_track
  }, fun k ⟨hkLt, hkNone⟩ => ⟨by dsimp only; rw [hInstsEq]; exact hkLt, fun d hd => by
      dsimp only at hd; rw [hInstsEq] at hd; exact hkNone d hd⟩⟩

theorem HaltedKindSimInvInst.finishStartSpkTracked_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σ₀ : BHE2EDrvState S ℓ} {tracks : List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone
      (σ₀, tracks))
    (hStartNext : qStartDone + 1 ≤ min qStart S.N_send_tot)
    (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    let fin := Computational.Proofs.E2E.Dsl.KindRedHalted.bhE2EFinishStartSpkTracked
      T.init C K bMode? (σ₀, tracks) sid kr1 kr2 ac
    HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone (qStartDone + 1) qSessDone
      fin.2 ∧
    (∀ k, Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k (σ₀, tracks) →
      Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k fin.2) := by
  dsimp only [Computational.Proofs.E2E.Dsl.KindRedHalted.bhE2EFinishStartSpkTracked]
  have hRest :
      (let p := CryptoVerification.E2E.bhE2EFinishStartSpk C K bMode? σ₀ sid kr1 kr2 ac
       let tracks' := match p.1, kr1 with
         | some _, .drKeyResp dk => tracks ++ [T.init (CryptoVerification.E2E.bhKeySOf dk ac)]
         | _, _ => tracks
       p.2.sends = σ₀.sends ∧
       p.2.insts.length ≤ qStartDone + 1 ∧
       p.2.st = σ₀.st ∧
       tracks'.length = p.2.insts.length ∧
       (∀ idx (d : BHModelInst S ℓ), p.2.insts[idx]? = some d →
         ∀ gs ∈ d.gs, SmReachBounded C K (qSessDone idx) gs ∧ SmEpochBounded (qSessDone idx) gs) ∧
       (∀ idx (tr : τ), tracks'[idx]? = some tr → TrackInv (qSessDone idx) tr) ∧
       (∀ k, Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k (σ₀, tracks) →
         Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k (p.2, tracks'))) := by
    have hInstLe : σ₀.insts.length ≤ qStartDone := h.insts_le_start
    unfold CryptoVerification.E2E.bhE2EFinishStartSpk
    rcases hg : CryptoVerification.E2E.bhE2EGuard σ₀ sid with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
    · exact ⟨rfl, Nat.le_succ_of_le hInstLe, rfl, h.tracks_len, h.slot_reach, h.slot_track, fun _ hk => hk⟩
    · cases kr1 with
      | drKeyResp dk =>
        cases kr2 with
        | spkSkResp spkSk =>
          simp only
          split_ifs with hlen
          · refine ⟨rfl, by dsimp only; simp; omega, rfl, by dsimp only; simp [h.tracks_len], ?_, ?_, ?_⟩
            · intro idx d hd gs hgs
              dsimp only at hd
              rcases lt_trichotomy idx σ₀.insts.length with hlt | rfl | hgt
              · rw [List.getElem?_append_left hlt] at hd
                exact h.slot_reach idx d hd gs hgs
              · rw [List.getElem?_append_right (le_refl _), Nat.sub_self,
                    List.getElem?_cons_zero, Option.some.injEq] at hd
                subst hd
                dsimp only at hgs
                cases bMode? with
                | none => simp at hgs
                | some bm =>
                  simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hgs
                  subst hgs
                  exact ⟨(Computational.Proofs.E2E.Dsl.SmReachInv.smReachBounded_initState
                      C K _ _ ℓ _ _ bm).mono (Nat.zero_le _),
                    (smEpochBounded_initState_fixedSpk _ ℓ _ _ bm).mono (Nat.zero_le _)⟩
              · rw [List.getElem?_eq_none (by simp; omega)] at hd
                simp at hd
            · intro idx tr htr
              rcases lt_trichotomy idx tracks.length with hlt | rfl | hgt
              · rw [List.getElem?_append_left hlt] at htr
                exact h.slot_track idx tr htr
              · rw [List.getElem?_append_right (le_refl _), Nat.sub_self,
                    List.getElem?_cons_zero, Option.some.injEq] at htr
                subst htr
                exact hT.init (qSessDone tracks.length) _
              · rw [List.getElem?_eq_none (by simp; omega)] at htr
                simp at htr
            · intro k ⟨hkLt, hkNone⟩
              have hkLt' : k < σ₀.insts.length := hkLt
              refine ⟨by dsimp only; simp; omega, fun d hd => ?_⟩
              dsimp only at hd
              rw [List.getElem?_append_left hkLt'] at hd
              exact hkNone d hd
          · exact ⟨rfl, Nat.le_succ_of_le hInstLe, rfl, h.tracks_len, h.slot_reach, h.slot_track, fun _ hk => hk⟩
        | _ => exact ⟨rfl, Nat.le_succ_of_le hInstLe, rfl, h.tracks_len, h.slot_reach, h.slot_track, fun _ hk => hk⟩
      | _ => exact ⟨rfl, Nat.le_succ_of_le hInstLe, rfl, h.tracks_len, h.slot_reach, h.slot_track, fun _ hk => hk⟩
  have hMir := Computational.Proofs.E2E.Dsl.M3Interfaces.DrvMirrorBounded.finishStartSpk
    C K bMode? h.mirror sid kr1 kr2 ac
  have hMeta := Computational.Proofs.E2E.Dsl.M3Interfaces.drvMetaAligned_finishStartSpk
    C K bMode? h.metaAligned sid kr1 kr2 ac
  have hSub := h.subsetSends.finishStartSpk C K bMode? sid kr1 kr2 ac
  rcases hRest with ⟨hSendsEq, hInstsLe, hStEq, hTrLen, hSlotR, hSlotT, hPaused⟩
  exact ⟨{
    ki_le := h.ki_le
    send_le := h.send_le
    start_le := hStartNext
    sess_le := h.sess_le
    sends_le_ki := by dsimp only; rw [hSendsEq]; exact h.sends_le_ki
    sends_le_send := by dsimp only; rw [hSendsEq]; exact h.sends_le_send
    insts_le_start := hInstsLe
    subsetSends := hSub
    mirror := hMir
    metaAligned := hMeta
    kiReach := by dsimp only; rw [hStEq]; exact h.kiReach
    tracks_len := hTrLen
    slot_reach := hSlotR
    slot_track := hSlotT
  }, hPaused⟩

theorem HaltedKindSimInvInst.stepLocalSmSessionTracked_preserves
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (i : ℕ) (hSessNext : i < qStart → qSessDone i + 1 ≤ qs i)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : CryptoVerification.E2E.BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hout : out ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    HaltedKindSimInvInst TrackInv C K b qStart qs
      qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone i) out.2 ∧
    (∀ k, Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k σH →
      Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k out.2) := by
  rcases σH with ⟨σ, tracks⟩
  have hSessLe : ∀ j < qStart, nextSessDone qStart qSessDone i j ≤ qs j := by
    intro j hj
    dsimp only [nextSessDone]
    split_ifs with hij
    · rcases hij with ⟨hi, rfl⟩; exact hSessNext hi
    · exact h.sess_le j hj
  have hSessMono : ∀ idx, qSessDone idx ≤ nextSessDone qStart qSessDone i idx := by
    intro idx
    dsimp only [nextSessDone]
    split_ifs with hcond
    · rcases hcond with ⟨_, rfl⟩; omega
    · exact le_rfl
  have hpure : out ∈ support (pure ((none, none, none), (σ, tracks)) :
      ProbComp (CryptoVerification.E2E.BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ))) →
      HaltedKindSimInvInst TrackInv C K b qStart qs
        qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone i) out.2 ∧
      (∀ k, Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k (σ, tracks) →
        Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k out.2) := by
    simp only [support_pure, Set.mem_singleton_iff]
    rintro rfl
    exact ⟨{
      ki_le := h.ki_le
      send_le := h.send_le
      start_le := h.start_le
      sess_le := hSessLe
      sends_le_ki := h.sends_le_ki
      sends_le_send := h.sends_le_send
      insts_le_start := h.insts_le_start
      subsetSends := h.subsetSends
      mirror := h.mirror
      metaAligned := h.metaAligned
      kiReach := h.kiReach
      tracks_len := h.tracks_len
      slot_reach := fun idx d hd gs hgs => by
        obtain ⟨hr, he⟩ := h.slot_reach idx d hd gs hgs
        exact ⟨hr.mono (hSessMono idx), he.mono (hSessMono idx)⟩
      slot_track := fun idx tr htr =>
        hT.mono (hSessMono idx) (h.slot_track idx tr htr)
    }, fun _ hk => hk⟩
  unfold bhE2EStepLocalSmSessionTracked at hout
  dsimp only at hout
  by_cases hcl : !CryptoVerification.E2E.bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte] at hout; exact hpure hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => simp only [hd] at hout; exact hpure hout
    | some d =>
      have hiLen : i < σ.insts.length := (List.getElem?_eq_some_iff.mp hd).1
      have hiLt : i < qStart := by
        have h1 : σ.insts.length ≤ qStartDone := h.insts_le_start
        have h2 := h.start_le
        omega
      cases him : σ.instMeta[i]? with
      | none => simp only [hd, him] at hout; exact hpure hout
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted && CryptoVerification.E2E.bhIsBobRecvSMQuery sq &&
            CryptoVerification.E2E.bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact ⟨{
            ki_le := h.ki_le
            send_le := h.send_le
            start_le := h.start_le
            sess_le := hSessLe
            sends_le_ki := h.sends_le_ki
            sends_le_send := h.sends_le_send
            insts_le_start := h.insts_le_start
            subsetSends := h.subsetSends.of_sids_sends_eq rfl rfl
            mirror := ⟨h.mirror.prins_le, h.mirror.bundles_le, h.mirror.opks_le,
              h.mirror.sends_le, h.mirror.corrPrins_le, h.mirror.insts_le,
              by simp [h.mirror.instMeta_le], h.mirror.revSpks_le⟩
            metaAligned := by
              have hm := h.metaAligned
              simp [Computational.Proofs.E2E.Dsl.M3Interfaces.DrvMetaAligned] at hm ⊢; exact hm
            kiReach := h.kiReach
            tracks_len := h.tracks_len
            slot_reach := fun idx d0 hd0 gs hgs => by
              obtain ⟨hr, he⟩ := h.slot_reach idx d0 hd0 gs hgs
              exact ⟨hr.mono (hSessMono idx), he.mono (hSessMono idx)⟩
            slot_track := fun idx tr htr =>
              hT.mono (hSessMono idx) (h.slot_track idx tr htr)
          }, fun _ hk => hk⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none => simp only [hgs] at hout; exact hpure hout
          | some gs =>
            simp only [hgs] at hout
            obtain ⟨hgsReach, hgsEp⟩ := h.slot_reach i d hd gs hgs
            have hiTrLen : i < tracks.length := h.tracks_len.symm ▸ hiLen
            have hti : tracks[i]? = some tracks[i] := List.getElem?_eq_getElem hiTrLen
            have hTr0 : TrackInv (qSessDone i) ((tracks[i]?).getD (T.init default)) := by
              rw [hti, Option.getD_some]
              exact h.slot_track i tracks[i] hti
            have hrunTr :
                ∀ (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ)
                    (BitVec 512) Bytes).Domain),
                out ∈ support (do
                  let tr₀ := (tracks[i]?).getD (T.init default)
                  let ((r, gs'), tr') ←
                    ((oracleImplRSessionTracked T
                      (sessionSchemeFixedSpk
                        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                        ℓ d.spkCoins) (2 + 1) qep
                      (configRefuseEarlyBobCorr decT encT) q').run gs).run tr₀
                  let accepted := CryptoVerification.E2E.bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true,
                                ikACorrAtAccept := CryptoVerification.E2E.bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  pure (CryptoVerification.E2E.bhPackSmResp q' r, (σ1, tracks.set i tr'))) →
                HaltedKindSimInvInst TrackInv C K b qStart qs
                  qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone i) out.2 ∧
                (∀ k, Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k
                    (σ, tracks) →
                  Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k out.2) := by
              intro q' hrun
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrun
              rcases hrun with ⟨⟨⟨r, gs'⟩, tr'⟩, hstep, rfl⟩
              obtain ⟨hTr', hReach', hEp'⟩ := oracleImplRSessionTracked_step_support_full hT
                C K d.idA d.idB d.spkCoins qep (qSessDone i) decT encT q'
                hgsReach hgsEp hTr0 hstep
              have hNextEq : nextSessDone qStart qSessDone i i = qSessDone i + 1 := by
                simp [nextSessDone, hiLt]
              refine ⟨{
                ki_le := h.ki_le
                send_le := h.send_le
                start_le := h.start_le
                sess_le := hSessLe
                sends_le_ki := h.sends_le_ki
                sends_le_send := h.sends_le_send
                insts_le_start := by simp [h.insts_le_start]
                subsetSends := h.subsetSends.setInstSameSid (d' := { d with gs := some gs' })
                  hd rfl rfl rfl
                mirror := ⟨h.mirror.prins_le, h.mirror.bundles_le, h.mirror.opks_le,
                  h.mirror.sends_le, h.mirror.corrPrins_le,
                  by simp [h.mirror.insts_le], by simp [h.mirror.instMeta_le],
                  h.mirror.revSpks_le⟩
                metaAligned := by
                  have hm := h.metaAligned
                  simp [Computational.Proofs.E2E.Dsl.M3Interfaces.DrvMetaAligned] at hm ⊢
                  exact hm
                kiReach := h.kiReach
                tracks_len := by simp [h.tracks_len]
                slot_reach := fun idx d' hd' gs0 hgs0 => by
                  dsimp only at hd'
                  by_cases hji : idx = i
                  · subst hji
                    rw [List.getElem?_set_self hiLen, Option.some.injEq] at hd'
                    subst hd'
                    simp only [Option.mem_def, Option.some.injEq] at hgs0
                    subst hgs0
                    rw [hNextEq]
                    exact ⟨hReach', hEp'⟩
                  · rw [List.getElem?_set_ne (Ne.symm hji)] at hd'
                    have hSame : nextSessDone qStart qSessDone i idx = qSessDone idx := by
                      simp [nextSessDone, hji]
                    rw [hSame]
                    exact h.slot_reach idx d' hd' gs0 hgs0
                slot_track := fun idx tr0 htr0 => by
                  dsimp only at htr0
                  by_cases hji : idx = i
                  · subst hji
                    rw [List.getElem?_set_self hiTrLen, Option.some.injEq] at htr0
                    subst htr0
                    rw [hNextEq]
                    exact hTr'
                  · rw [List.getElem?_set_ne (Ne.symm hji)] at htr0
                    have hSame : nextSessDone qStart qSessDone i idx = qSessDone idx := by
                      simp [nextSessDone, hji]
                    rw [hSame]
                    exact h.slot_track idx tr0 htr0
              }, fun k ⟨hkLt, hkNone⟩ => ?_⟩
              have hne : i ≠ k := by
                intro hik; subst hik
                exact absurd (hkNone d hd) (by simp [hgs])
              refine ⟨by simp [hkLt], fun d' hd' => ?_⟩
              dsimp only at hd'
              rw [List.getElem?_set_ne hne] at hd'
              exact hkNone d' hd'
            rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
            · dsimp only at hout; exact hrunTr _ hout
            · dsimp only at hout; exact hrunTr _ hout
            · cases pDl
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunTr _ hout
              · dsimp only at hout
                split_ifs at hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hpure hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunTr _ hout
                    · exact hpure hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hrunTr _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunTr _ hout
                    · exact hpure hout
            · cases pIj
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunTr _ hout
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cIj
                  · rw [hdec] at hout; dsimp only at hout; exact hrunTr _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunTr _ hout
                    · exact hpure hout
            · dsimp only at hout; exact hrunTr _ hout

private theorem map_sid_mapIdx_paused {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (insts : List (BHModelInst S ℓ)) (k : ℕ) :
    (insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)).map (·.sid) =
      insts.map (·.sid) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_mapIdx]
    split_ifs <;> rfl

theorem HaltedKindSimInvInst.promoteSlotK_paused_preserves
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σ' : BHE2EDrvState S ℓ} {tracks' : List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone
      (σ', tracks'))
    {k : ℕ} (hk : k < σ'.insts.length) :
    let insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
    let σ_p : BHE2EDrvState S ℓ := { σ' with insts := insts', paused := true }
    HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone
      (σ_p, tracks') ∧
    Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k (σ_p, tracks') := by
  dsimp only
  set insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
  refine ⟨{
    ki_le := h.ki_le
    send_le := h.send_le
    start_le := h.start_le
    sess_le := h.sess_le
    sends_le_ki := h.sends_le_ki
    sends_le_send := h.sends_le_send
    insts_le_start := by simp [insts', h.insts_le_start]
    subsetSends := h.subsetSends.of_sids_sends_eq (map_sid_mapIdx_paused σ'.insts k) rfl
    mirror := ⟨h.mirror.prins_le, h.mirror.bundles_le, h.mirror.opks_le,
      h.mirror.sends_le, h.mirror.corrPrins_le,
      by simp [insts', h.mirror.insts_le], h.mirror.instMeta_le, h.mirror.revSpks_le⟩
    metaAligned := by
      have hm := h.metaAligned
      simp [Computational.Proofs.E2E.Dsl.M3Interfaces.DrvMetaAligned, insts'] at hm ⊢
      exact hm
    kiReach := h.kiReach
    tracks_len := by simp [insts', h.tracks_len]
    slot_reach := fun idx d' hd' gs0 hgs0 => by
      dsimp only at hd'
      simp only [insts', List.getElem?_mapIdx] at hd'
      cases horig : σ'.insts[idx]? with
      | none => simp [horig] at hd'
      | some d0 =>
        simp only [horig, Option.map_some, Option.some.injEq] at hd'
        subst hd'
        split_ifs at hgs0 with hik
        · simp at hgs0
        · exact h.slot_reach idx d0 horig gs0 hgs0
    slot_track := h.slot_track
  }, ⟨by simp [insts', hk], fun d hd => ?_⟩⟩
  simp only [insts', List.getElem?_mapIdx, List.getElem?_eq_getElem hk,
    Option.map_some, ↓reduceIte, Option.some.injEq] at hd
  subst hd; rfl

theorem HaltedKindSimInvInst.commitExtSm_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {k : ℕ} {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedKindSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    (hPaused : Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k σH)
    (hSessNext : k < qStart → qSessDone k + 1 ≤ qs k)
    (sq' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sr : CryptoVerification.E2E.BHE2ESmResp ℓ) :
    let σ1 := (CryptoVerification.E2E.bhShallowCommitExtSm k σH.1 sq' sr).2
    HaltedKindSimInvInst TrackInv C K b qStart qs
      qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone k) (σ1, σH.2) ∧
    Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedPausedInv k (σ1, σH.2) := by
  rcases σH with ⟨σ, tracks⟩
  dsimp only
  set σ1 := (CryptoVerification.E2E.bhShallowCommitExtSm k σ sq' sr).2
  have hFields :
      σ1.prins = σ.prins ∧ σ1.bundles = σ.bundles ∧ σ1.opks = σ.opks ∧
      σ1.sends = σ.sends ∧ σ1.corrPrins = σ.corrPrins ∧ σ1.revealedSpks = σ.revealedSpks ∧
      σ1.insts = σ.insts ∧ σ1.instMeta.length = σ.instMeta.length ∧ σ1.st = σ.st := by
    dsimp only [σ1, CryptoVerification.E2E.bhShallowCommitExtSm]
    split_ifs
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases σ.insts[k]? <;> cases σ.instMeta[k]?
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · dsimp only
        split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, rfl⟩
  rcases hFields with ⟨hP, hB, hO, hS, hCp, hRv, hInsts, hMetaL, hSt⟩
  have hSessMono : ∀ idx, qSessDone idx ≤ nextSessDone qStart qSessDone k idx := by
    intro idx
    dsimp only [nextSessDone]
    split_ifs with hcond
    · rcases hcond with ⟨_, rfl⟩; omega
    · exact le_rfl
  refine ⟨{
    ki_le := h.ki_le
    send_le := h.send_le
    start_le := h.start_le
    sess_le := fun j hj => by
      dsimp only [nextSessDone]
      split_ifs with hkj
      · rcases hkj with ⟨hk, rfl⟩; exact hSessNext hk
      · exact h.sess_le j hj
    sends_le_ki := by rw [hS]; exact h.sends_le_ki
    sends_le_send := by rw [hS]; exact h.sends_le_send
    insts_le_start := by rw [hInsts]; exact h.insts_le_start
    subsetSends := h.subsetSends.of_sids_sends_eq (congrArg (List.map (·.sid)) hInsts) hS
    mirror := ⟨by rw [hP]; exact h.mirror.prins_le,
      by rw [hB]; exact h.mirror.bundles_le,
      by rw [hO]; exact h.mirror.opks_le,
      by rw [hS]; exact h.mirror.sends_le,
      by rw [hCp]; exact h.mirror.corrPrins_le,
      by rw [hInsts]; exact h.mirror.insts_le,
      by rw [hMetaL]; exact h.mirror.instMeta_le,
      by rw [hRv]; exact h.mirror.revSpks_le⟩
    metaAligned := by
      unfold Computational.Proofs.E2E.Dsl.M3Interfaces.DrvMetaAligned
      rw [hMetaL, hInsts]; exact h.metaAligned
    kiReach := by rw [hSt]; exact h.kiReach
    tracks_len := by dsimp only; rw [hInsts]; exact h.tracks_len
    slot_reach := fun idx d hd gs0 hgs0 => by
      dsimp only at hd; rw [hInsts] at hd
      obtain ⟨hr, he⟩ := h.slot_reach idx d hd gs0 hgs0
      exact ⟨hr.mono (hSessMono idx), he.mono (hSessMono idx)⟩
    slot_track := fun idx tr htr =>
      hT.mono (hSessMono idx) (h.slot_track idx tr htr)
  }, ⟨by dsimp only; rw [hInsts]; exact hPaused.1, fun d hd => by
      dsimp only at hd; rw [hInsts] at hd; exact hPaused.2 d hd⟩⟩

end Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst
