/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp2
import Computational.Proofs.GameHop.CompDedup

/-!
# Step Invariant Preservation and Sanitized-vs-Dedup Agreement for `SimDeliverForge`

Proves single-step preservation of `DFStateInv` and `SanSnapExtra` along `simDeliverForgeOracleSan`,
and single-step agreement between `simDeliverForgeOracleSan`, `simDeliverForgeOracleDedup`, and
`simDeliverForgeOracle`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.HMAC (keyToBytes32)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart ratchetKeyAdmissible)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimFig8C GhostChain SimState
  toGhost pushChain inReceiveOnlyEpoch SemHook SimCStateBounded SimCStateInv
  mkPub simParseRecvC onAcceptPure onAnswerPure semSendHook semCorrHookDedup semHandleHookDedup
  simStateCCanon simStateCCanon_idem
  deliverForgeSemHook simDeliverForgeOracle simDeliverForgeOracleDedup)
open _root_.CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState)
open _root_.CryptoGames.SM (RecvResult partyEnc noBobSendInEpoch0 noAliceCorrWhileAliceBelowEpoch10)
open Computational.Proofs.GameHop.CompDedup (afterCorrDedup run'_simulateQ_eq_of_idem_proj)
open _root_.CryptoGames.SM.Construction.DeliverForge (specDF)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState Params)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1 coinBytes)
open CryptoVerification.SpqrV1Sync.SendTotal (TopStateTight topStateTight_send topStateTight_recv)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (fig8StTruncSkB evalCKS semFwdAnswerHookS semResyncHookS semFwdEvictHookS semFwdHookS
   semRecvHookS semCorrHookTGB semHandleHookDedupS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (SanExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanSem (semHandleHookDedupS_pq)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (semHandleHookDedup_simStateCCanon' semHandleHook_simStateCCanon')
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame (SkippedLenLe KeptInv)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
  (SnapWF SanSnapExtra semHandleHookDedupS_inl_eq)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (simDeliverForgeOracleSan DFStateInv DFStateBounded simDeliverForgeOracleSan_preserves_dfStateInv)

section SnapExtraHelpers

private theorem modify_mem_inv {α : Type} {P : α → Prop} {cs : List α} {ci : ℕ} {f : α → α}
    (hcs : ∀ x ∈ cs, P x) (hf : ∀ x, P x → P (f x)) :
    ∀ y ∈ cs.modify ci f, P y := by
  induction cs generalizing ci with
  | nil => intro _ hy; simp at hy
  | cons a xs ih =>
    cases ci with
    | zero =>
      intro y hy; dsimp only [List.modify] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hf _ (hcs _ (List.mem_cons_self ..))
      · exact hcs y (List.mem_cons_of_mem _ hy)
    | succ ci' =>
      intro y hy; dsimp only [List.modify] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hcs _ (List.mem_cons_self ..)
      · exact ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) y hy

private theorem ghostChain_accept_skipped_le (g : GhostChain) (i : ℕ)
    (hg : g.skipped.length ≤ 2000) : (g.accept i).skipped.length ≤ 2000 := by
  unfold GhostChain.accept
  split_ifs
  · exact List.length_take_le 2000 _
  · exact Nat.le_trans List.erase_sublist.length_le hg

private theorem pushChain_chains_wf (cs : List GhostChain) (g : GhostChain)
    (hcs : ∀ x ∈ cs, x.skipped.length ≤ 2000) (hg : g.skipped.length ≤ 2000) :
    (pushChain cs g).length ≤ 5 ∧ ∀ x ∈ pushChain cs g, x.skipped.length ≤ 2000 := by
  refine ⟨by simp [pushChain]; omega, fun x hx => ?_⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hx) with hmem | hmem
  · exact hcs x hmem
  · rw [List.mem_singleton.mp hmem]; exact hg

private theorem modify_accept_chains_wf (cs : List GhostChain) (ci i : ℕ)
    (hlen : cs.length ≤ 5) (hcs : ∀ x ∈ cs, x.skipped.length ≤ 2000) :
    (cs.modify ci (·.accept i)).length ≤ 5 ∧
      ∀ x ∈ cs.modify ci (·.accept i), x.skipped.length ≤ 2000 :=
  ⟨by rw [List.length_modify]; exact hlen,
   modify_mem_inv hcs (fun g hg => ghostChain_accept_skipped_le g i hg)⟩

private theorem chains_wf_update {f : Party → List GhostChain} {Q : Party} {cs : List GhostChain}
    (hf : ∀ R, (f R).length ≤ 5 ∧ ∀ g ∈ f R, g.skipped.length ≤ 2000)
    (hcs : cs.length ≤ 5 ∧ ∀ g ∈ cs, g.skipped.length ≤ 2000) :
    ∀ R, (Function.update f Q cs R).length ≤ 5 ∧
      ∀ g ∈ Function.update f Q cs R, g.skipped.length ≤ 2000 := by
  intro R; by_cases hR : R = Q
  · subst hR; simpa using hcs
  · simpa [Function.update_of_ne hR] using hf R

private theorem onAcceptPure_chains_wf {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, (s.chains R).length ≤ 5 ∧ ∀ g ∈ s.chains R, g.skipped.length ≤ 2000) :
    ∀ R, ((onAcceptPure qep Q w isDel t i m ci? Tpk pq' s).2.chains R).length ≤ 5 ∧
      ∀ g ∈ (onAcceptPure qep Q w isDel t i m ci? Tpk pq' s).2.chains R,
        g.skipped.length ≤ 2000 := by
  let cs' : List GhostChain := match ci? with
    | some ci => (s.chains Q).modify ci (·.accept i)
    | none => pushChain (s.chains Q) (GhostChain.accept ⟨some Tpk, t, 0, []⟩ i)
  have hcs : cs'.length ≤ 5 ∧ ∀ g ∈ cs', g.skipped.length ≤ 2000 := by
    rcases ci? with _ | ci
    · exact pushChain_chains_wf (s.chains Q) _ (hs Q).2
        (ghostChain_accept_skipped_le ⟨some Tpk, t, 0, []⟩ i (Nat.zero_le _))
    · exact modify_accept_chains_wf (s.chains Q) ci i (hs Q).1 (hs Q).2
  have hu := chains_wf_update (Q := Q) hs hcs
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | exact hs | exact hu
  · simp only [↓reduceIte]
    rcases s.mir.inTransit Q.other w with _ | _
    · exact hs
    · exact hu

private theorem onAcceptPure_honest {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? Tpk pq' s).2.honest = s.honest := by
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> rfl
  · simp only [↓reduceIte]; rcases s.mir.inTransit Q.other w with _ | _ <;> rfl

private theorem onAnswerPure_chains_wf {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, (s.chains R).length ≤ 5 ∧ ∀ g ∈ s.chains R, g.skipped.length ≤ 2000) :
    ∀ R, ((onAnswerPure qep Q w isDel ci? Tpk pq' res s).2.chains R).length ≤ 5 ∧
      ∀ g ∈ (onAnswerPure qep Q w isDel ci? Tpk pq' res s).2.chains R,
        g.skipped.length ≤ 2000 := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact onAcceptPure_chains_wf qep Q w isDel t i ((pm.map (·.2)).getD default) ci? Tpk pq' s hs

private theorem toGhost_snapWF {PQ PQC Pt : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt)
    (hQ : (s.chains Q).length ≤ 5 ∧ ∀ g ∈ s.chains Q, g.skipped.length ≤ 2000) :
    SnapWF (toGhost P s Q st) := by
  unfold SnapWF toGhost; dsimp only
  refine ⟨by rw [List.length_map]; exact hQ.1, fun rc hrc => ?_⟩
  rw [List.mem_map] at hrc; obtain ⟨g, hg, rfl⟩ := hrc
  rcases st.vR g.epoch with _ | v
  · exact ⟨Nat.zero_le _, fun _ hm => nomatch hm⟩
  · dsimp only
    refine ⟨Nat.le_trans (List.length_filterMap_le _ _) (hQ.2 g hg), fun mk hmk => ?_⟩
    rw [List.mem_filterMap] at hmk; obtain ⟨j, -, hj⟩ := hmk
    rcases hlk : v.skippedKeys.lookup j with _ | k
    · simp [hlk] at hj
    · simp only [hlk, Option.map_some, Option.some.injEq] at hj
      subst hj; simp [keyToBytes32]

private def ChainSnapWF {PQ Pt : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) : Prop :=
  (∀ R, (sC.base.chains R).length ≤ 5 ∧ ∀ g ∈ sC.base.chains R, g.skipped.length ≤ 2000) ∧
    (∀ e ∈ sC.snaps, SnapWF e.2.2) ∧
    (∀ wc ∈ sC.base.honest, wc.1 = _root_.CryptoGames.Ratchet.LibsignalSim.toWire wc.2)

private theorem semSendHook_chainSnapWF {PQ PQC Pt : Type} [Zero Pt] {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semSendHook P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ chal r),
      ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx; unfold semSendHook at hx
  by_cases href : (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, _⟩; exact hs
    · by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨_, rfl, _⟩; exact hs
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
        obtain ⟨⟨rq, rc⟩, -, ⟨exOk, exFail⟩, -, hx⟩ := hx
        rcases hpub : mkPub P sC₀.base Q rq
          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with _ | ⟨pq', pub⟩ <;>
          simp only [hpub] at hx
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hs
        · simp only [mem_support_bind_iff] at hx; obtain ⟨⟨res, ex₂⟩, -, hx⟩ := hx
          rcases res with _ | c <;>
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          · rcases hx with ⟨_, rfl, _⟩; exact hs
          · rcases hx with ⟨_, rfl, _⟩
            refine ⟨hs.1, hs.2.1, fun wc hwc => ?_⟩
            rcases List.mem_cons.mp hwc with rfl | h
            · rfl
            · exact hs.2.2 wc h

private theorem semFwdAnswerHookS_chainSnapWF {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semFwdAnswerHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w isDel ci? Tpk pq' c'),
      ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx; unfold semFwdAnswerHookS at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨res, ex'⟩, -, _, rfl, _⟩ := hx
  refine ⟨onAnswerPure_chains_wf qep Q w isDel ci? Tpk pq' res sC₀.base hs.1,
    by rcases res with _ | (_ | ⟨t, i, pm⟩) <;> exact hs.2.1, ?_⟩
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs.2.2
  · exact hs.2.2
  · dsimp only [onAnswerPure]; rw [onAcceptPure_honest]; exact hs.2.2

private theorem semResyncHookS_chainSnapWF {PQ PQC Pt : Type} [Zero Pt] {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : SimFig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semResyncHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w ci? Tpk pq' c r),
      ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx; unfold semResyncHookS at hx
  rcases r with _ | ⟨t, i, _, m'⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [mem_support_bind_iff] at hx; obtain ⟨⟨res, ex'⟩, -, hx⟩ := hx
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hx with ⟨_, rfl, _⟩
      exact ⟨onAcceptPure_chains_wf qep Q w true t i m' ci? Tpk pq' sC₀.base hs.1, hs.2.1,
        by dsimp only; rw [onAcceptPure_honest]; exact hs.2.2⟩

private theorem semFwdEvictHookS_chainSnapWF {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semFwdEvictHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w isDel Tpk pq' c'),
      ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx; unfold semFwdEvictHookS at hx; split_ifs at hx
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨_, -, _, rfl, _⟩ := hx; exact hs
  · exact semFwdAnswerHookS_chainSnapWF P Dh encPt encT lam T sh qep
      sC₀ ex₀ Q w isDel none Tpk pq' c' hs _ hx

private theorem semFwdHookS_chainSnapWF {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T K : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support
        (semFwdHookS P Dh encPt encT lam T K sh qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c'),
      ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx; unfold semFwdHookS at hx
  rcases honestC with _ | c
  · exact semFwdAnswerHookS_chainSnapWF P Dh encPt encT lam T sh qep
      sC₀ ex₀ Q w isDel ci? Tpk pq' c' hs _ hx
  · dsimp only [] at hx; split_ifs at hx
    · rcases hev : evalCKS P Dh encPt encT lam T K B sC₀ Q w c c' with _ | r <;>
        simp only [hev] at hx
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        obtain ⟨_, -, _, rfl, _⟩ := hx; exact hs
      · exact semResyncHookS_chainSnapWF P Dh encPt encT lam T sh qep
          sC₀ ex₀ Q w ci? Tpk pq' c r hs _ hx
    · exact semFwdAnswerHookS_chainSnapWF P Dh encPt encT lam T sh qep
        sC₀ ex₀ Q w isDel ci? Tpk pq' c' hs _ hx

private theorem semRecvHookS_chainSnapWF {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (T K : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semRecvHookS P Dh encPt encT decT lam T K sh qep B sC₀ ex₀ Q w isDel),
      ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx; unfold semRecvHookS at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hparse : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;> simp only [hparse] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hsAmb : ChainSnapWF
            ({ sC₀ with base :=
                if inReceiveOnlyEpoch sC₀.base.mir Q ||
                  (Q == Party.A && (sC₀.base.chains Q).any (·.key.isNone))
                then { sC₀.base with amb := sC₀.base.amb + 1 } else sC₀.base } :
              LibsignalToModularSchemeSimState PQ Pt ℓ) :=
        ⟨fun R => by split_ifs <;> exact hs.1 R, hs.2.1, by split_ifs <;> exact hs.2.2⟩
        by_cases hc1 :
            ((((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true &&
             (((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hs
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨_, rfl, _⟩; exact hs
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) ||
                  decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨_, rfl, _⟩; exact hsAmb
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hT : T? with _ | T₀ <;> simp only [hT] at hx
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
                rcases hx with ⟨_, rfl, _⟩; exact hsAmb
              · by_cases hev_b :
                    ((((sC₀.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  exact semFwdEvictHookS_chainSnapWF P Dh encPt encT lam T sh qep
                    _ ex₀ Q w isDel pk pq' _ hsAmb _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHookS_chainSnapWF P Dh encPt encT lam T K sh qep B
                    _ ex₀ Q w isDel none pk pq' _ _ hsAmb _ hx
      · by_cases hrej : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hs
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          exact semFwdHookS_chainSnapWF P Dh encPt encT lam T K sh qep B
            sC₀ ex₀ Q w isDel (some ci) pk pq' _ _ hs _ hx

private theorem semCorrHookTGB_chainSnapWF {PQ PQC Pt : Type} {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (sh : SemHook PQC Pt ℓ T' Ex) (B_skip : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semCorrHookTGB P Dh encT sh B_skip sC₀ ex₀ Q), ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx; unfold semCorrHookTGB at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, -, hx⟩ := hx
    rcases res with _ | fig8st <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hx with ⟨_, rfl, _⟩
      set chains' : Party → List GhostChain :=
        if Q == Party.B && sC₀.base.mir.epoch Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC₀.base.chains Party.A
              ((sC₀.base.chains Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC₀.base.chains
        else sC₀.base.chains
      have hch' : ∀ R, (chains' R).length ≤ 5 ∧ ∀ g ∈ chains' R, g.skipped.length ≤ 2000 := by
        dsimp only [chains']; split_ifs
        · rcases fig8st.γ with _ | x
          · exact hs.1
          · refine chains_wf_update hs.1 ⟨by simpa using (hs.1 .A).1, fun g' hg' => ?_⟩
            rcases List.mem_map.mp hg' with ⟨g, hg, rfl⟩
            split_ifs <;> exact (hs.1 .A).2 g hg
        · exact hs.1
      refine ⟨hch', fun e he => ?_, hs.2.2⟩
      rcases List.mem_cons.mp he with rfl | he'
      · exact toGhost_snapWF P { sC₀.base with chains := chains' } Q
          (fig8StTruncSkB B_skip fig8st) (hch' Q)
      · exact hs.2.1 e he'

private theorem semHandleHookDedupS_chainSnapWF {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (T K B_skip : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep B : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semHandleHookDedupS P Dh encPt encT decT lam T K B_skip sh qep B t sC₀ ex₀),
      ChainSnapWF x.2.1 := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_chainSnapWF P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ none r hs
  · exact semSendHook_chainSnapWF P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ (some m₁) r hs
  · rintro ⟨_, sC₁, ex₁⟩ hx; unfold semHandleHookDedupS at hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨rr, sC', ex'⟩, hrec, ex₂, -, _, rfl, rfl⟩ := hx
    exact semRecvHookS_chainSnapWF P Dh encPt encT decT lam T K sh qep B
      sC₀ ex₀ Q w true hs (rr, sC₁, ex') hrec
  · exact semRecvHookS_chainSnapWF P Dh encPt encT decT lam T K sh qep B sC₀ ex₀ Q w false hs
  · exact semCorrHookTGB_chainSnapWF P Dh encT sh B_skip sC₀ ex₀ Q hs

end SnapExtraHelpers

theorem sanSnapExtra_step_df {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep B T Kc Bsk : ℕ) :
    ∀ t (s : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)),
      SanSnapExtra C K s.1 →
      ∀ x ∈ support ((simDeliverForgeOracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam
          qep B T Kc Bsk (.inr t)).run s), SanSnapExtra C K x.2.1 := by
  rintro t ⟨sC, sent⟩ ⟨hEx, hCS⟩ x hx
  dsimp only [simDeliverForgeOracleSan, StateT.run, StateT.mk] at hx
  have hS : ∀ (pq : Bytes) (r : BitVec 512) (pq' : Bytes) x,
      TopStateTight C.F K pq → (paramsV1 C K idA idB).spqr.send pq r = some (pq', x) →
        TopStateTight C.F K pq' := by
    intro pq r pq' ⟨salt, msg⟩ hpq h
    change (spqrV1 C.F K).send pq (coinBytes r) = some (pq', salt, msg) at h
    exact topStateTight_send C.F K hpq h
  have hR : ∀ (pq msg pq' : Bytes) salt,
      TopStateTight C.F K pq → (paramsV1 C K idA idB).spqr.recv pq msg = .ok (pq', salt) →
        TopStateTight C.F K pq' := by
    intro pq msg pq' salt hpq h
    change (spqrV1 C.F K).recv pq msg = .ok (pq', salt) at h
    exact topStateTight_recv C.F K hpq h
  exact ⟨semHandleHookDedupS_pq (paramsV1 C K idA idB) Dh encPt encT decT lam hS hR
      T Kc Bsk (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B t sC sent hEx x hx,
    semHandleHookDedupS_chainSnapWF (paramsV1 C K idA idB) Dh encPt encT decT lam
      T Kc Bsk (deliverForgeSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ)) qep B t sC sent hCS x hx⟩

/-- Combined step-wise preservation of `DFStateInv L m` (`SimCStateInv L m` and
`sent.length + m ≤ L`), `SimCStateBounded L`, `sent.length ≤ L`, and `SanSnapExtra C K`
along `simDeliverForgeOracleSan`. -/
theorem simDeliverForgeOracleSan_step_preserves_inv {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (L m qep B T Kc Bsk : ℕ)
    (t : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (s : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt))
    (hInv : DFStateInv L (m + 1) s) (hEx : SanSnapExtra C K s.1) :
    ∀ x ∈ support ((simDeliverForgeOracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam
        qep B T Kc Bsk (.inr t)).run s),
      DFStateInv L m x.2 ∧ SimCStateBounded L x.2.1 ∧ x.2.2.length ≤ L ∧
        SanSnapExtra C K x.2.1 := by
  intro x hx
  have hdf := simDeliverForgeOracleSan_preserves_dfStateInv (paramsV1 C K idA idB)
    Dh encPt encT decT lam L m qep B T Kc Bsk t s hInv x hx
  have hbd : DFStateBounded L x.2 := hdf.toBounded
  exact ⟨hdf, hbd.1, hbd.2,
    sanSnapExtra_step_df C K idA idB Dh encPt encT decT lam qep B T Kc Bsk t s hEx x hx⟩

theorem fig8StTruncSkB_eq_self {Pt : Type} {B0 Bsk : ℕ} {st : Fig8St Pt}
    (hsk : ∀ t v, st.vR t = some v → SkippedLenLe B0 v) (hle : B0 ≤ Bsk) :
    fig8StTruncSkB Bsk st = st := by
  rcases st with ⟨id0, root0, vS0, vR0, γ0, curCkaMsg0, tcur0⟩
  dsimp [fig8StTruncSkB] at hsk ⊢
  congr 1
  funext t
  cases hv : vR0 t with
  | none => rfl
  | some v =>
    dsimp [Option.map]
    congr 1
    have hvle : v.skippedKeys.length ≤ Bsk := Nat.le_trans (hsk t v hv) hle
    rcases v with ⟨ck, li, sk⟩
    dsimp at hvle ⊢
    rw [List.take_of_length_le hvle]

/-- On non-corrupt game queries (`t = .inl t₀`), `simDeliverForgeOracleSan` agrees identically
with `simDeliverForgeOracleDedup` under `KeptInv B0` (`B0 ≤ T`) and bounded chain `last`
(`g.last + 25000 ≤ Kc`). -/
theorem simDeliverForgeOracleSan_inr_inl_eq {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ B0 T Kc Bsk B : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep : ℕ)
    (t₀ : (((Party × Plain ℓ × Option PQC →ₒ Option Bytes) +
      (Party × Plain ℓ × Plain ℓ × Option PQC →ₒ Option Bytes) +
      (Party × Bytes →ₒ Option (RecvResult (Plain ℓ)))) +
      (Party × Bytes →ₒ Option (RecvResult (Plain ℓ)))).Domain)
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt))
    (hT : B0 ≤ T) (hk : ∀ R, KeptInv B0 (s.1.kept R))
    (hK0 : 25000 ≤ Kc) (hchains : ∀ R, ∀ g ∈ s.1.base.chains R, g.last + 25000 ≤ Kc) :
    (simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk (.inr (.inl t₀))).run s =
      (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B (.inr (.inl t₀))).run s :=
  semHandleHookDedupS_inl_eq P Dh encPt encT decT lam
    (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep t₀ s.1 s.2 hT hk hK0 hchains

/-- On corrupt game queries (`t = .inr Q`), running `simDeliverForgeOracleSan` under any outer
`QueryImpl` agrees with `simDeliverForgeOracleDedup` whenever every `some fig8st` returned by
`deliverForgeSemHook.onCr Q` satisfies `SkippedLenLe Bsk fig8st`. -/
theorem simDeliverForgeOracleSan_inr_inr_eq_of_support {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ T Kc Bsk B : ℕ} {σ : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep : ℕ) (Q : Party)
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt))
    (impl : QueryImpl
      (unifSpec + specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (StateT σ ProbComp))
    (ms : σ)
    (hcr : ∀ x ∈ support ((simulateQ impl
        ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onCr Q s.2)).run ms),
      ∀ fig8st, x.1.1 = some fig8st → ∀ t v, fig8st.vR t = some v → SkippedLenLe Bsk v) :
    (simulateQ impl
      ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk (.inr (.inr Q))).run s)).run ms =
    (simulateQ impl
      ((simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B (.inr (.inr Q))).run s)).run ms := by
  rcases s with ⟨sC, sent⟩
  dsimp only [simDeliverForgeOracleSan, simDeliverForgeOracleDedup,
    semHandleHookDedupS, semHandleHookDedup, semCorrHookTGB, semCorrHookDedup,
    StateT.run, StateT.mk]
  by_cases href :
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp only [href, ↓reduceIte]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
    refine bind_congr_of_forall_mem_support _ fun x hx => ?_
    rcases x with ⟨⟨res, ex₁⟩, ms'⟩
    rcases res with _ | fig8st
    · rfl
    · dsimp only
      rw [fig8StTruncSkB_eq_self (hcr _ hx fig8st rfl) le_rfl]
      cases fig8st.γ <;> rfl

theorem run'_simulateQ_simDeliverForgeOracleDedup_eq_public {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep B : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (st : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) :
    (simulateQ (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B) A).run' st =
      (simulateQ (simDeliverForgeOracle P Dh encPt encT decT lam qep B) A).run' st := by
  refine run'_simulateQ_eq_of_idem_proj
    (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B)
    (simDeliverForgeOracle P Dh encPt encT decT lam qep B)
    (Prod.map simStateCCanon id) ?_ ?_ A rfl
  · rintro (n | t) ⟨sC, ex⟩
    · simp [simDeliverForgeOracleDedup, simDeliverForgeOracle, StateT.run_lift, Prod.map,
        simStateCCanon_idem]
    · exact semHandleHookDedup_simStateCCanon' P Dh encPt encT decT lam deliverForgeSemHook
        qep B t sC ex
  · rintro (n | t) ⟨sC, ex⟩
    · simp [simDeliverForgeOracle, StateT.run_lift, Prod.map, simStateCCanon_idem]
    · exact semHandleHook_simStateCCanon' P Dh encPt encT decT lam deliverForgeSemHook
        qep B t sC ex

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
