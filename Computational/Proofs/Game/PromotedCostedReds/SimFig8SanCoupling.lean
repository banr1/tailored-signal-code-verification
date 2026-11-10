/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanSem
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep

/-!
# Sanitized `simFig8` Snapshot Invariant, Game Coupling, and `SimFig8EvalOk` Bridge

Proves preservation of the combined snapshot and ghost-chain invariant `SanSnapExtra` under
`simFig8OracleSan`, couples `simFig8ClampSan` with `simFig8ClampTG` and `libsignalToModularSchemeSim`
in `SM.run`, and derives `SimFig8EvalOk` for `simFig8ProgOfStep`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling

open OracleSpec OracleComp
open ReductionDsl (Comp handlerImpl isGameQuery bits atomicSessionOps fig8SmIface
  e2eSessionCodec GhostStT smQT smRT)
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState skipKeys fromAEADPRG)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  lPubOf lChainPRG lAead lFS lFig8 dummyKey ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimFig8C Fig8Comp GhostChain SimState
  initSim toGhost toWire pushChain inReceiveOnlyEpoch SemHook SimCStateBounded
  mkPub simParseRecvC fig8Clamp fsClampSim simKDecryptFig8
  onAcceptPure onAnswerPure scPostSendPure evalCKClamp
  semDrawSendCoins semSendHook semFwdAnswerHook semResyncHook semFwdEvictHook semFwdHook semRecvHook
  semCorrHookDedup semHandleHookDedup makesAtMostQueries_iff_isGameQuery)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState initSimC
  sentEval predictReceive chainSeedAt snapshotMessageKeySeed)
open CryptoGames.SM (GameState RecvResult partyEnc partyDec noBobSendInEpoch0
  noAliceCorrWhileAliceBelowEpoch10)
open CryptoGames.SM.Construction (Header PartyState initParty)
open CryptoGames.LibsignalSession (ShaCompress Crypto IdentityKey PublicKey PrivateKey GhostState
  ChainKey Params SignalMessage SignalMessageProtoCodec signalWireCodec rootCreateChain)
open CryptoGames.LibsignalSM.Proofs.Refinement (tryFrom_of_parse)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes idsOf paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (sanRS sanGamma sanAt fig8San fsSan fig8StTruncSkB chainSeedAtB snapshotMessageKeySeedB
   figS fsS evalCKS semFwdAnswerHookS semResyncHookS semFwdEvictHookS semFwdHookS semRecvHookS
   semCorrHookTGB semHandleHookDedupS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
  (simFig8OracleSan simFig8ClampSan SanExtra simFig8ProgOfStep_eval_san)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanSem
  (simFig8ClampSan_queries simFig8ClampSan_equalPub simFig8ClampSan_sendShort
   sanExtra_init sanExtra_step)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (lengthsOk_paramsIdsWithSpqr_v1 simFullT simFullDec simFig8ProgOfStep fig8IdSemHook
   semCorrHookTGDedup simFig8OracleTG simFig8OracleTGDedup simFig8ClampTG
   run'_simulateQ_simFig8OracleTGDedup_eq
   sm_run_simFig8ClampTG_eq sm_game_simFig8ClampTG_eq simCNoneWinEvent_eq_sm_run_simFig8ClampTG
   SimFig8EvalOk SimFig8AtomicStepBundle atomicFig8RedDescBits simFig8ProgOfStep_gRedBounded
   simFig8ProgOfStep_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicCompDescBits ratchetDescBudget)

/-! ## Snapshot well-formedness and `SanSnapExtra` -/

/-- Well-formedness of a corruption `GhostState` snapshot: at most 5 receiver chains, at most 2000
stored message keys per chain, and 32-byte message-key seeds. -/
def SnapWF {PQ : Type} (gh : GhostState PQ) : Prop :=
  gh.session.receiverChains.length ≤ 5 ∧
    ∀ rc ∈ gh.session.receiverChains,
      rc.messageKeys.length ≤ 2000 ∧ ∀ mk ∈ rc.messageKeys, mk.seed.length = 32

/-- Combined simulator-only invariant for atomic `simFig8` steps: tight SPQR states (`SanExtra`),
bounded ghost chains (`≤ 5` chains, `≤ 2000` skipped indices), `SnapWF` on all snapshots, and
canonical wire encoding on `honest`. -/
def SanSnapExtra {ℓ : ℕ} {Pt : Type} (C : Crypto) (K : MlKem)
    (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) : Prop :=
  SanExtra C K sC ∧
    (∀ R, (sC.base.chains R).length ≤ 5 ∧ ∀ g ∈ sC.base.chains R, g.skipped.length ≤ 2000) ∧
    (∀ e ∈ sC.snaps, SnapWF e.2.2) ∧
    (∀ wc ∈ sC.base.honest, wc.1 = toWire wc.2)

section SnapExtraProofs

private theorem modify_mem_inv {α : Type} {P : α → Prop} {cs : List α} {ci : ℕ} {f : α → α}
    (hcs : ∀ x ∈ cs, P x) (hf : ∀ x, P x → P (f x)) :
    ∀ y ∈ cs.modify ci f, P y := by
  induction cs generalizing ci with
  | nil => intro _ hy; simp at hy
  | cons a xs ih =>
    cases ci with
    | zero =>
      intro y hy
      dsimp only [List.modify] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hf _ (hcs _ (List.mem_cons_self ..))
      · exact hcs y (List.mem_cons_of_mem _ hy)
    | succ ci' =>
      intro y hy
      dsimp only [List.modify] at hy
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
  refine ⟨by simp [pushChain]; omega, ?_⟩
  intro x hx
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
  intro R
  by_cases hR : R = Q
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
    split_ifs
    · exact hs
    · exact hu
    · exact hs
  · simp only [↓reduceIte]
    rcases s.mir.inTransit Q.other w with _ | _
    · exact hs
    · exact hu

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
  unfold SnapWF toGhost
  dsimp only
  refine ⟨by rw [List.length_map]; exact hQ.1, ?_⟩
  intro rc hrc
  rw [List.mem_map] at hrc
  obtain ⟨g, hg, rfl⟩ := hrc
  rcases st.vR g.epoch with _ | v
  · exact ⟨Nat.zero_le _, fun _ hm => nomatch hm⟩
  · dsimp only
    refine ⟨Nat.le_trans (List.length_filterMap_le _ _) (hQ.2 g hg), ?_⟩
    intro mk hmk
    rw [List.mem_filterMap] at hmk
    obtain ⟨j, -, hj⟩ := hmk
    rcases hlk : v.skippedKeys.lookup j with _ | k
    · simp [hlk] at hj
    · simp only [hlk, Option.map_some, Option.some.injEq] at hj
      subst hj
      simp [keyToBytes32]

private theorem onAcceptPure_honest_eq {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? Tpk pq' s).2.honest = s.honest := by
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> rfl
  · simp only [↓reduceIte]; rcases s.mir.inTransit Q.other w with _ | _ <;> rfl

private def ChainSnapWF {PQ Pt : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) : Prop :=
  (∀ R, (sC.base.chains R).length ≤ 5 ∧ ∀ g ∈ sC.base.chains R, g.skipped.length ≤ 2000) ∧
    (∀ e ∈ sC.snaps, SnapWF e.2.2) ∧
    (∀ wc ∈ sC.base.honest, wc.1 = toWire wc.2)

private theorem semSendHook_chainSnapWF {PQ PQC Pt : Type} [Zero Pt] {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semSendHook P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ chal r),
      ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semSendHook at hx
  by_cases href : (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;>
      simp only [hep] at hx
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
        · simp only [mem_support_bind_iff] at hx
          obtain ⟨⟨res, ex₂⟩, -, hx⟩ := hx
          rcases res with _ | c <;>
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          · rcases hx with ⟨_, rfl, _⟩; exact hs
          · rcases hx with ⟨_, rfl, _⟩
            refine ⟨hs.1, hs.2.1, fun wc hwc => ?_⟩
            unfold scPostSendPure at hwc
            rcases List.mem_cons.mp hwc with rfl | hwc
            · rfl
            · exact hs.2.2 wc hwc

private theorem semFwdAnswerHookS_chainSnapWF {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semFwdAnswerHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w isDel ci? Tpk pq' c'),
      ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdAnswerHookS at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨res, ex'⟩, -, _, rfl, _⟩ := hx
  refine ⟨onAnswerPure_chains_wf qep Q w isDel ci? Tpk pq' res sC₀.base hs.1, ?_, ?_⟩
  · rcases res with _ | (_ | ⟨t, i, pm⟩) <;> exact hs.2.1
  · rcases res with _ | (_ | ⟨t, i, pm⟩)
    · exact hs.2.2
    · exact hs.2.2
    · dsimp only [onAnswerPure]; rw [onAcceptPure_honest_eq]; exact hs.2.2

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
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semResyncHookS at hx
  rcases r with _ | ⟨t, i, _, m'⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, -, hx⟩ := hx
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hx with ⟨_, rfl, _⟩
      exact ⟨onAcceptPure_chains_wf qep Q w true t i m' ci? Tpk pq' sC₀.base hs.1, hs.2.1,
        by dsimp only; rw [onAcceptPure_honest_eq]; exact hs.2.2⟩

private theorem semFwdEvictHookS_chainSnapWF {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semFwdEvictHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w isDel Tpk pq' c'),
      ChainSnapWF x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdEvictHookS at hx
  split_ifs at hx
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
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdHookS at hx
  rcases honestC with _ | c
  · exact semFwdAnswerHookS_chainSnapWF P Dh encPt encT lam T sh qep
      sC₀ ex₀ Q w isDel ci? Tpk pq' c' hs _ hx
  · dsimp only [] at hx
    split_ifs at hx
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
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semRecvHookS at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hparse : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hparse] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hsAmb : ChainSnapWF
            ({ sC₀ with base :=
                if inReceiveOnlyEpoch sC₀.base.mir Q ||
                  (Q == Party.A && (sC₀.base.chains Q).any (·.key.isNone))
                then { sC₀.base with amb := sC₀.base.amb + 1 } else sC₀.base } :
              LibsignalToModularSchemeSimState PQ Pt ℓ) := by
          refine ⟨fun R => ?_, hs.2.1, ?_⟩
          · split_ifs <;> exact hs.1 R
          · dsimp only; split_ifs <;> exact hs.2.2
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
              rcases hT : T? with _ | T₀ <;>
                simp only [hT] at hx
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
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semCorrHookTGB at hx
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
        dsimp only [chains']
        split_ifs
        · rcases fig8st.γ with _ | x
          · exact hs.1
          · refine chains_wf_update hs.1 ⟨by simpa using (hs.1 .A).1, ?_⟩
            intro g' hg'
            rcases List.mem_map.mp hg' with ⟨g, hg, rfl⟩
            split_ifs <;> exact (hs.1 .A).2 g hg
        · exact hs.1
      refine ⟨hch', ?_, hs.2.2⟩
      intro e he
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
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex)
    (hs : ChainSnapWF sC₀) :
    ∀ x ∈ support (semHandleHookDedupS P Dh encPt encT decT lam T K B_skip sh qep B t sC₀ ex₀),
      ChainSnapWF x.2.1 := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_chainSnapWF P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ none r hs
  · exact semSendHook_chainSnapWF P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ (some m₁) r hs
  · rintro ⟨_, sC₁, ex₁⟩ hx
    unfold semHandleHookDedupS at hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨rr, sC', ex'⟩, hrec, ex₂, -, _, rfl, rfl⟩ := hx
    exact semRecvHookS_chainSnapWF P Dh encPt encT decT lam T K sh qep B
      sC₀ ex₀ Q w true hs (rr, sC₁, ex') hrec
  · exact semRecvHookS_chainSnapWF P Dh encPt encT decT lam T K sh qep B sC₀ ex₀ Q w false hs
  · exact semCorrHookTGB_chainSnapWF P Dh encT sh B_skip sC₀ ex₀ Q hs

theorem sanSnapExtra_init {ℓ : ℕ} {Pt : Type} (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (k : BitVec 256) :
    SanSnapExtra (ℓ := ℓ) (Pt := Pt) C K
      (initSimC ((paramsV1 C K idA idB).spqr.init .a2b k)
        ((paramsV1 C K idA idB).spqr.init .b2a k)) := by
  refine ⟨sanExtra_init C K idA idB k, ?_, ?_, ?_⟩
  · intro R
    cases R <;> simp [initSimC, initSim]
  · intro e he
    simp [initSimC] at he
  · intro wc hwc
    simp [initSimC, initSim] at hwc

/-- `SanSnapExtra` is preserved by every `simFig8OracleSan (paramsV1 C K idA idB)` game step. -/
theorem sanSnapExtra_step {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep B T Kc Bsk : ℕ) :
    ∀ t (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ), SanSnapExtra C K sC →
      ∀ x ∈ support ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam
          qep B T Kc Bsk (.inr t)).run sC), SanSnapExtra C K x.2 := by
  intro t sC ⟨hEx, hCS⟩ x hx
  refine ⟨sanExtra_step C K idA idB Dh encPt encT decT lam qep B T Kc Bsk t sC hEx x hx, ?_⟩
  dsimp only [simFig8OracleSan, StateT.run, StateT.mk] at hx
  rw [support_map, Set.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact semHandleHookDedupS_chainSnapWF (paramsV1 C K idA idB) Dh encPt encT decT lam
    T Kc Bsk (fig8IdSemHook (PQC := BitVec 512) none) qep B t sC () hCS y hy

end SnapExtraProofs

/-! ## Real-game coupling infrastructure -/

section GameCouplingInfra

abbrev Fig8G (Pt : Type) (ℓ : ℕ) :=
  GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)

/-- Query implementation of `CryptoGames.SM.run fig 3 (qep + 1) cfg`. -/
def fig8GameImpl {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) (StateT (Fig8G Pt ℓ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Fig8G Pt ℓ) ProbComp) +
    CryptoGames.SM.oracleImpl fig 3 (qep + 1) cfg

private theorem simulateQ_fig8GameImpl_liftProb {Pt α : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (p : ProbComp α) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (liftM p : Fig8Comp Pt ℓ α)).run gs =
      (p >>= fun a => pure (a, gs)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (fig8GameImpl fig qep cfg)
      (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl t) >>=
          fun u => liftM (mx u))).run gs =
      ((query t >>= mx) >>= fun a => pure (a, gs))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    have hinl : (simulateQ (fig8GameImpl fig qep cfg)
        (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl t))).run gs =
        (query t >>= fun u => pure (u, gs)) := by
      simp only [query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rfl
    rw [hinl]
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

private theorem simulateQ_fig8GameImpl_inl {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (n : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg)
      ((StateT.lift (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)) :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _).run sC)).run gs =
      (query (spec := unifSpec) n >>= fun u => pure ((u, sC), gs)) := by
  have h : (StateT.lift (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)) :
      StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _).run sC =
      (liftM ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, sC)) :
        Fig8Comp Pt ℓ _) := by
    change (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n) >>=
        fun u => pure (u, sC)) = _
    rw [liftM_bind]
    exact bind_congr fun _ => rfl
  rw [h, simulateQ_fig8GameImpl_liftProb, bind_assoc]
  exact bind_congr fun _ => by simp

private theorem simulateQ_fig8GameImpl_transmitQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (msg : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg)
      (CryptoGames.SM.transmitQuery (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q msg rc)).run gs =
      (CryptoGames.SM.transmitImpl fig 3 (qep + 1) (Q, msg, rc)).run gs := by
  simp only [CryptoGames.SM.transmitQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

private theorem simulateQ_fig8GameImpl_challQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg)
      (CryptoGames.SM.challQuery (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q m₀ m₁ rc)).run gs =
      (CryptoGames.SM.challImpl fig 3 (qep + 1) cfg (Q, m₀, m₁, rc)).run gs := by
  simp only [CryptoGames.SM.challQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

private theorem simulateQ_fig8GameImpl_deliverQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg)
      (CryptoGames.SM.deliverQuery (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q c)).run gs =
      (CryptoGames.SM.deliverImpl fig cfg (Q, c)).run gs := by
  simp only [CryptoGames.SM.deliverQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

private theorem simulateQ_fig8GameImpl_injectQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg)
      (CryptoGames.SM.injectQuery (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q c)).run gs =
      (CryptoGames.SM.injectImpl fig 3 (qep + 1) cfg (Q, c)).run gs := by
  simp only [CryptoGames.SM.injectQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

private theorem simulateQ_fig8GameImpl_corrQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg)
      (CryptoGames.SM.corrQuery (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q)).run gs =
      (CryptoGames.SM.corrImpl Q).run gs := by
  simp only [CryptoGames.SM.corrQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

abbrev SimImpl (PQ PQC Pt : Type) (ℓ : ℕ) :=
  QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)
    (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ))

def simFig8ClampOf {PQ PQC Pt : Type} {ℓ : ℕ} (P : Params PQ PQC) (O : SimImpl PQ PQC Pt ℓ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    CryptoGames.SM.Adversary (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt) :=
  show Fig8Comp Pt ℓ Bool from do
    let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
    let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    (simulateQ O A).run' sC₀

theorem simFig8ClampTG_eq_clampOf {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    simFig8ClampTG P ℓ Dh encPt encT decT lam qep B B_skip? A =
      simFig8ClampOf P (simFig8OracleTG P Dh encPt encT decT lam qep B B_skip?) A := rfl

theorem simFig8ClampSan_eq_clampOf {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A =
      simFig8ClampOf P (simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk) A := rfl

theorem simFig8ClampTGDedup_eq_clampTG {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    simFig8ClampOf P (simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip?) A =
      simFig8ClampTG P ℓ Dh encPt encT decT lam qep B B_skip? A := by
  unfold simFig8ClampOf simFig8ClampTG
  refine bind_congr fun pqrKey => ?_
  exact run'_simulateQ_simFig8OracleTGDedup_eq P Dh encPt encT decT lam qep B B_skip? A _

private theorem simulateQ_fig8GameImpl_eq_of_inv {PQ PQC Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (O₁ O₂ : SimImpl PQ PQC Pt ℓ)
    (hinl₁ : ∀ n, O₁ (.inl n) = StateT.lift (query (spec := unifSpec +
      CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (.inl n)))
    (hinl₂ : ∀ n, O₂ (.inl n) = StateT.lift (query (spec := unifSpec +
      CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (.inl n)))
    (Inv : ℕ → LibsignalToModularSchemeSimState PQ Pt ℓ → Fig8G Pt ℓ → Prop)
    (hstepEq : ∀ (m : ℕ) (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
      (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ), Inv (m + 1) sC gs →
      (simulateQ (fig8GameImpl fig qep cfg) ((O₁ (.inr t)).run sC)).run gs =
        (simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inr t)).run sC)).run gs)
    (hstepInv : ∀ (m : ℕ) (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
      (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ), Inv (m + 1) sC gs →
      ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inr t)).run sC)).run gs),
        Inv m x.1.2 x.2)
    {α : Type}
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes) α)
    (m : ℕ) (hq : oa.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) (hInv : Inv m sC gs) :
    (simulateQ (fig8GameImpl fig qep cfg) ((simulateQ O₁ oa).run sC)).run gs =
      (simulateQ (fig8GameImpl fig qep cfg) ((simulateQ O₂ oa).run sC)).run gs := by
  induction oa using OracleComp.inductionOn generalizing m sC gs with
  | pure a => rfl
  | query_bind q mx ih =>
    have hq' := (isQueryBoundP_query_bind_iff _ q mx m).mp hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rcases q with n | t
    · have hqu : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m :=
        fun u => by simpa [isGameQuery] using hq'.2 u
      rw [hinl₁ n, hinl₂ n, simulateQ_fig8GameImpl_inl]
      simp only [bind_assoc, pure_bind]
      exact bind_congr fun u => ih u m (hqu u) sC gs hInv
    · have hm_pos : 0 < m := by simpa [isGameQuery] using hq'.1
      rcases m with _ | m'
      · omega
      have hqu : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m' :=
        fun u => by simpa [isGameQuery] using hq'.2 u
      rw [hstepEq m' t sC gs hInv]
      exact bind_congr_of_forall_mem_support _ fun x hx =>
        ih x.1.1 m' (hqu x.1.1) x.1.2 x.2 (hstepInv m' t sC gs hInv x hx)

theorem sm_run_simFig8ClampOf_eq_of_inv {PQ PQC Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    (O₁ O₂ : SimImpl PQ PQC Pt ℓ)
    (hinl₁ : ∀ n, O₁ (.inl n) = StateT.lift (query (spec := unifSpec +
      CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (.inl n)))
    (hinl₂ : ∀ n, O₂ (.inl n) = StateT.lift (query (spec := unifSpec +
      CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (.inl n)))
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (Inv : ℕ → LibsignalToModularSchemeSimState PQ Pt ℓ → Fig8G Pt ℓ → Prop)
    (hinit : ∀ (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256),
      Inv q (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
        (CryptoGames.SM.initState fig k b))
    (hstepEq : ∀ (m : ℕ) (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
      (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ), Inv (m + 1) sC gs →
      (simulateQ (fig8GameImpl fig qep cfg) ((O₁ (.inr t)).run sC)).run gs =
        (simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inr t)).run sC)).run gs)
    (hstepInv : ∀ (m : ℕ) (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
      (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ), Inv (m + 1) sC gs →
      ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inr t)).run sC)).run gs),
        Inv m x.1.2 x.2) :
    CryptoGames.SM.run fig 3 (qep + 1) cfg b (simFig8ClampOf P O₁ A) =
      CryptoGames.SM.run fig 3 (qep + 1) cfg b (simFig8ClampOf P O₂ A) := by
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  unfold CryptoGames.SM.run simFig8ClampOf
  refine bind_congr fun k => ?_
  change (simulateQ (fig8GameImpl fig qep cfg) _).run (CryptoGames.SM.initState fig k b) =
    (simulateQ (fig8GameImpl fig qep cfg) _).run (CryptoGames.SM.initState fig k b)
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_fig8GameImpl_liftProb, bind_assoc,
    pure_bind, StateT.run'_eq, simulateQ_map, StateT.run_map]
  refine bind_congr fun pqrKey => congrArg (Functor.map (Prod.map Prod.fst id)) ?_
  exact simulateQ_fig8GameImpl_eq_of_inv fig qep cfg O₁ O₂ hinl₁ hinl₂ Inv hstepEq hstepInv
    A q hq' _ _ (hinit k pqrKey)

end GameCouplingInfra

/-! ## Party, `Kept`, and sanitizer identities -/

section PartyAndKeptInv

def Fig8CkaInv {Pt : Type} (st : Fig8St Pt) : Prop :=
  if st.id.sendsIn (st.tcur + 1) then ∃ h, st.γ = .pub h else ∃ x, st.γ = .exp x

def SkippedLenLe (B0 : ℕ) (v : RatchetReceiverState (BitVec 256) (BitVec 256)) : Prop :=
  v.skippedKeys.length ≤ B0

theorem SkippedLenLe.mono {B0 B0' : ℕ} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hle : B0 ≤ B0') (hv : SkippedLenLe B0 v) : SkippedLenLe B0' v :=
  Nat.le_trans hv hle

def Fig8PartyInv {Pt : Type} (B0 : ℕ) (st : Fig8St Pt) : Prop :=
  Fig8CkaInv st ∧ ∀ t v, st.vR t = some v → SkippedLenLe B0 v

theorem Fig8PartyInv.mono {Pt : Type} {B0 B0' : ℕ} {st : Fig8St Pt}
    (hle : B0 ≤ B0') (hst : Fig8PartyInv B0 st) : Fig8PartyInv B0' st :=
  ⟨hst.1, fun t v hv => (hst.2 t v hv).mono hle⟩

def KeptInv {Pt : Type} (B0 : ℕ) (k : Kept Pt) : Prop :=
  (∀ st, k.full = some st → Fig8PartyInv B0 st) ∧
  (∀ t v, k.rs t = some v → SkippedLenLe B0 v)

theorem KeptInv.mono {Pt : Type} {B0 B0' : ℕ} {k : Kept Pt}
    (hle : B0 ≤ B0') (hk : KeptInv B0 k) : KeptInv B0' k :=
  ⟨fun st hst => (hk.1 st hst).mono hle, fun t v hv => (hk.2 t v hv).mono hle⟩

private theorem sendsIn_succ_eq_not (p : Party) (t : ℕ) :
    p.sendsIn (t + 1) = !(p.sendsIn t) := by
  by_cases h : t % 2 = 1
  · have h1 : (t + 1) % 2 = 0 := by omega
    cases p <;> simp only [Party.sendsIn, h, h1] <;> rfl
  · have h0 : t % 2 = 0 := by omega
    have h1 : (t + 1) % 2 = 1 := by omega
    cases p <;> simp only [Party.sendsIn, h0, h1] <;> rfl

private theorem skipKeys_length_local {CK MK : Type}
    (G : _) (n : ℕ) (w : CK) (p : ℕ) (acc : List (ℕ × MK)) :
    (skipKeys G n w p acc).2.length = acc.length + n := by
  induction n generalizing w p acc with
  | zero => simp only [skipKeys, Nat.add_zero]
  | succ n ih => simp only [skipKeys, ih, List.length_cons]; omega

private theorem skippedLenLe_of_lFS_receive {Pt : Type} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {B0 : ℕ}
    {v v' : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {a : Header Pt} {c : ℕ × LibsignalCiphertextWithSalt32}
    {i : ℕ} {m : LibsignalMsgPublicPart × Plain ℓ}
    (hv : SkippedLenLe B0 v)
    (hrec : (lFS C codec ℓ encT idOf 25000).receive v a c = some (v', i, m)) :
    SkippedLenLe (B0 + 25000) v' := by
  rcases c with ⟨idx, wsc⟩
  dsimp only [lFS, fromAEADPRG, CryptoGames.AEADScheme.movePubPartToAD] at hrec
  rcases hlk : v.skippedKeys.lookup idx with _ | key
  · rw [hlk] at hrec
    split_ifs at hrec with hbad
    have hnot : ¬ idx ≤ v.lastIndex ∧ ¬ 25000 < idx - v.lastIndex - 1 := not_or.mp hbad
    rcases hpub : lPubOf codec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec
      dsimp only at hrec
      rcases hdec : (lAead C codec ℓ encT idOf).dec
          ((lChainPRG C.F (idx - 1)).gen
            (skipKeys (lChainPRG C.F) (idx - v.lastIndex - 1)
              v.chainKey v.lastIndex v.skippedKeys).1).2
          ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl⟩
        unfold SkippedLenLe at hv ⊢
        dsimp only
        rw [skipKeys_length_local]
        omega
  · rw [hlk] at hrec
    dsimp only at hrec
    rcases hpub : lPubOf codec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec
      dsimp only at hrec
      rcases hdec : (lAead C codec ℓ encT idOf).dec key ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl⟩
        unfold SkippedLenLe at hv ⊢
        exact Nat.le_trans (List.length_filter_le _ _) (by omega)

private theorem fig8PartyInv_init {Pt : Type} [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (R : Party) (k : BitVec 256 × BitVec 256) :
    Fig8PartyInv 0
      (initParty (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf 25000)
        lam R k) := by
  refine ⟨?_, ?_⟩
  · cases R <;> simp [Fig8CkaInv, initParty, Party.sendsIn, dhScheme]
  · intro t v hv
    cases R
    · simp only [initParty] at hv
      split_ifs at hv with ht
      · simp only [Option.some.injEq] at hv; subst hv
        simp [SkippedLenLe, lFS, fromAEADPRG]
    · simp [initParty] at hv

private theorem fig8PartyInv_send {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {st : Fig8St Pt} (hst : Fig8PartyInv B0 st)
    (m : LibsignalMsgPublicPart × Plain ℓ) (r : BitVec 256) :
    Fig8PartyInv B0
      ((lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send st m r).1 := by
  rcases hst with ⟨hcka, hvr⟩
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.send]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · unfold Fig8CkaInv at hcka
    simp only [hs, ↓reduceIte] at hcka
    rcases hcka with ⟨h, hγ⟩
    simp only [hs, ↓reduceIte, hγ, dhScheme]
    have hs2 : st.id.sendsIn (st.tcur + 1 + 1) = false := by
      rw [sendsIn_succ_eq_not, hs]; rfl
    exact ⟨by simp [Fig8CkaInv, hs2], hvr⟩
  · have hs0 : st.id.sendsIn (st.tcur + 1) = false := Bool.eq_false_iff.mpr hs
    simp only [hs0, Bool.false_eq_true, ↓reduceIte]
    cases st.vS <;> exact ⟨hcka, hvr⟩

private theorem fig8PartyInv_receive {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {st st' : Fig8St Pt} {c : Fig8C Pt} {t i : ℕ}
    {m : LibsignalMsgPublicPart × Plain ℓ}
    (hst : Fig8PartyInv B0 st)
    (hrec : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive st c =
      some (st', t, i, m)) :
    Fig8PartyInv (B0 + 25000) st' := by
  rcases hst with ⟨hcka, hvr⟩
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.receive] at hrec
  by_cases hbad : (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) = true
  · simp [hbad] at hrec
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hrec
    have hbad' : st.id.sendsIn c.1.1 = false ∧ ¬ st.tcur + 1 < c.1.1 := by
      simpa [Bool.or_eq_true] using hbad
    by_cases heq : c.1.1 = st.tcur + 1
    · simp only [heq, ↓reduceIte] at hrec
      rcases hc2 : c.1.2 with _ | Tn
      · rw [hc2] at hrec; cases hrec
      · rw [hc2] at hrec
        unfold Fig8CkaInv at hcka
        have hs0 : st.id.sendsIn (st.tcur + 1) = false := by rw [← heq]; exact hbad'.1
        simp only [hs0, Bool.false_eq_true, ↓reduceIte] at hcka
        rcases hcka with ⟨x, hγ⟩
        simp only [hγ, dhScheme, Function.update_self] at hrec
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive
            ((lFS C codec ℓ encT idOf 25000).initReceiver
              ((rootPRNG C.F encPt).up st.root (Dh.dh x Tn)).2)
            c.1 c.2 with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          have hs2 : st.id.sendsIn (st.tcur + 1 + 1) = true := by
            rw [sendsIn_succ_eq_not, hs0]; rfl
          refine ⟨by simp [Fig8CkaInv, hs2], ?_⟩
          intro t' v0 hv0
          dsimp only at hv0
          by_cases ht' : t' = st.tcur + 1
          · subst ht'
            simp only [Function.update_self, Option.some.injEq] at hv0; subst hv0
            have hinit : SkippedLenLe B0
                ((lFS C codec ℓ encT idOf 25000).initReceiver
                  ((rootPRNG C.F encPt).up st.root (Dh.dh x Tn)).2) := by
              simp [SkippedLenLe, lFS, fromAEADPRG]
            exact skippedLenLe_of_lFS_receive hinit hfs
          · simp only [Function.update_of_ne ht'] at hv0
            exact (hvr t' v0 hv0).mono (by omega)
    · simp only [heq, ↓reduceIte] at hrec
      rcases hvt : st.vR c.1.1 with _ | v
      · rw [hvt] at hrec; cases hrec
      · rw [hvt] at hrec
        dsimp only at hrec
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive v c.1 c.2
            with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨hcka, ?_⟩
          intro t' v0 hv0
          dsimp only at hv0
          by_cases ht' : t' = c.1.1
          · subst ht'
            simp only [Function.update_self, Option.some.injEq] at hv0; subst hv0
            exact skippedLenLe_of_lFS_receive (hvr c.1.1 v hvt) hfs
          · simp only [Function.update_of_ne ht'] at hv0
            exact (hvr t' v0 hv0).mono (by omega)

private theorem keptInv_unknown {Pt : Type} (B0 : ℕ) : KeptInv B0 (Kept.unknown (Pt := Pt)) :=
  ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

private theorem keptInv_ofSt {Pt : Type} {B0 : ℕ} {st : Fig8St Pt} (hst : Fig8PartyInv B0 st) :
    KeptInv B0 (Kept.ofSt st) :=
  ⟨fun _ h => Option.some.inj h ▸ hst, hst.2⟩

private theorem keptInv_send {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {k : Kept Pt} (hk : KeptInv B0 k) :
    KeptInv B0
      (Kept.send (ℓ := ℓ) (fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) k) := by
  unfold Kept.send
  rcases hfull : k.full with _ | st
  · exact hk
  · dsimp only
    have hst := hk.1 st hfull
    split_ifs with hs
    · exact ⟨fun _ h => (nomatch h), hst.2⟩
    · exact ⟨fun _ h => Option.some.inj h ▸ fig8PartyInv_send hst _ _, hk.2⟩

private theorem keptInv_recv {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {c : Fig8C Pt} {k : Kept Pt} (hk : KeptInv B0 k) :
    KeptInv (B0 + 25000)
      (Kept.recv (fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam)
        (fs := lFS C codec ℓ encT idOf 25000) c k) := by
  unfold Kept.recv
  rcases hfull : k.full with _ | st
  · dsimp only
    refine ⟨fun _ h => (nomatch h), ?_⟩
    intro t' v0 hv0
    dsimp only at hv0
    by_cases ht' : t' = c.1.1
    · subst ht'
      simp only [Function.update_self] at hv0
      rcases hrs : k.rs c.1.1 with _ | v
      · simp [hrs] at hv0
      · rw [hrs] at hv0
        dsimp only [Option.bind] at hv0
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive v c.1 c.2
            with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hv0; cases hv0
        · simp only [hfs, Option.map_some, Option.some.injEq] at hv0; subst hv0
          exact skippedLenLe_of_lFS_receive (hk.2 c.1.1 v hrs) hfs
    · simp only [Function.update_of_ne ht'] at hv0
      exact (hk.2 t' v0 hv0).mono (by omega)
  · dsimp only
    have hst := hk.1 st hfull
    rcases hrec : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive st c
        with _ | ⟨st', t, i, pm⟩
    · dsimp only
      exact ⟨fun _ h => (nomatch h), fun t' v hv => (hst.2 t' v hv).mono (by omega)⟩
    · dsimp only
      exact ⟨fun _ h => Option.some.inj h ▸ fig8PartyInv_receive hst hrec,
        fun t' v hv => (hk.2 t' v hv).mono (by omega)⟩

private theorem sanRS_eq_self {B0 T : ℕ} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hle : B0 ≤ T) (hv : SkippedLenLe B0 v) : sanRS T v = v := by
  cases v
  simp only [sanRS, List.take_of_length_le (Nat.le_trans hv hle)]

private theorem sanRS_nil (T : ℕ) (ck : BitVec 256) (idx : ℕ) :
    sanRS T ⟨ck, idx, []⟩ = ⟨ck, idx, []⟩ := by
  simp [sanRS]

private theorem sanGamma_eq_self {Pt : Type} [Zero Pt] (lam : Pt) {st : Fig8St Pt}
    (hcka : Fig8CkaInv st) : sanGamma lam st = st.γ := by
  unfold Fig8CkaInv at hcka
  unfold sanGamma
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp only [hs, ↓reduceIte] at hcka ⊢
    rcases hcka with ⟨h, hγ⟩; simp [hγ]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hcka ⊢
    rcases hcka with ⟨x, hγ⟩; simp [hγ]

private theorem sanAt_eq_self {Pt : Type} [Zero Pt] {B0 T : ℕ} (lam : Pt) (t : ℕ) {st : Fig8St Pt}
    (hle : B0 ≤ T) (hst : Fig8PartyInv B0 st) : sanAt T lam t st = st := by
  have hγ := sanGamma_eq_self lam hst.1
  have hvR : (fun j => if j = t then (st.vR t).map (sanRS T) else st.vR j) = st.vR := by
    funext j
    split_ifs with hj
    · subst hj
      rcases hv : st.vR j with _ | v
      · rfl
      · simp [sanRS_eq_self hle (hst.2 j v hv)]
    · rfl
  cases st
  dsimp only [sanAt] at hvR hγ ⊢
  rw [hvR, hγ]


private theorem fig8San_receive_eq {Pt Key M Coins : Type} [Zero Pt] {B0 T : ℕ} (lam : Pt)
    (fig : CryptoGames.SMScheme Key (Fig8St Pt) M Coins (Fig8C Pt))
    {st : Fig8St Pt} (hle : B0 ≤ T) (hst : Fig8PartyInv B0 st) (c : Fig8C Pt) :
    (fig8San T lam fig).receive st c = fig.receive st c := by
  simp only [fig8San, sanAt_eq_self lam c.1.1 hle hst]

private theorem fsSan_receive_eq {SS AD M C : Type} {B0 T : ℕ}
    (fs : CryptoGames.FSAEADScheme (BitVec 256) SS
      (RatchetReceiverState (BitVec 256) (BitVec 256)) AD M C)
    {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hle : B0 ≤ T) (hv : SkippedLenLe B0 v) (h : AD) (c : C) :
    (fsSan T fs).receive v h c = fs.receive v h c := by
  simp only [fsSan, sanRS_eq_self hle hv]

private theorem kept_recv_congr_of_inv {Pt : Type} {ℓ B0 : ℕ}
    {fig₁ fig₂ : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {fs₁ fs₂ : CryptoGames.FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (hfig : ∀ st c, Fig8PartyInv B0 st → fig₁.receive st c = fig₂.receive st c)
    (hfs : ∀ v h c, SkippedLenLe B0 v → fs₁.receive v h c = fs₂.receive v h c)
    (c : Fig8C Pt) {k : Kept Pt} (hk : KeptInv B0 k) :
    Kept.recv (ℓ := ℓ) (fig := fig₁) (fs := fs₁) c k =
      Kept.recv (ℓ := ℓ) (fig := fig₂) (fs := fs₂) c k := by
  unfold Kept.recv
  rcases hfull : k.full with _ | st
  · dsimp only
    congr 1; funext j
    by_cases hj : j = c.1.1
    · subst hj
      simp only [Function.update_self]
      rcases hrs : k.rs c.1.1 with _ | v
      · rfl
      · simp only [Option.bind_some, hfs v c.1 c.2 (hk.2 c.1.1 v hrs)]
    · simp only [Function.update_of_ne hj]
  · dsimp only
    rw [hfig st c (hk.1 st hfull)]

private theorem kept_eval_congr_of_inv {Pt : Type} {ℓ B0 : ℕ}
    {fig₁ fig₂ : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {fs₁ fs₂ : CryptoGames.FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (hfig : ∀ st c, Fig8PartyInv B0 st → fig₁.receive st c = fig₂.receive st c)
    (hfs : ∀ v h c, SkippedLenLe B0 v → fs₁.receive v h c = fs₂.receive v h c)
    (c : Fig8C Pt) {k : Kept Pt} (hk : KeptInv B0 k) :
    Kept.eval (ℓ := ℓ) (fig := fig₁) (fs := fs₁) c k =
      Kept.eval (ℓ := ℓ) (fig := fig₂) (fs := fs₂) c k := by
  unfold Kept.eval
  rcases hfull : k.full with _ | st
  · dsimp only
    rcases hrs : k.rs c.1.1 with _ | v
    · rfl
    · simp only [Option.map_some, hfs v c.1 c.2 (hk.2 c.1.1 v hrs)]
  · dsimp only
    rw [hfig st c (hk.1 st hfull)]

private theorem sentEval_congr_of_nil {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {fs₁ fs₂ : CryptoGames.FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (hfs : ∀ ck idx h c, fs₁.receive ⟨ck, idx, []⟩ h c = fs₂.receive ⟨ck, idx, []⟩ h c)
    (sent : List (Fig8C Pt × RatchetSenderState (BitVec 256))) (c c' : Fig8C Pt) :
    sentEval (ℓ := ℓ) (fs := fs₁) sent c c' =
      sentEval (ℓ := ℓ) (fs := fs₂) sent c c' := by
  unfold sentEval
  congr 1; funext e
  rw [hfs e.2.chainKey e.2.lastIndex c'.1 c'.2]

private theorem kept_recv_figS_eq {PQ PQC Pt : Type} [Zero Pt] {ℓ B0 T : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (hle : B0 ≤ T) (c : Fig8C Pt) {k : Kept Pt} (hk : KeptInv B0 k) :
    Kept.recv (ℓ := ℓ) (fig := figS (ℓ := ℓ) P Dh encPt encT lam T)
        (fs := fsS (ℓ := ℓ) P encT T) c k =
      Kept.recv (ℓ := ℓ)
        (fig := lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
        (fs := lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000) c k :=
  kept_recv_congr_of_inv
    (fun _ c₀ hst => fig8San_receive_eq lam _ hle hst c₀)
    (fun _ h₀ c₀ hv => fsSan_receive_eq _ hle hv h₀ c₀)
    c hk

private theorem predictReceive_fig8Clamp_figS_eq {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ B B0 T : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (hle : B0 ≤ T) {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {Q : Party}
    (hk : KeptInv B0 (sC.kept Q)) (c c' : Fig8C Pt) :
    predictReceive (fig := fig8Clamp B (figS (ℓ := ℓ) P Dh encPt encT lam T))
        (fs := fsClampSim B (fsS (ℓ := ℓ) P encT T)) sC Q c c' =
      predictReceive
        (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000)) sC Q c c' := by
  unfold predictReceive
  have hke :
      Kept.eval (fig := fig8Clamp B (figS (ℓ := ℓ) P Dh encPt encT lam T))
        (fs := fsClampSim B (fsS (ℓ := ℓ) P encT T)) c' (sC.kept Q) =
      Kept.eval
        (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000)) c' (sC.kept Q) :=
    kept_eval_congr_of_inv
      (fun st c₀ hst => by
        dsimp only [fig8Clamp, figS]
        rw [fig8San_receive_eq lam _ hle hst c₀])
      (fun v h₀ c₀ hv => by
        dsimp only [fsClampSim, fsS]
        rw [fsSan_receive_eq _ hle hv h₀ c₀])
      c' hk
  rw [hke]
  rcases Kept.eval
      (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
      (fs := fsClampSim B (lFS P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000)) c' (sC.kept Q) with _ | r
  · exact sentEval_congr_of_nil
      (fun ck idx h₀ c₀ => by
        simp only [fsClampSim, fsS, fsSan, sanRS_nil])
      sC.sent c c'
  · rfl

private theorem lFig8_send_vS_and_idx {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {Bvs : ℕ} {st : Fig8St Pt}
    (hvs : ∀ vs, st.vS = some vs → vs.lastIndex ≤ Bvs)
    (m : LibsignalMsgPublicPart × Plain ℓ) (r : BitVec 256) :
    let out := (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send st m r
    (∀ vs', out.1.vS = some vs' → vs'.lastIndex ≤ Bvs + 1) ∧ out.2.2.1 ≤ Bvs + 1 := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.send,
    lFS, fromAEADPRG]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp only [hs, ↓reduceIte]
    refine ⟨?_, by omega⟩
    intro vs' hvs'
    simp only [Option.some.injEq] at hvs'
    subst hvs'
    dsimp only
    omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    rcases hst : st.vS with _ | v
    · simp only [hst]
      refine ⟨(fun _ h => by cases h), ?_⟩
      change 0 ≤ Bvs + 1
      omega
    · have hvle := hvs v hst
      refine ⟨?_, ?_⟩
      · intro vs' hvs'
        simp only [Option.some.injEq] at hvs'
        subst hvs'
        dsimp only
        omega
      · dsimp only
        omega

private theorem lFS_receive_idx_eq {Pt : Type} {C : Crypto} {codec : SignalMessageProtoCodec}
    {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {v v' : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {a : Header Pt} {c : ℕ × LibsignalCiphertextWithSalt32}
    {i : ℕ} {m : LibsignalMsgPublicPart × Plain ℓ}
    (hrec : (lFS C codec ℓ encT idOf 25000).receive v a c = some (v', i, m)) :
    i = c.1 := by
  rcases c with ⟨idx, wsc⟩
  dsimp only [lFS, fromAEADPRG, CryptoGames.AEADScheme.movePubPartToAD] at hrec
  rcases hlk : v.skippedKeys.lookup idx with _ | key
  · rw [hlk] at hrec
    split_ifs at hrec
    rcases hpub : lPubOf codec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec; dsimp only at hrec
      rcases hdec : (lAead C codec ℓ encT idOf).dec _ ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        exact hrec.2.1.symm
  · rw [hlk] at hrec; dsimp only at hrec
    rcases hpub : lPubOf codec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec; dsimp only at hrec
      rcases hdec : (lAead C codec ℓ encT idOf).dec key ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        exact hrec.2.1.symm

private theorem lFig8_receive_vS_and_idx {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {st st' : Fig8St Pt} {c : Fig8C Pt} {t i : ℕ}
    {m : LibsignalMsgPublicPart × Plain ℓ}
    (hrec : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive st c =
      some (st', t, i, m)) :
    st'.vS = st.vS ∧ i = c.2.1 := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.receive] at hrec
  by_cases hbad : (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) = true
  · simp [hbad] at hrec
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hrec
    by_cases heq : c.1.1 = st.tcur + 1
    · simp only [heq, ↓reduceIte] at hrec
      rcases hc2 : c.1.2 with _ | Tn
      · rw [hc2] at hrec; cases hrec
      · rw [hc2] at hrec; dsimp only at hrec
        simp only [Function.update_self] at hrec
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive _ c.1 c.2 with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, lFS_receive_idx_eq hfs⟩
    · simp only [heq, ↓reduceIte] at hrec
      rcases hvt : st.vR c.1.1 with _ | v
      · rw [hvt] at hrec; cases hrec
      · rw [hvt] at hrec; dsimp only at hrec
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive v c.1 c.2 with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, lFS_receive_idx_eq hfs⟩

private structure GamePartyInv {Pt : Type} {ℓ : ℕ} (q m : ℕ) (gs : Fig8G Pt ℓ) : Prop where
  hm : m ≤ q
  hparty : ∀ R : Party, Fig8PartyInv (25000 * (q - m)) (gs.st R)
  hvs : ∀ R : Party, ∀ vs, (gs.st R).vS = some vs → vs.lastIndex ≤ q - m

private theorem GamePartyInv.mono {Pt : Type} {ℓ q m₁ m₂ : ℕ} {gs : Fig8G Pt ℓ}
    (hle : m₁ ≤ m₂) (h : GamePartyInv q m₂ gs) : GamePartyInv q m₁ gs where
  hm := Nat.le_trans hle h.hm
  hparty R := (h.hparty R).mono (Nat.mul_le_mul_left 25000 (by omega))
  hvs R vs hv := Nat.le_trans (h.hvs R vs hv) (by omega)

private theorem gamePartyInv_init {Pt : Type} [Zero Pt] {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto)
    (codec : SignalMessageProtoCodec) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (q : ℕ) (k : BitVec 256 × BitVec 256) (b : Bool) :
    GamePartyInv (Pt := Pt) (ℓ := ℓ) q q
      (CryptoGames.SM.initState (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) k b) where
  hm := le_rfl
  hparty R := by
    simp only [Nat.sub_self, Nat.mul_zero, CryptoGames.SM.initState]
    cases R <;> exact fig8PartyInv_init Dh encPt C codec ℓ encT idOf lam _ k
  hvs R vs hv := by
    simp only [Nat.sub_self]
    dsimp only [CryptoGames.SM.initState, lFig8, CryptoGames.SM.Construction.scheme,
      initParty, lFS, fromAEADPRG] at hv
    cases R
    · cases hv
    · simp only [Option.some.injEq] at hv
      subst hv
      rfl

private theorem epMgmt_st_eq {St Msg C : Type}
    {gs s₁ : GameState St Msg C} {Δ qep : ℕ} {Q : Party} {bad : Bool}
    (h : gs.epMgmt Δ qep Q bad = some s₁) : s₁.st = gs.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> injection h with h <;> subst h <;> rfl

private theorem stateT_liftProb_run {σ α : Type} (p : ProbComp α) (s : σ) :
    (liftM p : StateT σ ProbComp α).run s = (p >>= fun a => pure (a, s)) := rfl

private theorem gamePartyInv_record {Pt : Type} [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m qep : ℕ} {gs s₁ : Fig8G Pt ℓ} {Q : Party} {bad isChall : Bool}
    (msg : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256)
    (hInv : GamePartyInv q (m + 1) gs)
    (hep : gs.epMgmt 3 (qep + 1) Q bad = some s₁) :
    let out := (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send (s₁.st Q) msg coins
    GamePartyInv q m
      (s₁.record 3 Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, msg, out.2⟩ isChall) ∧
      out.2.2.1 ≤ q - m := by
  have hst := epMgmt_st_eq hep
  have hm1 : m + 1 ≤ q := hInv.hm
  have hInv0 := hInv.mono (Nat.le_succ m)
  have hsub : (q - (m + 1)) + 1 = q - m := by omega
  have hvsQ : ∀ vs, (s₁.st Q).vS = some vs → vs.lastIndex ≤ q - (m + 1) := hst ▸ hInv.hvs Q
  have hsend := lFig8_send_vS_and_idx (Dh := Dh) (encPt := encPt) (C := C) (codec := codec)
    (ℓ := ℓ) (encT := encT) (idOf := idOf) (lam := lam) hvsQ msg coins
  refine ⟨⟨hInv0.hm, fun R => ?_, fun R vs hv => ?_⟩, hsend.2.trans_eq hsub⟩
  · dsimp only [GameState.record]
    by_cases hR : R = Q
    · subst hR
      simp only [Function.update_self]
      have hpQ : Fig8PartyInv (25000 * (q - (m + 1))) (s₁.st R) := hst ▸ hInv.hparty R
      exact (fig8PartyInv_send hpQ msg coins).mono (Nat.mul_le_mul_left 25000 (by omega))
    · simp only [Function.update_of_ne hR, hst]; exact hInv0.hparty R
  · dsimp only [GameState.record] at hv
    by_cases hR : R = Q
    · subst hR
      simp only [Function.update_self] at hv
      exact (hsend.1 vs hv).trans_eq hsub
    · simp only [Function.update_of_ne hR, hst] at hv; exact hInv0.hvs R vs hv

private theorem gamePartyInv_accept {Pt : Type} [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m : ℕ} {gs : Fig8G Pt ℓ} {Q : Party} {c : Fig8C Pt}
    {st' : Fig8St Pt} {t i : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (pos : CryptoGames.SM.Pos)
    (hInv : GamePartyInv q (m + 1) gs)
    (hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c =
      some (st', t, i, pm)) :
    GamePartyInv q m (gs.accept Q st' pos) ∧ i = c.2.1 := by
  have hm1 : m + 1 ≤ q := hInv.hm
  have hInv0 := hInv.mono (Nat.le_succ m)
  obtain ⟨hvS_eq, hi_eq⟩ := lFig8_receive_vS_and_idx hrcv
  refine ⟨⟨hInv0.hm, fun R => ?_, fun R vs hv => ?_⟩, hi_eq⟩
  · dsimp only [GameState.accept, GameState.delete]
    by_cases hR : R = Q
    · subst hR
      simp only [Function.update_self]
      exact (fig8PartyInv_receive (hInv.hparty R) hrcv).mono (by omega)
    · simp only [Function.update_of_ne hR]; exact hInv0.hparty R
  · dsimp only [GameState.accept, GameState.delete] at hv
    by_cases hR : R = Q
    · subst hR
      simp only [Function.update_self, hvS_eq] at hv
      exact hInv0.hvs R vs hv
    · simp only [Function.update_of_ne hR] at hv
      exact hInv0.hvs R vs hv

private theorem gamePartyInv_transmitImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m qep : ℕ} {gs gs' : Fig8G Pt ℓ}
    {Q : Party} {msg : LibsignalMsgPublicPart × Plain ℓ} {rc : Option (BitVec 256)}
    {res : Option (Fig8C Pt)}
    (hInv : GamePartyInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.transmitImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) 3 (qep + 1) (Q, msg, rc)).run gs)) :
    GamePartyInv q m gs' ∧ ∀ c, res = some c → c.2.1 ≤ q - m := by
  unfold CryptoGames.SM.transmitImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftProb_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;>
      simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    · rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
    · rcases hmem with ⟨rfl, rfl⟩
      have hrec := gamePartyInv_record (Dh := Dh) (encPt := encPt) (C := C) (codec := codec)
        (encT := encT) (idOf := idOf) (lam := lam) (isChall := false) msg coins hInv hep
      exact ⟨hrec.1, fun _ hc => Option.some.inj hc ▸ hrec.2⟩

private theorem gamePartyInv_challImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m qep : ℕ}
    {cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : Fig8G Pt ℓ}
    {Q : Party} {m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ} {rc : Option (BitVec 256)}
    {res : Option (Fig8C Pt)}
    (hInv : GamePartyInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.challImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) 3 (qep + 1) cfg (Q, m₀, m₁, rc)).run gs)) :
    GamePartyInv q m gs' ∧ ∀ c, res = some c → c.2.1 ≤ q - m := by
  unfold CryptoGames.SM.challImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftProb_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;> simp only [hep] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
    · by_cases hch : (!(s₁.safeCh 3 Q) || !(cfg.challAllowedIn (s₁.epoch Q))) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        have hrec := gamePartyInv_record (Dh := Dh) (encPt := encPt) (C := C) (codec := codec)
          (encT := encT) (idOf := idOf) (lam := lam) (isChall := true)
          ((cfg.challMsg (s₁.epoch Q)).getD (if gs.b then m₁ else m₀)) coins hInv hep
        exact ⟨hrec.1, fun _ hc => Option.some.inj hc ▸ hrec.2⟩

private theorem gamePartyInv_deliverImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m : ℕ}
    {cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : Fig8G Pt ℓ} {Q : Party} {c : Fig8C Pt}
    {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (hInv : GamePartyInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.deliverImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) cfg (Q, c)).run gs)) :
    GamePartyInv q m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → i = c.2.1 := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold CryptoGames.SM.deliverImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      at hmem
    rcases htr : gs.inTransit Q.other c with _ | r <;> simp only [htr] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
    · rcases hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
        _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
      · split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          rcases hmem with ⟨rfl, rfl⟩ <;>
          exact ⟨⟨hInv0.hm, hInv0.hparty, hInv0.hvs⟩, fun _ _ _ hc => nomatch hc⟩
      · obtain ⟨hacc, hi_eq⟩ := gamePartyInv_accept r.pos hInv hrcv
        split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          rcases hmem with ⟨rfl, rfl⟩ <;>
          exact ⟨⟨hacc.hm, hacc.hparty, hacc.hvs⟩, fun _ _ _ hc => by
            injection hc with hc; injection hc with _ hi _; exact hi.symm.trans hi_eq⟩

private theorem gamePartyInv_injectImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m qep : ℕ}
    {cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : Fig8G Pt ℓ} {Q : Party} {c : Fig8C Pt}
    {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (hInv : GamePartyInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.injectImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) 3 qep cfg (Q, c)).run gs)) :
    GamePartyInv q m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → i = c.2.1 := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold CryptoGames.SM.injectImpl at hmem
  by_cases href : (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3)) = true
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      at hmem
    rcases hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
      _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
    · by_cases hcap : qep + 1 < t'
      · simp only [hcap, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
      · simp only [hcap, ↓reduceIte] at hmem
        by_cases htriv : gs.trivial 3 ⟨Q.other, t', i'⟩ = true
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          obtain ⟨hacc, hi_eq⟩ := gamePartyInv_accept ⟨Q.other, t', i'⟩ hInv hrcv
          exact ⟨hacc, fun _ _ _ hc => by
            injection hc with hc; injection hc with _ hi _; exact hi.symm.trans hi_eq⟩
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
            rcases hmem with ⟨rfl, rfl⟩ <;>
            exact ⟨⟨hInv0.hm, hInv0.hparty, hInv0.hvs⟩, fun _ _ _ hc => nomatch hc⟩

private theorem gamePartyInv_corrImpl {Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {q m : ℕ}
    {gs gs' : Fig8G Pt ℓ} {Q : Party} {res : Option (Fig8St Pt)}
    (hInv : GamePartyInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.corrImpl Q).run gs)) :
    GamePartyInv q m gs' ∧ ∀ fig8st, res = some fig8st → fig8st = gs.st Q := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold CryptoGames.SM.corrImpl at hmem
  by_cases href : (gs.win || !(gs.corrAllowed Q)) = true
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv0, fun _ hc => nomatch hc⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    have hst : (gs.afterCorr Q).st = gs.st := rfl
    exact ⟨⟨hInv0.hm, fun R => hst ▸ hInv0.hparty R, fun R => hst ▸ hInv0.hvs R⟩,
      fun _ hc => (Option.some.inj hc).symm⟩

end PartyAndKeptInv

/-! ## Pointwise hook equalities -/

section PointwiseHooks

theorem chainSeedAtB_eq_of_le (K : ℕ) (F : ShaCompress) (ck : ChainKey) (counter : BitVec 32)
    (hK : counter.toNat ≤ K) :
    chainSeedAtB K F ck counter = chainSeedAt F ck counter := by
  unfold chainSeedAtB
  have hnot : ¬ K < counter.toNat - ck.index.toNat := by omega
  simp [hnot]

theorem snapshotMessageKeySeedB_eq_of_tryFrom {PQ PQC : Type} (K : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : Bytes)
    {msg : SignalMessage} (htry : SignalMessage.tryFrom P.codec w = .ok msg)
    (hK : msg.counter.toNat ≤ K) :
    snapshotMessageKeySeedB K P snaps Q t w = snapshotMessageKeySeed P snaps Q t w := by
  have hcs : ∀ ck, chainSeedAtB K P.C.F ck msg.counter = chainSeedAt P.C.F ck msg.counter :=
    fun ck => chainSeedAtB_eq_of_le K P.C.F ck msg.counter hK
  have horElse : ∀ {α : Type} {a₁ a₂ b₁ b₂ : Option α},
      a₁ = a₂ → b₁ = b₂ → (a₁ <|> b₁) = (a₂ <|> b₂) := by
    intro _ _ _ _ _ ha hb; rw [ha, hb]
  have hite : ∀ {α : Type} {p : Prop} (i₁ i₂ : Decidable p) {a₁ a₂ b₁ b₂ : α},
      a₁ = a₂ → b₁ = b₂ → @ite α p i₁ a₁ b₁ = @ite α p i₂ a₂ b₂ := by
    intro _ _ i₁ i₂ _ _ _ _ ha hb; cases Subsingleton.elim i₁ i₂; rw [ha, hb]
  unfold snapshotMessageKeySeedB snapshotMessageKeySeed
  rw [htry]
  dsimp only
  simp only [hcs]
  refine horElse ?_ (horElse ?_ (horElse ?_ ?_))
  · exact congrArg (snaps.findSome? ·) (funext fun _ => hite _ _ rfl rfl)
  · exact congrArg (snaps.findSome? ·) (funext fun e =>
      hite _ _ (congrArg (e.2.2.session.senderChain.bind ·)
        (funext fun _ => hite _ _ rfl rfl)) rfl)
  · exact congrArg (snaps.findSome? ·) (funext fun _ => hite _ _ rfl rfl)
  · exact congrArg₂ Option.bind
      (congrArg (snaps.findSome? ·) (funext fun e_cur =>
        hite _ _ (congrArg (e_cur.2.2.session.senderChain.bind ·)
          (funext fun _ => hite _ _ rfl rfl)) rfl))
      (funext fun _ => congrArg (snaps.findSome? ·)
        (funext fun _ => hite _ _ rfl rfl))

theorem simParseRecvC_tryFrom_and_idx {PQ PQC Pt : Type} (P : Params PQ PQC)
    (decT : PublicKey → Option Pt) (Q : Party) (pq pq' : PQ) (w : Bytes)
    (i : ℕ) (pk : PublicKey) (T? : Option Pt)
    (lct : ℕ × LibsignalCiphertextWithSalt32)
    (hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) pq w = some (pq', (i, (pk, (T?, lct))))) :
    ∃ msg : SignalMessage,
      SignalMessage.tryFrom P.codec w = .ok msg ∧
        i = msg.counter.toNat + 1 ∧ lct.1 = i ∧ i ≤ 2 ^ 32 := by
  unfold simParseRecvC at hp
  by_cases hlen : w.length < 9
  · simp [hlen] at hp
  · simp only [hlen, ↓reduceIte] at hp
    rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, body⟩
    · simp [hparse] at hp
    · simp only [hparse] at hp
      split_ifs at hp
      rcases hspqr : P.spqr.recv pq h.pqRatchet with _ | ⟨pq₁, salt⟩
      · simp [hspqr] at hp
      · simp only [hspqr, Option.some.injEq, Prod.mk.injEq] at hp
        rcases hp with ⟨_, hi, _, _, hlct⟩
        have hlt : h.counter.toNat < 2 ^ 32 := h.counter.isLt
        have hmin : min (h.counter.toNat + 1) (2 ^ 32) = h.counter.toNat + 1 := by omega
        refine ⟨_, tryFrom_of_parse P.codec w h body hlen hparse, ?_, ?_, ?_⟩
        · dsimp only
          omega
        · rw [← hlct, ← hi, hmin]
        · omega

theorem evalCKS_eq_evalCKClamp {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ B0 T K B : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : Bytes)
    (c c' : SimFig8C Pt) {msg : SignalMessage}
    (hT : B0 ≤ T) (hk : KeptInv B0 (sC.kept Q))
    (htry : SignalMessage.tryFrom P.codec w = .ok msg) (hK : msg.counter.toNat ≤ K) :
    evalCKS P Dh encPt encT lam T K B sC Q w c c' =
      evalCKClamp P Dh encPt encT lam B sC Q w c c' := by
  unfold evalCKS evalCKClamp
  rw [predictReceive_fig8Clamp_figS_eq P Dh encPt encT lam hT hk c c',
    snapshotMessageKeySeedB_eq_of_tryFrom K P sC.snaps Q c.1.1 w htry hK]

theorem semFwdAnswerHookS_eq {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ B0 T : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hT : B0 ≤ T) (hk : KeptInv B0 (sC.kept Q)) :
    semFwdAnswerHookS P Dh encPt encT lam T sh qep sC ex Q w isDel ci? Tpk pq' c' =
      semFwdAnswerHook P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c' := by
  unfold semFwdAnswerHookS semFwdAnswerHook
  refine bind_congr fun ⟨res, _⟩ => ?_
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · rfl
  · rfl
  · simp only [kept_recv_figS_eq P Dh encPt encT lam hT c' hk]

theorem semResyncHookS_eq {PQ PQC Pt : Type} [Zero Pt] {ℓ B0 T : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hT : B0 ≤ T) (hk : KeptInv B0 (sC.kept Q)) :
    semResyncHookS P Dh encPt encT lam T sh qep sC ex Q w ci? Tpk pq' c r =
      semResyncHook P Dh encPt encT lam sh qep sC ex Q w ci? Tpk pq' c r := by
  unfold semResyncHookS semResyncHook
  rcases r with _ | ⟨t, i, _, m'⟩
  · rfl
  · refine bind_congr fun ⟨res, _⟩ => ?_
    rcases res with _ | (_ | ⟨t', i', pm'⟩)
    · rfl
    · rfl
    · simp only [kept_recv_figS_eq P Dh encPt encT lam hT c hk]

theorem semFwdEvictHookS_eq {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ B0 T : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hT : B0 ≤ T) (hk : KeptInv B0 (sC.kept Q)) :
    semFwdEvictHookS P Dh encPt encT lam T sh qep sC ex Q w isDel Tpk pq' c' =
      semFwdEvictHook P Dh encPt encT lam sh qep sC ex Q w isDel Tpk pq' c' := by
  unfold semFwdEvictHookS semFwdEvictHook
  split_ifs
  · rfl
  · exact semFwdAnswerHookS_eq P Dh encPt encT lam sh qep sC ex Q w isDel none Tpk pq' c' hT hk

theorem semFwdHookS_eq {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ B0 T K B : ℕ}
    {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    {msg : SignalMessage}
    (hT : B0 ≤ T) (hk : KeptInv B0 (sC.kept Q))
    (htry : SignalMessage.tryFrom P.codec w = .ok msg) (hK : msg.counter.toNat ≤ K) :
    semFwdHookS P Dh encPt encT lam T K sh qep B sC ex Q w isDel ci? Tpk pq' honestC c' =
      semFwdHook P Dh encPt encT lam sh qep B sC ex Q w isDel ci? Tpk pq' honestC c' := by
  unfold semFwdHookS semFwdHook
  rcases honestC with _ | c
  · exact semFwdAnswerHookS_eq P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c' hT hk
  · dsimp only
    split_ifs
    · rw [evalCKS_eq_evalCKClamp P Dh encPt encT lam sC Q w c c' hT hk htry hK]
      rcases evalCKClamp P Dh encPt encT lam B sC Q w c c' with _ | r
      · rfl
      · exact semResyncHookS_eq P Dh encPt encT lam sh qep sC ex Q w ci? Tpk pq' c r hT hk
    · exact semFwdAnswerHookS_eq P Dh encPt encT lam sh qep sC ex Q w isDel ci? Tpk pq' c' hT hk

private theorem getD_mem_of_findIdx?_eq_some {α : Type} {p : α → Bool} {cs : List α}
    {ci : ℕ} (d : α) (h : cs.findIdx? p = some ci) : cs.getD ci d ∈ cs := by
  induction cs generalizing ci with
  | nil => simp at h
  | cons a xs ih =>
    rw [List.findIdx?_cons] at h
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [List.getD]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      simp only [List.getD, List.getElem?_cons_succ]
      exact List.mem_cons_of_mem a (ih hj)

private theorem rejects_false_le {g : GhostChain} {i : ℕ} (h : g.rejects i = false) :
    i ≤ g.last + 25001 ∧ i - 1 ≤ g.last + 25000 := by
  unfold GhostChain.rejects at h
  by_cases hle : i ≤ g.last
  · omega
  · simp only [hle, ↓reduceIte, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    omega

theorem semRecvHookS_eq_semRecvHook {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ B0 T K B : ℕ} {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (hT : B0 ≤ T) (hk : KeptInv B0 (sC.kept Q))
    (hK0 : 25000 ≤ K) (hchains : ∀ g ∈ sC.base.chains Q, g.last + 25000 ≤ K) :
    semRecvHookS P Dh encPt encT decT lam T K sh qep B sC ex Q w isDel =
      semRecvHook P Dh encPt encT decT lam sh qep B sC ex Q w isDel := by
  unfold semRecvHookS semRecvHook
  by_cases href :
      (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) ||
          !(CryptoGames.Ratchet.LibsignalInst.ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    rcases hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩
    · rfl
    · obtain ⟨msg, htry, hi, _, _⟩ :=
        simParseRecvC_tryFrom_and_idx P decT Q (sC.base.pq Q) pq' w i pk T? lct hp
      dsimp only
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · by_cases hc1 :
            ((((sC.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
             (((sC.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte]
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte]
          · simp only [hz, Bool.false_eq_true, ↓reduceIte]
            by_cases hc2 :
                (CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
                  decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte]
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
              have hnot : ¬ 25000 < i - 1 := fun hlt => hc2 (by simp [hlt])
              have hcnt : msg.counter.toNat ≤ K := by omega
              rcases T? with _ | T₀
              · rfl
              · dsimp only
                by_cases hev_b :
                    ((((sC.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte]
                  exact semFwdEvictHookS_eq P Dh encPt encT lam sh qep _ ex Q w isDel pk pq' _ hT hk
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte]
                  exact semFwdHookS_eq P Dh encPt encT lam sh qep _ ex Q w isDel none pk pq' _ _
                    hT hk htry hcnt
      · by_cases hrej :
            ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte]
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
          have hrej0 :
              ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = false :=
            Bool.eq_false_iff.mpr hrej
          have hgmem := getD_mem_of_findIdx?_eq_some ⟨none, 0, 0, []⟩ hidx
          have hgl := hchains _ hgmem
          have hle := (rejects_false_le hrej0).2
          have hcnt : msg.counter.toNat ≤ K := by omega
          exact semFwdHookS_eq P Dh encPt encT lam sh qep sC ex Q w isDel (some ci) pk pq' _ _
            hT hk htry hcnt

theorem semHandleHookDedupS_inl_eq {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ B0 T K B_skip B : ℕ} {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (t₀ : (((Party × Plain ℓ × Option PQC →ₒ Option Bytes) +
      (Party × Plain ℓ × Plain ℓ × Option PQC →ₒ Option Bytes) +
      (Party × Bytes →ₒ Option (RecvResult (Plain ℓ)))) +
      (Party × Bytes →ₒ Option (RecvResult (Plain ℓ)))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (hT : B0 ≤ T) (hk : ∀ R, KeptInv B0 (sC.kept R))
    (hK0 : 25000 ≤ K) (hchains : ∀ R, ∀ g ∈ sC.base.chains R, g.last + 25000 ≤ K) :
    semHandleHookDedupS P Dh encPt encT decT lam T K B_skip sh qep B (.inl t₀) sC ex =
      semHandleHookDedup P Dh encPt encT decT lam sh qep B (.inl t₀) sC ex := by
  rcases t₀ with (((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩)
  · rfl
  · rfl
  · dsimp only [semHandleHookDedupS, semHandleHookDedup]
    rw [semRecvHookS_eq_semRecvHook P Dh encPt encT decT lam sh qep sC ex Q w true
      hT (hk Q) hK0 (hchains Q)]
  · dsimp only [semHandleHookDedupS, semHandleHookDedup]
    exact semRecvHookS_eq_semRecvHook P Dh encPt encT decT lam sh qep sC ex Q w false
      hT (hk Q) hK0 (hchains Q)

theorem semCorrHookTGB_idHook_eq_semCorrHookTGDedup {PQ PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (Bsk : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    Prod.map id Prod.fst <$>
        semCorrHookTGB P Dh encT (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) Bsk sC () Q =
      semCorrHookTGDedup P Dh encT (some Bsk) sC Q := by
  unfold semCorrHookTGB semCorrHookTGDedup
  by_cases href :
      (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
       CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
       !CryptoGames.SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
  · simp [href, Prod.map]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    dsimp only [fig8IdSemHook]
    rw [map_bind, bind_assoc]
    refine bind_congr fun res => ?_
    rw [pure_bind]
    rcases res with _ | fig8st
    · simp [Prod.map]
    · dsimp only [Option.map, SimFig8LoopAndCost.fig8StTruncSkOpt]
      rw [map_pure]
      rfl

end PointwiseHooks

/-! ## Joint coupling invariant -/

section JointCoupling

private theorem find?_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (h : xs.find? p = some x) : x ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons a ys ih =>
    rw [List.find?_cons] at h
    cases hp : p a <;> simp only [hp] at h
    · exact List.mem_cons_of_mem a (ih h)
    · simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self ..

theorem evalCKClamp_index_le {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ B : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : Bytes)
    (c c' : SimFig8C Pt) {t_r i_r : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (hev : evalCKClamp P Dh encPt encT lam B sC Q w c c' = some (some (t_r, i_r, pm))) :
    i_r ≤ c'.2.1 := by
  unfold evalCKClamp at hev
  dsimp only at hev
  rcases hpr : predictReceive
      (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
      (fs := fsClampSim B (lFS P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000)) sC Q c c' with _ | r₀
  · rw [hpr] at hev
    change (snapshotMessageKeySeed P sC.snaps Q c.1.1 w).map
      (simKDecryptFig8 P ℓ B (partyEnc Q) w c') = some (some (t_r, i_r, pm)) at hev
    rw [Option.map_eq_some_iff] at hev
    obtain ⟨seed, -, hkdec⟩ := hev
    unfold simKDecryptFig8 at hkdec
    dsimp only at hkdec
    split at hkdec
    · simp only [Option.some.injEq, Prod.mk.injEq] at hkdec
      rcases hkdec with ⟨_, rfl, _⟩
      exact Nat.min_le_left _ _
    · cases hkdec
  · rw [hpr] at hev
    change some r₀ = some (some (t_r, i_r, pm)) at hev
    injection hev with hr₀
    subst hr₀
    unfold predictReceive at hpr
    rcases hke : Kept.eval
        (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000)) c' (sC.kept Q) with _ | r₁
    · rw [hke] at hpr
      unfold sentEval at hpr
      rw [Option.map_eq_some_iff] at hpr
      obtain ⟨e, -, hfs⟩ := hpr
      rw [Option.map_eq_some_iff] at hfs
      obtain ⟨⟨v', i₁, pm₁⟩, hrec, hEq⟩ := hfs
      dsimp only [fsClampSim] at hrec
      rw [Option.map_eq_some_iff] at hrec
      obtain ⟨⟨v₀, i₀, pm₀⟩, hfs₀, hEq₀⟩ := hrec
      have hi₀ := lFS_receive_idx_eq hfs₀
      simp only [Prod.mk.injEq] at hEq₀ hEq
      rcases hEq₀ with ⟨_, hi₁, _⟩
      rcases hEq with ⟨_, hir, _⟩
      omega
    · rw [hke] at hpr
      injection hpr with hr₁
      subst hr₁
      unfold Kept.eval at hke
      rcases hfull : (sC.kept Q).full with _ | st <;> rw [hfull] at hke
      · dsimp only at hke
        rw [Option.map_eq_some_iff] at hke
        obtain ⟨v, -, hfs⟩ := hke
        rw [Option.map_eq_some_iff] at hfs
        obtain ⟨⟨v', i₁, pm₁⟩, hrec, hEq⟩ := hfs
        dsimp only [fsClampSim] at hrec
        rw [Option.map_eq_some_iff] at hrec
        obtain ⟨⟨v₀, i₀, pm₀⟩, hfs₀, hEq₀⟩ := hrec
        have hi₀ := lFS_receive_idx_eq hfs₀
        simp only [Prod.mk.injEq] at hEq₀ hEq
        rcases hEq₀ with ⟨_, hi₁, _⟩
        rcases hEq with ⟨_, hir, _⟩
        omega
      · dsimp only at hke
        simp only [Option.some.injEq, Option.map_eq_some_iff] at hke
        obtain ⟨⟨st', t₁, i₁, pm₁⟩, hrec, hEq⟩ := hke
        dsimp only [fig8Clamp] at hrec
        rw [Option.map_eq_some_iff] at hrec
        obtain ⟨⟨st₀, t₀, i₀, pm₀⟩, hfig₀, hEq₀⟩ := hrec
        have hi₀ := (lFig8_receive_vS_and_idx hfig₀).2
        simp only [Prod.mk.injEq] at hEq₀ hEq
        rcases hEq₀ with ⟨_, _, hi₁, _⟩
        rcases hEq with ⟨_, hir, _⟩
        omega

private structure SanInv {PQ Pt : Type} {ℓ : ℕ} (q m : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) : Prop where
  hgame : GamePartyInv q m gs
  hkept : ∀ R : Party, KeptInv (25000 * (q - m)) (sC.kept R)
  hchains : ∀ R : Party, ∀ g ∈ sC.base.chains R, g.last ≤ 25001 * (q - m)
  hhonest : ∀ wc ∈ sC.base.honest, wc.2.2.1 ≤ q - m

private theorem SanInv.mono {PQ Pt : Type} {ℓ q m₁ m₂ : ℕ}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {gs : Fig8G Pt ℓ}
    (hle : m₁ ≤ m₂) (h : SanInv q m₂ sC gs) : SanInv q m₁ sC gs where
  hgame := h.hgame.mono hle
  hkept R := (h.hkept R).mono (Nat.mul_le_mul_left 25000 (by omega))
  hchains R g hg := Nat.le_trans (h.hchains R g hg) (Nat.mul_le_mul_left 25001 (by omega))
  hhonest wc hwc := Nat.le_trans (h.hhonest wc hwc) (by omega)

private theorem sanInv_init {PQ PQC Pt : Type} [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (q : ℕ)
    (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256) (b : Bool) :
    SanInv (PQ := PQ) (Pt := Pt) (ℓ := ℓ) q q
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (CryptoGames.SM.initState
        (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam) k b) where
  hgame := gamePartyInv_init Dh encPt P.C P.codec encT
    (fun R => if R == Party.A then P.idA else P.idB) lam q k b
  hkept R := by
    simp only [Nat.sub_self, Nat.mul_zero, initSimC]
    exact keptInv_unknown 0
  hchains R g hg := by
    cases R <;> simp [initSimC, initSim] at hg ⊢
    subst hg; rfl
  hhonest _ hwc := nomatch hwc

private theorem ghostChain_accept_last_le {g : GhostChain} {i M : ℕ}
    (hg : g.last ≤ M) (hi : i ≤ M) : (g.accept i).last ≤ M := by
  unfold GhostChain.accept
  split_ifs
  · exact hi
  · exact hg

private theorem pushChain_last_le {cs : List GhostChain} {g₀ : GhostChain} {M : ℕ}
    (hcs : ∀ g ∈ cs, g.last ≤ M) (hg₀ : g₀.last ≤ M) :
    ∀ g ∈ pushChain cs g₀, g.last ≤ M := by
  intro g hgm
  have hmem := List.mem_of_mem_drop hgm
  rw [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | rfl
  · exact hcs g hmem
  · exact hg₀

private theorem onAcceptPure_last_le {PQ Pt : Type} {ℓ M : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, ∀ g ∈ s.chains R, g.last ≤ M) (hi : i ≤ M) :
    ∀ R, ∀ g ∈ (onAcceptPure qep Q w isDel t i m ci? Tpk pq' s).2.chains R, g.last ≤ M := by
  let cs' : List GhostChain := match ci? with
    | some ci => (s.chains Q).modify ci (·.accept i)
    | none => pushChain (s.chains Q)
        (GhostChain.accept { key := some Tpk, epoch := t, last := 0, skipped := [] } i)
  have hcs : ∀ g ∈ cs', g.last ≤ M := by
    rcases ci? with _ | ci
    · exact pushChain_last_le (hs Q) (ghostChain_accept_last_le (Nat.zero_le M) hi)
    · exact modify_mem_inv (hs Q) (fun _ hg => ghostChain_accept_last_le hg hi)
  have hu : ∀ R, ∀ g ∈ Function.update s.chains Q cs' R, g.last ≤ M := by
    intro R
    by_cases hR : R = Q
    · subst hR; simpa using hcs
    · simpa [Function.update_of_ne hR] using hs R
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact hs
    · exact hu
    · exact hs
  · simp only [↓reduceIte]
    rcases s.mir.inTransit Q.other w with _ | r
    · exact hs
    · exact hu

private theorem onAnswerPure_last_le {PQ Pt : Type} {ℓ M : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, ∀ g ∈ s.chains R, g.last ≤ M)
    (hres : ∀ t i pm, res = some (.accepted t i pm) → i ≤ M) :
    ∀ R, ∀ g ∈ (onAnswerPure qep Q w isDel ci? Tpk pq' res s).2.chains R, g.last ≤ M := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact onAcceptPure_last_le qep Q w isDel t i ((pm.map (·.2)).getD default) ci? Tpk pq' s hs
      (hres t i pm rfl)

private theorem simulateQ_fig8GameImpl_semDrawSendCoins {PQC Pt α : Type} [DecidableEq Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (r : Option PQC) (k : PQC × Option (BitVec 256) → Fig8Comp Pt ℓ α)
    (gs : Fig8G Pt ℓ) {x : α × Fig8G Pt ℓ}
    (hx : x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
      (semDrawSendCoins (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) r >>= k)).run gs)) :
    ∃ rq rc, x ∈ support ((simulateQ (fig8GameImpl fig qep cfg) (k (rq, rc))).run gs) := by
  cases r with
  | none =>
    dsimp only [semDrawSendCoins, fig8IdSemHook] at hx
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_liftProb, mem_support_bind_iff] at hx
    obtain ⟨rq, -, hx⟩ := hx
    exact ⟨rq, none, hx⟩
  | some rq =>
    dsimp only [semDrawSendCoins, fig8IdSemHook] at hx
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_liftProb, mem_support_bind_iff] at hx
    obtain ⟨rc, -, hx⟩ := hx
    exact ⟨rq, some rc, hx⟩

private theorem semSendHook_sanInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ q m qep : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hInv : SanInv q (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semSendHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q m₀ chal r)).run gs),
      SanInv q m x.1.2.1 x.2 := by
  intro fig ⟨⟨out₁, sC₁, ex₁⟩, gs₁⟩ hx
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semSendHook at hx
  by_cases href :
      (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;>
      simp only [hep] at hx
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
    · by_cases hch : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp only [hch, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hx
        obtain ⟨rq, rc, hx⟩ := simulateQ_fig8GameImpl_semDrawSendCoins fig qep cfg r _ gs hx
        dsimp only [fig8IdSemHook] at hx
        rw [pure_bind] at hx
        rcases hmk : CryptoGames.Ratchet.LibsignalSim.mkPub P sC.base Q rq
            (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
              BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;>
          simp only [hmk] at hx
        · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · have hpost : ∀ (c : Fig8C Pt),
              GamePartyInv q m gs₁ → c.2.1 ≤ q - m →
              sC₁ = scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq'
                (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
                  BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) c →
              SanInv q m sC₁ gs₁ := by
            intro c hg' hc hsC₁
            subst hsC₁
            refine ⟨hg', ?_, hInv0.hchains, ?_⟩
            · intro R
              unfold scPostSendPure
              by_cases hR : R = Q
              · subst hR
                simp only [Function.update_self]
                exact (keptInv_send (hInv.hkept R)).mono
                  (Nat.mul_le_mul_left 25000 (by omega))
              · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
            · intro wc hwc
              unfold scPostSendPure at hwc
              rw [List.mem_cons] at hwc
              rcases hwc with rfl | hwc
              · exact hc
              · exact hInv0.hhonest wc hwc
          cases chal with
          | none =>
            dsimp only [fig8IdSemHook] at hx
            simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
              simulateQ_fig8GameImpl_transmitQuery, mem_support_bind_iff] at hx
            obtain ⟨⟨res, gs'⟩, htr, hEq⟩ := hx
            obtain ⟨hg', hc⟩ := gamePartyInv_transmitImpl hInv.hgame htr
            rcases res with _ | c <;>
              simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hEq
            · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩
              exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
            · rcases hEq with ⟨⟨_, hsC₁, _⟩, rfl⟩
              exact hpost c hg' (hc c rfl) hsC₁
          | some m₁ =>
            dsimp only [fig8IdSemHook] at hx
            simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
              simulateQ_fig8GameImpl_challQuery, mem_support_bind_iff] at hx
            obtain ⟨⟨res, gs'⟩, hch, hEq⟩ := hx
            obtain ⟨hg', hc⟩ := gamePartyInv_challImpl hInv.hgame hch
            rcases res with _ | c <;>
              simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hEq
            · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩
              exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
            · rcases hEq with ⟨⟨_, hsC₁, _⟩, rfl⟩
              exact hpost c hg' (hc c rfl) hsC₁

private theorem semFwdAnswerHook_sanInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ q m qep : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs : Fig8G Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (hg : GamePartyInv q (m + 1) gs)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m)
    (hc' : c'.2.1 ≤ 25001 * (q - m)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semFwdAnswerHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none)
          qep sC' () Q w isDel ci? Tpk pq' c')).run gs),
      SanInv q m x.1.2.1 x.2 := by
  intro fig ⟨⟨rr₁, sC₁, ex₁⟩, gs₁⟩ hx
  have hm1 : m + 1 ≤ q := hg.hm
  have hsubK : 25000 * (q - (m + 1)) + 25000 = 25000 * (q - m) := by omega
  unfold semFwdAnswerHook at hx
  dsimp only at hx
  have hfin : ∀ (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))),
      GamePartyInv q m gs₁ → (∀ t i pm, res = some (.accepted t i pm) → i = c'.2.1) →
      sC₁ = { (match res with
         | some (.accepted _ _ _) =>
           { sC' with kept := Function.update sC'.kept Q (Kept.recv (fig := fig)
               (fs := lFS P.C P.codec ℓ encT
                 (fun R => if R == Party.A then P.idA else P.idB) 25000)
               c' (sC'.kept Q)) }
         | _ => sC') with base := (onAnswerPure qep Q w isDel ci? Tpk pq' res sC'.base).2 } →
      SanInv q m sC₁ gs₁ := by
    intro res hg' hi_eq hsC₁
    subst hsC₁
    have hhon_oa : ∀ wc ∈ (onAnswerPure qep Q w isDel ci? Tpk pq' res sC'.base).2.honest,
        wc.2.2.1 ≤ q - m := by
      rcases res with _ | (_ | ⟨t, i, pm⟩)
      · exact hhon'
      · exact hhon'
      · dsimp only [onAnswerPure, onAcceptPure]
        cases isDel
        · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> exact hhon'
        · simp only [↓reduceIte]
          rcases sC'.base.mir.inTransit Q.other w with _ | _ <;> exact hhon'
    refine ⟨hg', ?_, onAnswerPure_last_le qep Q w isDel ci? Tpk pq' res sC'.base hch'
      (fun t i pm hr => (hi_eq t i pm hr) ▸ hc'), hhon_oa⟩
    rcases res with _ | (_ | ⟨t, i, pm⟩)
    · exact fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
    · exact fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
    · intro R
      by_cases hR : R = Q
      · subst hR
        change KeptInv _ (Function.update sC'.kept R _ R)
        rw [Function.update_self]
        exact hsubK ▸ keptInv_recv (hk' R)
      · change KeptInv _ (Function.update sC'.kept Q _ R)
        rw [Function.update_of_ne hR]
        exact (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
  by_cases hinT :
      (sC'.base.honest.any fun wc =>
        decide (wc.2 = c') && (sC'.base.mir.inTransit Q.other wc.1).isSome) = true
  · simp only [hinT, ↓reduceIte] at hx
    dsimp only [fig8IdSemHook] at hx
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_deliverQuery, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨res, gs'⟩, hdl, ⟨_, hsC₁, _⟩, rfl⟩ := hx
    obtain ⟨hg', hi_eq⟩ := gamePartyInv_deliverImpl hg hdl
    exact hfin res hg' hi_eq hsC₁
  · simp only [hinT, Bool.false_eq_true, ↓reduceIte] at hx
    dsimp only [fig8IdSemHook] at hx
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_injectQuery, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨res, gs'⟩, hij, ⟨_, hsC₁, _⟩, rfl⟩ := hx
    obtain ⟨hg', hi_eq⟩ := gamePartyInv_injectImpl hg hij
    exact hfin res hg' hi_eq hsC₁

private theorem semResyncHook_sanInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ q m qep : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs : Fig8G Pt ℓ) (Q : Party) (w : Bytes)
    (hg : GamePartyInv q (m + 1) gs)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m)
    (hr_le : ∀ t_r i_r pm, r = some (t_r, i_r, pm) → i_r ≤ 25001 * (q - m)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semResyncHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none)
          qep sC' () Q w ci? Tpk pq' c r)).run gs),
      SanInv q m x.1.2.1 x.2 := by
  intro fig ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  have hm1 : m + 1 ≤ q := hg.hm
  have hsubK : 25000 * (q - (m + 1)) + 25000 = 25000 * (q - m) := by omega
  unfold semResyncHook at hx
  rcases r with _ | ⟨t_r, i_r, pub_r, m_r⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
    exact ⟨hg.mono (Nat.le_succ m),
      fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
  · dsimp only [fig8IdSemHook] at hx
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_deliverQuery, mem_support_bind_iff] at hx
    obtain ⟨⟨res, gs'⟩, hdl, hx⟩ := hx
    obtain ⟨hg', -⟩ := gamePartyInv_deliverImpl hg hdl
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      exact ⟨hg', fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      exact ⟨hg', fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      have hhon_oa : ∀ wc ∈ (onAcceptPure qep Q w true t_r i_r m_r ci? Tpk pq' sC'.base).2.honest,
          wc.2.2.1 ≤ q - m := by
        dsimp only [onAcceptPure]
        rcases sC'.base.mir.inTransit Q.other w with _ | _ <;> exact hhon'
      refine ⟨hg', ?_,
        onAcceptPure_last_le qep Q w true t_r i_r m_r ci? Tpk pq' sC'.base hch'
          (hr_le t_r i_r (pub_r, m_r) rfl), hhon_oa⟩
      intro R; dsimp only
      by_cases hR : R = Q
      · subst hR; simp only [Function.update_self]
        exact hsubK ▸ keptInv_recv (hk' R)
      · simp only [Function.update_of_ne hR]
        exact (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))

private theorem semFwdHook_sanInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ q m qep B : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs : Fig8G Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (hg : GamePartyInv q (m + 1) gs)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (hc : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m)
    (hc' : c'.2.1 ≤ 25001 * (q - m)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semFwdHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none)
          qep B sC' () Q w isDel ci? Tpk pq' hc c')).run gs),
      SanInv q m x.1.2.1 x.2 := by
  intro fig x hx
  have hm1 : m + 1 ≤ q := hg.hm
  unfold semFwdHook at hx
  rcases hc with _ | c
  · exact semFwdAnswerHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hg
      sC' ci? Tpk pq' c' hk' hch' hhon' hc' x hx
  · dsimp only at hx
    split at hx
    · rcases hev : evalCKClamp P Dh encPt encT lam B sC' Q w c c' with _ | r <;>
        simp only [hev] at hx
      · rcases x with ⟨⟨_, sC₁, _⟩, gs₁⟩
        dsimp only [fig8IdSemHook] at hx
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
        exact ⟨hg.mono (Nat.le_succ m),
          fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
      · exact semResyncHook_sanInv P Dh encPt encT lam cfg gs Q w hg
          sC' ci? Tpk pq' c r hk' hch' hhon'
          (fun t_r i_r pm hr =>
            (evalCKClamp_index_le P Dh encPt encT lam sC' Q w c c' (hr ▸ hev)).trans hc') x hx
    · exact semFwdAnswerHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hg
        sC' ci? Tpk pq' c' hk' hch' hhon' hc' x hx

private theorem semRecvHook_sanInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ q m qep B : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (hInv : SanInv q (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w isDel)).run gs),
      SanInv q m x.1.2.1 x.2 := by
  rintro fig ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  have hm1 : m + 1 ≤ q := hInv.hgame.hm
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semRecvHook at hx
  by_cases href :
      (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) ||
          !(CryptoGames.Ratchet.LibsignalInst.ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hp] at hx
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
    · obtain ⟨_, -, _, hlct_i, _⟩ :=
        simParseRecvC_tryFrom_and_idx P decT Q (sC.base.pq Q) pq' w i pk T? lct hp
      let hcOpt : Option (SimFig8C Pt) :=
        Option.map (fun (wc : Bytes × SimFig8C Pt) => wc.2)
          (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      have hmkC : ∀ (t : ℕ) (T : Option Pt), i ≤ 25001 * (q - m) →
          (match hcOpt with
            | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
            | none => ((t, T), lct)).2.1 ≤ 25001 * (q - m) := by
        intro t T hi_le
        cases hhc : hcOpt with
        | none => dsimp only; omega
        | some c =>
          obtain ⟨wc, hfind, rfl⟩ := Option.map_eq_some_iff.mp hhc
          have hwc := hInv.hhonest wc (find?_mem hfind)
          dsimp only
          by_cases hct : wc.2.2.2.2 = lct.2.2 <;> simp only [hct, ↓reduceIte] <;> omega
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hsAmb_k : ∀ amb : Bool, ∀ R, KeptInv (25000 * (q - (m + 1)))
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }.kept R) :=
          fun amb => by cases amb <;> exact hInv.hkept
        have hsAmb_c : ∀ amb : Bool, ∀ R, ∀ g ∈
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }.base.chains R),
            g.last ≤ 25001 * (q - m) :=
          fun amb => by cases amb <;> exact hInv0.hchains
        have hsAmb_h : ∀ amb : Bool, ∀ wc ∈
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }.base.honest),
            wc.2.2.1 ≤ q - m :=
          fun amb => by cases amb <;> exact hInv0.hhonest
        by_cases hc1 :
            ((((sC.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
             (((sC.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
                  decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
              exact ⟨hInv0.hgame,
                fun R => (hsAmb_k _ R).mono (Nat.mul_le_mul_left 25000 (by omega)),
                hsAmb_c _, hsAmb_h _⟩
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              have hnot : ¬ 25000 < i - 1 := fun hlt => hc2 (by simp [hlt])
              have hi_le : i ≤ 25001 * (q - m) := by omega
              rcases hT : T? with _ | T₀ <;>
                simp only [hT] at hx
              · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hx
                rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
                exact ⟨hInv0.hgame,
                  fun R => (hsAmb_k _ R).mono (Nat.mul_le_mul_left 25000 (by omega)),
                  hsAmb_c _, hsAmb_h _⟩
              · by_cases hev_b :
                    ((((sC.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  unfold semFwdEvictHook at hx
                  have hsAmb_mir :
                      (if (CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
                            (Q == Party.A && (sC.base.chains Q).any fun x => x.key.isNone)) = true then
                        { sC.base with amb := sC.base.amb + 1 }
                      else sC.base).mir = sC.base.mir := by
                    split_ifs <;> rfl
                  rw [hsAmb_mir] at hx
                  by_cases hev2 : (isDel && !sC.base.mir.safeInj 3) = true
                  · simp only [hev2, ↓reduceIte] at hx
                    dsimp only [fig8IdSemHook] at hx
                    simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff, Prod.mk.injEq] at hx
                    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
                    exact ⟨hInv0.hgame,
                      fun R => (hsAmb_k _ R).mono (Nat.mul_le_mul_left 25000 (by omega)),
                      hsAmb_c _, hsAmb_h _⟩
                  · simp only [hev2, Bool.false_eq_true, ↓reduceIte] at hx
                    exact semFwdAnswerHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hInv.hgame
                      _ none pk pq' ((sC.base.mir.epoch Q + 1, some T₀), lct)
                      (hsAmb_k _) (hsAmb_c _) (hsAmb_h _)
                      (by dsimp only; omega) _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hInv.hgame
                    _ none pk pq' hcOpt _ (hsAmb_k _) (hsAmb_c _) (hsAmb_h _)
                    (hmkC (sC.base.mir.epoch Q + 1) (some T₀) hi_le) _ hx
      · by_cases hrej :
            ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          have hrej0 :
              ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = false :=
            Bool.eq_false_iff.mpr hrej
          have hgmem := getD_mem_of_findIdx?_eq_some ⟨none, 0, 0, []⟩ hidx
          have hgl := hInv.hchains Q _ hgmem
          have hle := (rejects_false_le hrej0).1
          have hi_le : i ≤ 25001 * (q - m) := by omega
          exact semFwdHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hInv.hgame
            sC (some ci) pk pq' hcOpt _ hInv.hkept hInv0.hchains hInv0.hhonest
            (hmkC (((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch) T? hi_le) _ hx

private theorem semCorrHookTGDedup_sanInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (B_skip? : Option ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) (Q : Party)
    (hInv : SanInv q (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semCorrHookTGDedup P Dh encT B_skip? sC Q)).run gs),
      SanInv q m x.1.2 x.2 := by
  intro fig ⟨⟨_, sC₁⟩, gs₁⟩ hx
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semCorrHookTGDedup at hx
  by_cases href :
      (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
       CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
       !CryptoGames.SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_corrQuery, mem_support_bind_iff] at hx
    obtain ⟨⟨res, gs'⟩, hcr, hx⟩ := hx
    obtain ⟨hg', hst_eq⟩ := gamePartyInv_corrImpl hInv.hgame hcr
    rcases res with _ | fig8st
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl⟩, rfl⟩
      exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl⟩, rfl⟩
      refine ⟨hg', ?_, ?_, hInv0.hhonest⟩
      · intro R; dsimp only
        by_cases hR : R = Q
        · subst hR; simp only [Function.update_self, hst_eq fig8st rfl]
          exact (keptInv_ofSt (hInv.hgame.hparty R)).mono
            (Nat.mul_le_mul_left 25000 (by omega))
        · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
      · intro R g hg; dsimp only at hg
        by_cases hB0 : (Q == Party.B && sC.base.mir.epoch Party.B == 0) = true <;>
          simp only [hB0, ↓reduceIte, Bool.false_eq_true] at hg
        · rcases hγ : fig8st.γ with _ | x <;> simp only [hγ] at hg
          · exact hInv0.hchains R g hg
          · by_cases hR : R = .A
            · subst hR; simp only [Function.update_self, List.mem_map] at hg
              obtain ⟨g₀, hg₀, rfl⟩ := hg
              split_ifs <;> exact hInv0.hchains .A g₀ hg₀
            · simp only [Function.update_of_ne hR] at hg
              exact hInv0.hchains R g hg
        · exact hInv0.hchains R g hg

private theorem simFig8OracleTGDedup_step_sanInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ q m qep B : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (B_skip? : Option ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (hInv : SanInv q (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        ((simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip? (.inr t)).run sC)).run gs),
      SanInv q m x.1.2 x.2 := by
  intro fig x hx
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · have hstep :
        (simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip?
          (.inr (.inl (.inl (.inl (.inl (Q, m₀, r))))))).run sC =
        Prod.map id Prod.fst <$>
          semSendHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep sC () Q m₀ none r := rfl
    rw [hstep, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semSendHook_sanInv P Dh encPt encT lam cfg sC gs Q m₀ none r hInv y hy
  · have hstep :
        (simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip?
          (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run sC =
        Prod.map id Prod.fst <$>
          semSendHook P Dh encPt encT lam (fig8IdSemHook (PQC := PQC) none) qep sC () Q m₀ (some m₁) r := rfl
    rw [hstep, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semSendHook_sanInv P Dh encPt encT lam cfg sC gs Q m₀ (some m₁) r hInv y hy
  · have hstep :
        (simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip?
          (.inr (.inl (.inl (.inr (Q, w)))))).run sC =
        Prod.map id Prod.fst <$>
          (semRecvHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B sC () Q w true >>=
            fun x => pure () >>= fun ex₂ => pure (x.1, x.2.1, ex₂)) := rfl
    rw [hstep] at hx
    simp only [pure_bind, map_bind, map_pure, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semRecvHook_sanInv P Dh encPt encT decT lam cfg sC gs Q w true hInv y hy
  · have hstep :
        (simFig8OracleTGDedup P Dh encPt encT decT lam qep B B_skip?
          (.inr (.inl (.inr (Q, w))))).run sC =
        Prod.map id Prod.fst <$>
          semRecvHook P Dh encPt encT decT lam (fig8IdSemHook (PQC := PQC) none) qep B sC () Q w false := rfl
    rw [hstep, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semRecvHook_sanInv P Dh encPt encT decT lam cfg sC gs Q w false hInv y hy
  · exact semCorrHookTGDedup_sanInv P Dh encPt encT lam B_skip? cfg sC gs Q hInv x hx

private theorem simFig8OracleSan_step_eq_tgDedup {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ q m qep B T Kc Bsk : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) {gs : Fig8G Pt ℓ}
    (hT : 25000 * q ≤ T) (hKc : 25001 * q ≤ Kc)
    (hInv : SanInv q (m + 1) sC gs) :
    (simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk (.inr t)).run sC =
      (simFig8OracleTGDedup P Dh encPt encT decT lam qep B (some Bsk) (.inr t)).run sC := by
  have hm1 : m + 1 ≤ q := hInv.hgame.hm
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · rfl
  · refine congrArg (Prod.map id Prod.fst <$> ·) (semHandleHookDedupS_inl_eq P Dh encPt encT decT lam
      (fig8IdSemHook (PQC := PQC) none) qep (.inl (.inr (Q, w))) sC () (by omega) hInv.hkept
      (by omega) fun R g hg => ?_)
    have hgl := hInv.hchains R g hg
    omega
  · refine congrArg (Prod.map id Prod.fst <$> ·) (semHandleHookDedupS_inl_eq P Dh encPt encT decT lam
      (fig8IdSemHook (PQC := PQC) none) qep (.inr (Q, w)) sC () (by omega) hInv.hkept
      (by omega) fun R g hg => ?_)
    have hgl := hInv.hchains R g hg
    omega
  · exact semCorrHookTGB_idHook_eq_semCorrHookTGDedup P Dh encT Bsk sC Q

end JointCoupling

/-! ## Game-level coupling and `SimFig8EvalOk` bridge -/

section GameCouplingAndBridge

theorem sm_run_simFig8ClampSan_eq_clampTG {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q ≤ Kc) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampTG P ℓ Dh encPt encT decT lam qep B (some Bsk) A) := by
  intro fig
  rw [simFig8ClampSan_eq_clampOf, ← simFig8ClampTGDedup_eq_clampTG]
  refine sm_run_simFig8ClampOf_eq_of_inv P fig qep cfg b _ _ (fun _ => rfl) (fun _ => rfl) hq
    (SanInv q) (fun k pqrKey => sanInv_init P Dh encPt encT lam q k pqrKey b) ?_ ?_
  · intro m t sC gs hInv
    rw [simFig8OracleSan_step_eq_tgDedup P Dh encPt encT decT lam t sC hT hKc hInv]
  · intro m t sC gs hInv
    exact simFig8OracleTGDedup_step_sanInv P Dh encPt encT decT lam (some Bsk) cfg t sC gs hInv

/-- Game-level `SM.run` equivalence between `simFig8ClampSan` and `simFig8ClampTG ... (some Bsk)`. -/
theorem sm_run_simFig8ClampSan_eq_tg {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hB : 2 ^ 32 ≤ B) (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampTG P ℓ Dh encPt encT decT lam qep B (some Bsk) A) := by
  let _ := hB
  exact sm_run_simFig8ClampSan_eq_clampTG P Dh encPt encT decT lam qep B T Kc Bsk cfg b hq
    (by omega) (by omega)

/-- Full `SM.run` equivalence between `simFig8ClampSan` and `Refine.libsignalToModularSchemeSim`. -/
theorem sm_run_simFig8ClampSan_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf
        lam qep A) := by
  intro fig
  have hid_eq : (fun R : Party => if R == Party.A then P.idA else P.idB) = idOf := funext hid
  have h1 := sm_run_simFig8ClampSan_eq_tg P Dh encPt encT decT lam qep B T Kc Bsk cfg b hq
    h232 hT hKc
  dsimp only at h1
  rw [hid_eq] at h1
  exact h1.trans (sm_run_simFig8ClampTG_eq P Dh encPt encT decT idOf hid lam qep B (some Bsk)
    cfg b hq h232 hqB (fun Bs h => by injection h with rfl; omega))

theorem sm_game_simFig8ClampSan_eq {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.game fig 3 (qep + 1) cfg
      (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) =
    CryptoGames.SM.game fig 3 (qep + 1) cfg
      (CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf
        lam qep A) := by
  unfold CryptoGames.SM.game
  refine bind_congr fun b => ?_
  dsimp only
  rw [sm_run_simFig8ClampSan_eq P Dh encPt encT decT idOf hid lam qep B T Kc Bsk cfg b
    hq h232 hqB hT hKc hBsk]

theorem simCNoneWinEvent_eq_sm_run_simFig8ClampSan {PQ PQC Pt : Type} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    CryptoGames.LibsignalSM.Proofs.Refinement.simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam
      qep A =
    (do
      let b ← $ᵗ Bool
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let (_, s) ← CryptoGames.SM.run fig 3 (qep + 1) CryptoGames.SM.Config.h1 b
        (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A)
      return s.win) := by
  unfold CryptoGames.LibsignalSM.Proofs.Refinement.simCNoneWinEvent
  refine bind_congr fun b => ?_
  dsimp only
  rw [sm_run_simFig8ClampSan_eq P Dh encPt encT decT idOf hid lam qep B T Kc Bsk
    CryptoGames.SM.Config.h1 b hq h232 hqB hT hKc hBsk]

private theorem paramsV1_idsOf_eq (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (R : Party) :
    (if R == Party.A then (paramsV1 C K idA idB).idA else (paramsV1 C K idA idB).idB) =
      idsOf idA idB R := by
  cases R <;> rfl

theorem simFig8ProgOfStep_evalOk_san' {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep q B T Kc Bsk : ℕ)
    (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep : ℓ < 10 ^ 6 → ∀ t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      SanSnapExtra C K (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk
        (.inr t)).run (simFullDec s_raw))) :
    SimFig8EvalOk Pt ℓ C K idA idB Dh encPt encT decT lam qep q
      (simFig8ProgOfStep C K Dh encPt encT decT lam step) where
  queries hℓ A hq := by
    rw [simFig8ProgOfStep_eval_san C K idA idB Dh encPt encT decT lam L qep B T Kc Bsk hℓ
      (SanSnapExtra C K) (sanSnapExtra_init C K idA idB)
      (sanSnapExtra_step C K idA idB Dh encPt encT decT lam qep B T Kc Bsk)
      step (hstep hℓ) A q hq hqL]
    exact simFig8ClampSan_queries (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk hq
  equalPub hℓ A hq := by
    rw [simFig8ProgOfStep_eval_san C K idA idB Dh encPt encT decT lam L qep B T Kc Bsk hℓ
      (SanSnapExtra C K) (sanSnapExtra_init C K idA idB)
      (sanSnapExtra_step C K idA idB Dh encPt encT decT lam qep B T Kc Bsk)
      step (hstep hℓ) A q hq hqL]
    exact simFig8ClampSan_equalPub (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk A
  sendShort hℓ A hq := by
    rw [simFig8ProgOfStep_eval_san C K idA idB Dh encPt encT decT lam L qep B T Kc Bsk hℓ
      (SanSnapExtra C K) (sanSnapExtra_init C K idA idB)
      (sanSnapExtra_step C K idA idB Dh encPt encT decT lam qep B T Kc Bsk)
      step (hstep hℓ) A q hq hqL]
    exact simFig8ClampSan_sendShort (paramsV1 C K idA idB)
      (lengthsOk_paramsIdsWithSpqr_v1 C K idA idB (by omega))
      Dh encPt encT decT lam qep B T Kc Bsk A
  sm_game_eq hℓ cfg A hq := by
    rw [simFig8ProgOfStep_eval_san C K idA idB Dh encPt encT decT lam L qep B T Kc Bsk hℓ
      (SanSnapExtra C K) (sanSnapExtra_init C K idA idB)
      (sanSnapExtra_step C K idA idB Dh encPt encT decT lam qep B T Kc Bsk)
      step (hstep hℓ) A q hq hqL]
    exact sm_game_simFig8ClampSan_eq (paramsV1 C K idA idB) Dh encPt encT decT (idsOf idA idB)
      (paramsV1_idsOf_eq C K idA idB) lam qep B T Kc Bsk cfg hq h232 hqB hT hKc hBsk
  simCNoneWinEvent_eq hℓ A hq := by
    rw [simFig8ProgOfStep_eval_san C K idA idB Dh encPt encT decT lam L qep B T Kc Bsk hℓ
      (SanSnapExtra C K) (sanSnapExtra_init C K idA idB)
      (sanSnapExtra_step C K idA idB Dh encPt encT decT lam qep B T Kc Bsk)
      step (hstep hℓ) A q hq hqL]
    exact simCNoneWinEvent_eq_sm_run_simFig8ClampSan (paramsV1 C K idA idB) Dh encPt encT decT
      (idsOf idA idB) (paramsV1_idsOf_eq C K idA idB) lam qep B T Kc Bsk hq h232 hqB hT hKc hBsk

/-- `SimFig8EvalOk` for `simFig8ProgOfStep` against `simFig8OracleSan` under `SanSnapExtra`. -/
theorem simFig8ProgOfStep_evalOk_san {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep q B T Kc Bsk : ℕ)
    (hqL : q ≤ L) (hB : 2 ^ 32 + q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep : ℓ < 10 ^ 6 → ∀ t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      SanSnapExtra C K (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk
        (.inr t)).run (simFullDec s_raw))) :
    SimFig8EvalOk Pt ℓ C K idA idB Dh encPt encT decT lam qep q
      (simFig8ProgOfStep C K Dh encPt encT decT lam step) :=
  simFig8ProgOfStep_evalOk_san' C K idA idB Dh encPt encT decT lam L qep q B T Kc Bsk
    hqL (by omega) (by omega) hT hKc hBsk step hstep

/-- Construct a `SimFig8AtomicStepBundle` from any single-query step body matching
`simFig8OracleSan` under `SimCStateBounded L` and `SanSnapExtra C K`. -/
def SimFig8AtomicStepBundle.ofSan {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (L qep q B T Kc Bsk : ℕ)
    (hqL : q ≤ L) (hB : 2 ^ 32 + q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hstep : ℓ < 10 ^ 6 → ∀ idA idB t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      SanSnapExtra C K (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk
        (.inr t)).run (simFullDec s_raw)))
    (hqep : qep ≤ q + 10) :
    SimFig8AtomicStepBundle Pt ℓ C K Dh encPt encT decT lam qep q where
  prog := simFig8ProgOfStep C K Dh encPt encT decT lam step
  gRedBounded :=
    simFig8ProgOfStep_gRedBounded C K Dh encPt encT decT lam qep q step hstep_q hstep_c hstep_d hqep
  descBits_le := simFig8ProgOfStep_descBits_le C K Dh encPt encT decT lam qep q step hstep_d
  evalOk idA idB := simFig8ProgOfStep_evalOk_san C K idA idB Dh encPt encT decT lam
    L qep q B T Kc Bsk hqL hB hT hKc hBsk step (fun hℓ => hstep hℓ idA idB)

def SimFig8AtomicStepBundle.ofSan' {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (L qep q B T Kc Bsk : ℕ)
    (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hstep : ℓ < 10 ^ 6 → ∀ idA idB t (s_raw : (simFullT ℓ Pt).denote),
      SimCStateBounded L (simFullDec s_raw) →
      SanSnapExtra C K (simFullDec s_raw) →
      (Prod.map id simFullDec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk
        (.inr t)).run (simFullDec s_raw)))
    (hqep : qep ≤ q + 10) :
    SimFig8AtomicStepBundle Pt ℓ C K Dh encPt encT decT lam qep q where
  prog := simFig8ProgOfStep C K Dh encPt encT decT lam step
  gRedBounded :=
    simFig8ProgOfStep_gRedBounded C K Dh encPt encT decT lam qep q step hstep_q hstep_c hstep_d hqep
  descBits_le := simFig8ProgOfStep_descBits_le C K Dh encPt encT decT lam qep q step hstep_d
  evalOk idA idB := simFig8ProgOfStep_evalOk_san' C K idA idB Dh encPt encT decT lam
    L qep q B T Kc Bsk hqL h232 hqB hT hKc hBsk step (fun hℓ => hstep hℓ idA idB)

end GameCouplingAndBridge

end Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
