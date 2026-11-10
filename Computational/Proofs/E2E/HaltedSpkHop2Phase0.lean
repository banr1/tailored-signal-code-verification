/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkHop2Core
public import Computational.Proofs.E2E.SpkHop1Phases01

/-!
# Tracker-Halted Hop-2 Phase 0

Lifts Phase 0 of the Hop-2 hybrid step to `KemFailSessionTrack`-halted reductions (`runHop2Track`,
`hop2PrfRedKTrackHalted`, `hop2PrgRedKTrackHalted`), parameterized by `Hop2TrackPhase1Bound`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSpkHop2Phase0

open scoped BigOperators ENNReal
open Classical OracleComp OracleSpec
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  initKemFailTrack)
open Computational.Proofs.E2E.HaltedSpkDefs (challRTrackHalted_support hop2GameTrackHalted
  hop2ImplTrackHalted hop2PrfRedKTrackHalted hop2PrgRedKTrackHalted transmitRTrackHalted_support
  updateKemFailOnDeliver)
open Computational.Proofs.E2E.HaltedSpkHop2Core (runHop2Track runHop2Track_bind_query
  runHop2Track_corr runHop2Track_deliver runHop2Track_hop2LiftTrackHalted' runHop2Track_noTrack
  runHop2Track_pure runHop2Track_unif simulateQ_prfReal_hop2ImplTrackHalted_eq_runHop2Track)
open CryptoGames (MACScheme Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (GhostState KeyPair LengthsOk Params PublicKey SessionState
  SignalMessage currentVersion)
open CryptoGames.Ratchet (RootKey expandPRG extractPRF)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh ratchetKeyAdmissible)
open CryptoGames.SM (Adversary GameState MakesAtMostQueries RecvResult corrR spec)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes Hop2Aux Hop2Hyb Hop2Out configRefuseEarlyBobCorr hop2BadAt
  hop2Commit hop2Deliver hop2Inject hop2Recv hop2Unif sessionSchemeU)
open CryptoVerification.E2E.SpkHop1 (Hop2FullInv Hop2Phase0Inv Hop2Phase1Rel Hop2State
  IsDeliverInTransitOrInjectPost IsGoodDeliverOrInjectPost bind_evalDist_true_eq
  bind_evalDist_true_le_of_support bind_le_of_support bind_unif_swap_evalDist_true_le
  bind_unif_swap_evalDist_true_le_of_good_rc challR_support_hop2FullInv corrR_support_hop2FullInv
  evalDist_bind_unif_swap evalDist_branch_true_eq_lazyImpl evalDist_unif_bind6_swap
  evalDist_unif_bind_const hop2CreateCollUnit hop2CreateOutChain
  hop2CreateOutChain_eq_of_tryDecrypt hop2DeliverPost hop2Deliver_run_eq_post hop2HybPrf hop2HybPrg
  hop2InjectPost hop2InjectPost_eq_of_not_commit hop2Inject_run_eq_post hop2NonDhOut
  hop2NonDhOut_snd_none hop2OffChainOut hop2OffChainOut_some_props hop2Phase0Inv_init
  hop2Phase0Inv_of_create_commit hop2Phase0Inv_of_post hop2Phase1Rel_of_phase0_self
  hop2Recv_run_of_idx_none hop2Recv_run_of_idx_some_non_dh hop2Recv_run_of_succ_eq_made_some
  lazyImpl partyOfParity party_eq_partyOfParity_or_succ pureStepHyb pureStepImpl
  simulateQ_lazyImpl_hop2Recv_of_le_made_none simulateQ_lazyImpl_hop2Recv_of_succ_lt_made_some
  simulateQ_lazyImpl_hop2Unif simulateQ_lazyImpl_liftM simulateQ_pureStepImpl_hop2Unif
  simulateQ_pureStepImpl_liftM stateT_lift_probComp_run stateT_run'_lift_bind steppedSessBase
  transmitR_support_hop2FullInv)

section Phase0

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Phase 1 coupling hypothesis at the `tbl = []`, `st_L = st_R` entry point when table `k` is
created (or immediately at `k = 0`). -/
abbrev Hop2TrackPhase1Bound (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ℓ qep : ℕ) (s : BitVec 256) (k : ℕ) (rc_L : RootKey × BitVec 256) : Prop :=
  ∀ (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ), MakesAtMostQueries oa rem →
    ∀ (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes),
      Hop2Phase1Rel P decT encT k st [] st →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) oa st tr []] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            oa st tr []] {true} +
        ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh

theorem evalDist_hop2RecvTrack_create_of_post_const {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (qep : ℕ) (s : BitVec 256) (h : Hop2Hyb Pt) (m : ℕ)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : _) (ckR : BitVec 256)
    (hidx : st.2.idx g.party = some m)
    (hmle : m + 1 ≤ h.k)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : g.session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0)
    (hmade : st.2.made.lookup (m, Dh.dh (st.2.coins g.party) T) = some ckR)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (o0 : Hop2Out Pt ℓ)
    (hconst : ∀ ckS, post (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS) st =
        post o0 st)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT h g c rc).run st)).run []
      runHop2Track P K Dh encT decT qep s h (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} =
    𝒟[runHop2Track P K Dh encT decT qep s h (k_oa (post o0 st).1)
      (post o0 st).2 (tr_next (post o0 st).1) []] {true} := by
  rcases Nat.lt_or_eq_of_le hmle with hlt | heq
  · rw [simulateQ_lazyImpl_hop2Recv_of_succ_lt_made_some P Dh encPt encT decT hX h m
      g c rc st msg T sc ckR hidx hlt htry hfind hdec hT hsc hQ0 hmade []]
    simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, hconst]
    exact evalDist_unif_bind_const _
  · rw [hop2Recv_run_of_succ_eq_made_some P Dh encPt encT decT hX h m
      g c rc st msg T sc ckR hidx heq htry hfind hdec hT hsc hQ0 hmade]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, hconst]

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_phase0_of_pure_recv {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k) (r_L : RootKey)
    {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes) (rc : BitVec 256)
    (o : Hop2Out Pt ℓ)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s Q c rc st post)
    (hrun_L : ∀ c_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k (r_L, c_chall)) (st.1.st Q) c rc).run st =
      pure (o, st))
    (hrun_R : ∀ u_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
        (st.1.st Q) c rc).run st =
      pure (o, st))
    (h_upd : ∀ x ∈ o, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
          (k_oa r) st' (tr_next r) []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' (tr_next r) []] {true} + ε) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) (st.1.st Q) c rc).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          (st.1.st Q) c rc).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} +
      ε := by
  have hsupp_R : ((o, st), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) 0)
        (st.1.st Q) c rc).run st)).run []) := by
    rw [hrun_R 0, simulateQ_pure, StateT.run_pure]
    simp only [support_pure, Set.mem_singleton_iff]
  have hinv' : Hop2FullInv P decT encT (post o st).2 :=
    hpost.preserves_hop2FullInv h0.inv ((o, st), []) hsupp_R
  have h0' :=
    hop2Phase0Inv_of_post h0 hpost.toIsDeliverOrInjectPost o st hinv' rfl rfl h0.lazy_gt h_upd
  simp only [hrun_L, hrun_R, simulateQ_pure, StateT.run_pure, pure_bind]
  exact ih' (post o st).1 m (post o st).2 hm h0'

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_phase0_of_lazy {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k m t : ℕ} (hm : m < k) (ht : t ≤ m + 1)
    (r_L : RootKey) {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes) (rc : BitVec 256) (msg : SignalMessage) (T : Pt) (sc : _)
    (hidx : st.2.idx (st.1.st Q).party = some t)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind : ((st.1.st Q).session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : (st.1.st Q).session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins (st.1.st Q).party) T ≠ 0)
    (hmade : st.2.made.lookup (t, Dh.dh (st.2.coins (st.1.st Q).party) T) = none)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s Q c rc st post)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
          (k_oa r) st' (tr_next r) []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' (tr_next r) []] {true} + ε) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) (st.1.st Q) c rc).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          (st.1.st Q) c rc).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} +
      ε := by
  set g := st.1.st Q
  set Q_in := Dh.dh (st.2.coins g.party) T
  have htk : t ≤ k := by omega
  have htk1 : t ≤ k + 1 := by omega
  have hrun_L : ∀ c_chall,
      (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc).run st)).run [] =
      match st.2.lazy.lookup (t, Q_in) with
      | some u => pure ((hop2OffChainOut P ℓ g msg sc rc u, st), [])
      | none => (fun u => ((hop2OffChainOut P ℓ g msg sc rc u,
          (st.1, { st.2 with lazy := ((t, Q_in), u) :: st.2.lazy })), [])) <$>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :=
    fun c_chall => simulateQ_lazyImpl_hop2Recv_of_le_made_none P Dh encT decT
      (hop2HybPrf k (r_L, c_chall)) t g c rc st msg T sc hidx htk htry hfind hdec hT hsc hQ0 hmade
      []
  have hrun_R : ∀ u_chall,
      (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          g c rc).run st)).run [] =
      match st.2.lazy.lookup (t, Q_in) with
      | some u => pure ((hop2OffChainOut P ℓ g msg sc rc u, st), [])
      | none => (fun u => ((hop2OffChainOut P ℓ g msg sc rc u,
          (st.1, { st.2 with lazy := ((t, Q_in), u) :: st.2.lazy })), [])) <$>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :=
    fun u_chall => simulateQ_lazyImpl_hop2Recv_of_le_made_none P Dh encT decT
      (hop2HybPrg P encPt (k + 1) u_chall) t g c rc st msg T sc hidx htk1 htry hfind hdec hT hsc
      hQ0 hmade []
  have h_upd : ∀ u : BitVec 256, ∀ x ∈ hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u,
      x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩ := by
    intro u x hx
    rcases x with ⟨⟨st', t', i', m'⟩, upd⟩
    have hp := hop2OffChainOut_some_props P g msg sc rc u (h0.inv.sender_inv Q) st' t' i' m' upd hx
    exact Or.inr ⟨rc, hp.1⟩
  simp only [hrun_L, hrun_R]
  cases hlook : st.2.lazy.lookup (t, Q_in) with
  | some u0 =>
    simp only [pure_bind]
    set o := hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u0
    have hsupp_R : ((o, st), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) 0) g c rc).run st)).run []) := by
      rw [hrun_R 0, hlook]
      simp only [support_pure, Set.mem_singleton_iff]
      rfl
    have hinv' : Hop2FullInv P decT encT (post o st).2 :=
      hpost.preserves_hop2FullInv h0.inv ((o, st), []) hsupp_R
    have h0' :=
      hop2Phase0Inv_of_post h0 hpost.toIsDeliverOrInjectPost o st hinv' rfl rfl h0.lazy_gt
        (h_upd u0)
    exact ih' (post o st).1 m (post o st).2 hm h0'
  | none =>
    simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    refine bind_unif_swap_evalDist_true_le ($ᵗ BitVec 256) _ _ ε fun u _ => ?_
    set o := hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u
    set st2 : Hop2State Pt ℓ := (st.1, { st.2 with lazy := ((t, Q_in), u) :: st.2.lazy })
    have hsupp_R : ((o, st2), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) 0) g c rc).run st)).run []) := by
      rw [hrun_R 0, hlook]
      simp only [map_eq_bind_pure_comp, Function.comp_apply,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      exact ⟨u, by simp, rfl⟩
    have hinv' : Hop2FullInv P decT encT (post o st2).2 :=
      hpost.preserves_hop2FullInv h0.inv ((o, st2), []) hsupp_R
    have hlazy2 : ∀ t' > m + 1, ∀ Q', st2.2.lazy.lookup (t', Q') = none := by
      intro t' ht' Q'
      have hne : (t', Q') ≠ (t, Q_in) := by
        intro h; rcases Prod.mk.inj h with ⟨h1, _⟩; omega
      dsimp only [st2]
      simp [List.lookup, beq_eq_false_iff_ne.mpr hne, h0.lazy_gt t' ht' Q']
    have h0' :=
      hop2Phase0Inv_of_post h0 hpost.toIsDeliverOrInjectPost o st2 hinv' rfl rfl hlazy2 (h_upd u)
    exact ih' (post o st2).1 m (post o st2).2 hm h0'

theorem evalDist_runHop2Track_phase0_of_create_pm {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT)
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k)
    (r_L : RootKey) {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (c : Bytes) (rc : BitVec 256) (msg : SignalMessage) (T : Pt) (sc : _) (ckR : BitVec 256)
    (hidx : st.2.idx (st.1.st (partyOfParity m)).party = some m)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind : ((st.1.st (partyOfParity m)).session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : (st.1.st (partyOfParity m)).session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins (st.1.st (partyOfParity m)).party) T ≠ 0)
    (hmade : st.2.made.lookup (m, Dh.dh (st.2.coins (st.1.st (partyOfParity m)).party) T) =
        some ckR)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s (partyOfParity m) c rc st post)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (ε : ℝ≥0∞)
    (hph1 : ∀ c_chall r st', Hop2Phase1Rel P decT encT k st' [] st' →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa r) st' (tr_next r) []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' (tr_next r) []] {true} + ε)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
          (k_oa r) st' (tr_next r) []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' (tr_next r) []] {true} + ε) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall))
          (st.1.st (partyOfParity m)) c rc).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          (st.1.st (partyOfParity m)) c rc).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} +
      ε := by
  set Q := partyOfParity m
  set g := st.1.st Q
  have hmk : m + 1 ≤ k := by omega
  have hmk1 : m + 1 < k + 1 := by omega
  have hrun_R : ∀ u_chall,
      (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          g c rc).run st)).run [] =
      (fun ckS => ((hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS, st), [])) <$>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :=
    fun u_chall => simulateQ_lazyImpl_hop2Recv_of_succ_lt_made_some P Dh encPt encT decT hX
      (hop2HybPrg P encPt (k + 1) u_chall) m g c rc st msg T sc ckR
      hidx hmk1 htry hfind hdec hT hsc hQ0 hmade []
  have hsupp_R : ∀ ckS,
      ((hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS, st), []) ∈
        support ((simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) 0) g c rc).run st)).run []) := by
    intro ckS
    rw [hrun_R 0]
    simp only [map_eq_bind_pure_comp, Function.comp_apply,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
    exact ⟨ckS, by simp, rfl⟩
  set prev := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
  have hout_eq := fun ckS =>
    hop2CreateOutChain_eq_of_tryDecrypt (Pt := Pt) (ℓ := ℓ) P (m + 1) (Dh.dh rc T) g msg sc rc ckR
      ckS hfind
  rcases htr0 : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper 0 (steppedSessBase g msg prev ckR) with ⟨r_tr, s_base⟩
  cases r_tr with
  | error _ =>
    have hconst : ∀ ckS, post (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS) st =
        post none st := fun ckS => by rw [hout_eq ckS, htr0]
    have hL_eq : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc).run st)).run []
        runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
          (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1)
          z.2)] {true} =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
          (k_oa (post none st).1) (post none st).2 (tr_next (post none st).1) []] {true} :=
      bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun c_chall =>
        evalDist_hop2RecvTrack_create_of_post_const P K Dh encPt encT decT hX qep s
          (hop2HybPrf k (r_L, c_chall)) m g c rc st msg T sc ckR
          hidx hmk htry hfind hdec hT hsc hQ0 hmade post none hconst tr_next k_oa
    have hR_eq : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st)).run []
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1)
          z.2)] {true} =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa (post none st).1) (post none st).2 (tr_next (post none st).1) []] {true} :=
      bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun u_chall =>
        evalDist_hop2RecvTrack_create_of_post_const P K Dh encPt encT decT hX qep s
          (hop2HybPrg P encPt (k + 1) u_chall) m g c rc st msg T sc ckR
          hidx (Nat.le_of_lt hmk1) htry hfind hdec hT hsc hQ0 hmade post none hconst tr_next k_oa
    rw [hL_eq, hR_eq]
    have hinv' : Hop2FullInv P decT encT (post none st).2 := by
      have h1 := hpost.preserves_hop2FullInv h0.inv _ (hsupp_R 0)
      rw [hout_eq 0, htr0] at h1
      exact h1
    have h0' :=
      hop2Phase0Inv_of_post h0 hpost.toIsDeliverOrInjectPost none st hinv' rfl rfl h0.lazy_gt
        (by simp)
    exact ih' (post none st).1 m (post none st).2 hm h0'
  | ok m_plain =>
    by_cases hcomm : (∃ r_rec, post = hop2DeliverPost P s Q c g r_rec) ∨
        (post = hop2InjectPost P qep s Q c g ∧ ¬ (qep + 1 < g.epoch + 1) ∧
          st.1.trivial 3 ⟨Q.other, g.epoch + 1, msg.counter.toNat + 1⟩ = true)
    · have h0_step : ∀ ckS,
          Hop2Phase0Inv P decT encT (m + 1)
            (post (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS) st).2 ∧
          (∀ t > m + 1, ∀ Q',
            (post (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS)
              st).2.2.lazy.lookup (t, Q') = none) := by
        intro ckS
        set o := hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS
        have hinv' := hpost.preserves_hop2FullInv h0.inv ((o, st), []) (hsupp_R ckS)
        rcases hcomm with ⟨r_rec, rfl⟩ | ⟨rfl, hqep_le, htriv⟩
        · have hpost_aux : (hop2DeliverPost P s Q c g r_rec o st).2.2 =
              { hop2Commit st.2 Q (some ⟨some (m + 2), rc, some ((m + 1, Dh.dh rc T), ckS)⟩) with
                bad := st.2.bad || hop2BadAt P s g c } := by
            dsimp only [o]; rw [hout_eq ckS, htr0]; rfl
          exact hop2Phase0Inv_of_create_commit h0 rc (Dh.dh rc T) ckS _ hinv'
            (by rw [hpost_aux]; rfl)
            (by rw [hpost_aux])
            (by rw [hpost_aux])
        · have hpost_aux : (hop2InjectPost P qep s Q c g o st).2.2 =
              hop2Commit { st.2 with bad := st.2.bad || hop2BadAt P s g c } Q
                (some ⟨some (m + 2), rc, some ((m + 1, Dh.dh rc T), ckS)⟩) := by
            dsimp only [o]; rw [hout_eq ckS, htr0]
            dsimp only [hop2InjectPost]
            simp [hqep_le, htriv]
          exact hop2Phase0Inv_of_create_commit h0 rc (Dh.dh rc T) ckS _ hinv'
            (by rw [hpost_aux]; rfl)
            (by rw [hpost_aux]; rfl)
            (by rw [hpost_aux]; rfl)
      rcases Nat.lt_or_eq_of_le hmk with hlt | heq
      · have hrun_L : ∀ c_chall,
            (simulateQ (lazyImpl (Pt := Pt))
              ((hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k (r_L, c_chall))
                g c rc).run st)).run [] =
            (fun ckS => ((hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS, st),
                [])) <$>
              ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :=
          fun c_chall => simulateQ_lazyImpl_hop2Recv_of_succ_lt_made_some P Dh encPt encT decT hX
            (hop2HybPrf k (r_L, c_chall)) m g c rc st msg T sc ckR
            hidx hlt htry hfind hdec hT hsc hQ0 hmade []
        simp only [hrun_L, hrun_R, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc,
            pure_bind]
        refine bind_unif_swap_evalDist_true_le ($ᵗ BitVec 256) _ _ ε fun ckS _ => ?_
        exact ih' _ (m + 1) _ hlt (h0_step ckS).1
      · have hrun_L : ∀ c_chall,
            (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc).run st =
            pure (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR c_chall, st) :=
          fun c_chall => hop2Recv_run_of_succ_eq_made_some P Dh encPt encT decT hX
            (hop2HybPrf k (r_L, c_chall)) m g c rc st msg T sc ckR
            hidx heq htry hfind hdec hT hsc hQ0 hmade
        simp only [hrun_L, hrun_R, simulateQ_pure, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
        rw [evalDist_bind_unif_swap ($ᵗ BitVec 256)]
        refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ ε fun c_chall _ => ?_
        obtain ⟨h0_next, hlazy_next⟩ := h0_step c_chall
        subst heq
        exact hph1 c_chall _ _ (hop2Phase1Rel_of_phase0_self (m + 1) _ h0_next
          (fun Q' => hlazy_next (m + 1 + 1) (by omega) Q'))
    · rcases hpost.toIsDeliverOrInjectPost with ⟨r_rec, rfl⟩ | hpost_inj
      · exact absurd (Or.inl ⟨r_rec, rfl⟩) hcomm
      · have hnc : ¬ (¬ (qep + 1 < g.epoch + 1) ∧
            st.1.trivial 3 ⟨Q.other, g.epoch + 1, msg.counter.toNat + 1⟩ = true) :=
          fun h => hcomm (Or.inr ⟨hpost_inj, h.1, h.2⟩)
        set o0 := hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR 0
        have hconst : ∀ ckS, hop2InjectPost P qep s Q c g
            (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS) st =
            hop2InjectPost P qep s Q c g o0 st := by
          intro ckS
          dsimp only [o0]
          rw [hout_eq ckS, hout_eq 0, htr0]
          exact hop2InjectPost_eq_of_not_commit P qep s Q c g _ _ _ _ _ _ _ st hnc
        have hL_eq : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
            let z ← (simulateQ (lazyImpl (Pt := Pt))
              ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc).run st)).run []
            runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
              (k_oa (hop2InjectPost P qep s Q c g z.1.1 z.1.2).1)
              (hop2InjectPost P qep s Q c g z.1.1 z.1.2).2
              (tr_next (hop2InjectPost P qep s Q c g z.1.1 z.1.2).1) z.2)] {true} =
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
            runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
              (k_oa (hop2InjectPost P qep s Q c g o0 st).1)
              (hop2InjectPost P qep s Q c g o0 st).2
              (tr_next (hop2InjectPost P qep s Q c g o0 st).1) []] {true} :=
          bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun c_chall =>
            evalDist_hop2RecvTrack_create_of_post_const P K Dh encPt encT decT hX qep s
              (hop2HybPrf k (r_L, c_chall)) m g c rc st msg T sc ckR
              hidx hmk htry hfind hdec hT hsc hQ0 hmade (hop2InjectPost P qep s Q c g) o0 hconst
              tr_next k_oa
        have hR_eq : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
            let z ← (simulateQ (lazyImpl (Pt := Pt))
              ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st)).run []
            runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
              (k_oa (hop2InjectPost P qep s Q c g z.1.1 z.1.2).1)
              (hop2InjectPost P qep s Q c g z.1.1 z.1.2).2
              (tr_next (hop2InjectPost P qep s Q c g z.1.1 z.1.2).1) z.2)] {true} =
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
            runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
              (k_oa (hop2InjectPost P qep s Q c g o0 st).1)
              (hop2InjectPost P qep s Q c g o0 st).2
              (tr_next (hop2InjectPost P qep s Q c g o0 st).1) []] {true} :=
          bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun u_chall =>
            evalDist_hop2RecvTrack_create_of_post_const P K Dh encPt encT decT hX qep s
              (hop2HybPrg P encPt (k + 1) u_chall) m g c rc st msg T sc ckR
              hidx (Nat.le_of_lt hmk1) htry hfind hdec hT hsc hQ0 hmade
              (hop2InjectPost P qep s Q c g) o0 hconst tr_next k_oa
        simp only [hpost_inj]
        rw [hL_eq, hR_eq]
        have hinv' : Hop2FullInv P decT encT (hop2InjectPost P qep s Q c g o0 st).2 := by
          have h1 := hpost.preserves_hop2FullInv h0.inv ((o0, st), []) (hsupp_R 0)
          simpa only [hpost_inj] using h1
        have hnc_aux : (hop2InjectPost P qep s Q c g o0 st).2.2 =
            { st.2 with bad := st.2.bad || hop2BadAt P s g c } := by
          dsimp only [o0]; rw [hout_eq 0, htr0]
          dsimp only [hop2InjectPost]
          by_cases hqep : qep + 1 < g.epoch + 1
          · simp [hqep]
          · have htrivF : st.1.trivial 3 ⟨Q.other, g.epoch + 1, msg.counter.toNat + 1⟩ = false := by
              cases h : st.1.trivial 3 ⟨Q.other, g.epoch + 1, msg.counter.toNat + 1⟩
              · rfl
              · exact absurd ⟨hqep, h⟩ hnc
            simp [hqep, htrivF]
        have h0' : Hop2Phase0Inv P decT encT m (hop2InjectPost P qep s Q c g o0 st).2 :=
          ⟨hinv',
           by rw [congrArg Hop2Aux.idx hnc_aux]; exact h0.idx_pm,
           by rw [congrArg Hop2Aux.idx hnc_aux]; exact h0.idx_pm1,
           by rw [congrArg Hop2Aux.made hnc_aux]; exact h0.made_gt,
           by rw [congrArg Hop2Aux.lazy hnc_aux]; exact h0.lazy_gt⟩
        exact ih' _ m _ hm h0'

theorem evalDist_runHop2Track_phase0_recvWithPost_le {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k) (r_L : RootKey)
    {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsDeliverInTransitOrInjectPost (Pt := Pt) P qep s Q c st.1 post)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (d ε : ℝ≥0∞)
    (hd : d + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hph1 : ∀ c_chall r st', Hop2Phase1Rel P decT encT k st' [] st' →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa r) st' (tr_next r) []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' (tr_next r) []] {true} + d)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
          (k_oa r) st' (tr_next r) []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' (tr_next r) []] {true} + d) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) (st.1.st Q) c rc).run st
        return post res.1 res.2)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa z.1.1) z.1.2 (tr_next z.1.1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          (st.1.st Q) c rc).run st
        return post res.1 res.2)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa z.1.1) z.1.2 (tr_next z.1.1) z.2)] {true} + ε := by
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
    stateT_lift_probComp_run, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
  refine bind_unif_swap_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st Q _ _ d ε hd
    fun rc hgood_rc => ?_
  have hpost_rc := hpost.withGoodRc hgood_rc
  rcases party_eq_partyOfParity_or_succ m Q with rfl | rfl
  · set Q0 := partyOfParity m
    set g := st.1.st Q0
    have hp : g.party = Q0 := h0.inv.party_eq Q0
    rcases h0.idx_pm with hnone | hsome
    · have hidx : st.2.idx g.party = none := by rw [hp]; exact hnone
      have hrun_L := fun c_chall =>
        hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc st hidx
      have hrun_R := fun u_chall =>
        hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc st hidx
      refine evalDist_runHop2Track_phase0_of_pure_recv hm r_L h0 Q0 c rc
        (((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none)))
        post hpost_rc hrun_L hrun_R ?_ tr_next k_oa d ih'
      intro x hx
      simp only [Option.mem_def, Option.map_eq_some_iff] at hx
      rcases hx with ⟨_, _, rfl⟩
      exact Or.inl rfl
    · have hidx : st.2.idx g.party = some m := by rw [hp]; exact hsome
      by_cases hdh : ∃ msg T sc,
          SignalMessage.tryFrom P.codec c = .ok msg ∧
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
              true ∧
          decT msg.senderRatchetKey = some T ∧
          ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
          g.session.senderChain = some sc ∧
          Dh.dh (st.2.coins g.party) T ≠ 0
      · rcases hdh with ⟨msg, T, sc, htry, hfind, hdec_T, hT, hsc, hQ0⟩
        cases hmade : st.2.made.lookup (m, Dh.dh (st.2.coins g.party) T) with
        | none =>
          exact evalDist_runHop2Track_phase0_of_lazy hm (Nat.le_succ m) r_L h0 Q0 c rc msg T sc
            hidx htry hfind hdec_T hT hsc hQ0 hmade post hpost_rc tr_next k_oa d ih'
        | some ckR =>
          exact evalDist_runHop2Track_phase0_of_create_pm hX hm r_L h0 c rc msg T sc ckR
            hidx htry hfind hdec_T hT hsc hQ0 hmade post hpost_rc tr_next k_oa d hph1 ih'
      · have hrun_L := fun c_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrf k (r_L, c_chall))
            m g c rc st hidx hdh
        have hrun_R := fun u_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
            m g c rc st hidx hdh
        exact evalDist_runHop2Track_phase0_of_pure_recv hm r_L h0 Q0 c rc (hop2NonDhOut P ℓ g c rc)
          post hpost_rc hrun_L hrun_R
          (fun x hx => Or.inl (hop2NonDhOut_snd_none P g c rc x hx)) tr_next k_oa d ih'
  · set Q1 := partyOfParity (m + 1)
    set g := st.1.st Q1
    have hp : g.party = Q1 := h0.inv.party_eq Q1
    rcases h0.idx_pm1 with hnone | hsome
    · have hidx : st.2.idx g.party = none := by rw [hp]; exact hnone
      have hrun_L := fun c_chall =>
        hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc st hidx
      have hrun_R := fun u_chall =>
        hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc st hidx
      refine evalDist_runHop2Track_phase0_of_pure_recv hm r_L h0 Q1 c rc
        (((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none)))
        post hpost_rc hrun_L hrun_R ?_ tr_next k_oa d ih'
      intro x hx
      simp only [Option.mem_def, Option.map_eq_some_iff] at hx
      rcases hx with ⟨_, _, rfl⟩
      exact Or.inl rfl
    · have hidx : st.2.idx g.party = some (m + 1) := by rw [hp]; exact hsome
      by_cases hdh : ∃ msg T sc,
          SignalMessage.tryFrom P.codec c = .ok msg ∧
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
              true ∧
          decT msg.senderRatchetKey = some T ∧
          ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
          g.session.senderChain = some sc ∧
          Dh.dh (st.2.coins g.party) T ≠ 0
      · rcases hdh with ⟨msg, T, sc, htry, hfind, hdec_T, hT, hsc, hQ0⟩
        have hmade : st.2.made.lookup (m + 1, Dh.dh (st.2.coins g.party) T) = none :=
          h0.made_gt (m + 1) (Nat.lt_succ_self m) _
        exact evalDist_runHop2Track_phase0_of_lazy hm (le_refl (m + 1)) r_L h0 Q1 c rc msg T sc
          hidx htry hfind hdec_T hT hsc hQ0 hmade post hpost_rc tr_next k_oa d ih'
      · have hrun_L := fun c_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrf k (r_L, c_chall))
            (m + 1) g c rc st hidx hdh
        have hrun_R := fun u_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
            (m + 1) g c rc st hidx hdh
        exact evalDist_runHop2Track_phase0_of_pure_recv hm r_L h0 Q1 c rc (hop2NonDhOut P ℓ g c rc)
          post hpost_rc hrun_L hrun_R
          (fun x hx => Or.inl (hop2NonDhOut_snd_none P g c rc x hx)) tr_next k_oa d ih'

theorem evalDist_runHop2Track_phase0_deliver_le {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k) (r_L : RootKey)
    {st : Hop2State Pt ℓ} (tr : KemFailSessionTrack P.C.F Bytes)
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (d ε : ℝ≥0∞)
    (hd : d + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hph1 : ∀ c_chall r st', Hop2Phase1Rel P decT encT k st' [] st' →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa r) st' (updateKemFailOnDeliver P.C.F K tr (Q, c) r) []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' (updateKemFailOnDeliver P.C.F K tr (Q, c) r) []] {true} + d)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
          (k_oa r) st' (updateKemFailOnDeliver P.C.F K tr (Q, c) r) []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' (updateKemFailOnDeliver P.C.F K tr (Q, c) r) []] {true} + d) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrf k (r_L, c_chall)) (Q, c)).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa z.1.1) z.1.2 (updateKemFailOnDeliver P.C.F K tr (Q, c) z.1.1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrg P encPt (k + 1) u_chall) (Q, c)).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa z.1.1) z.1.2 (updateKemFailOnDeliver P.C.F K tr (Q, c) z.1.1) z.2)] {true} + ε := by
  have hd_le : d ≤ ε := le_self_add.trans hd
  by_cases hwin : st.1.win = true
  · unfold hop2Deliver
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
      StateT.run_pure, simulateQ_pure]
    exact (ih' none m st hm h0).trans (add_le_add le_rfl hd_le)
  · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
    cases hin : st.1.inTransit Q.other c with
    | none =>
      unfold hop2Deliver
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hwinF, Bool.false_eq_true, ↓reduceIte,
        hin, StateT.run_pure, simulateQ_pure]
      exact (ih' none m st hm h0).trans (add_le_add le_rfl hd_le)
    | some r_rec =>
      simp only [hop2Deliver_run_eq_post P Dh encT decT s _ Q c st r_rec hwinF hin]
      exact evalDist_runHop2Track_phase0_recvWithPost_le (qep := qep) hX hdec hm r_L h0 Q c
        _ (Or.inl ⟨r_rec, hin, rfl⟩) (updateKemFailOnDeliver P.C.F K tr (Q, c)) k_oa d ε hd hph1
        ih'

theorem evalDist_runHop2Track_phase0_inject_le {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k) (r_L : RootKey)
    {st : Hop2State Pt ℓ} (tr : KemFailSessionTrack P.C.F Bytes)
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (d ε : ℝ≥0∞)
    (hd : d + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hph1 : ∀ c_chall r st', Hop2Phase1Rel P decT encT k st' [] st' →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa r) st' tr []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' tr []] {true} + d)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
          (k_oa r) st' tr []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa r) st' tr []] {true} + d) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (Q, c)).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
        (k_oa z.1.1) z.1.2 tr z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (Q, c)).run st)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa z.1.1) z.1.2 tr z.2)] {true} + ε := by
  have hd_le : d ≤ ε := le_self_add.trans hd
  by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · unfold hop2Inject
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte,
      StateT.run_pure, simulateQ_pure]
    exact (ih' none m st hm h0).trans (add_le_add le_rfl hd_le)
  · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
    simp only [hop2Inject_run_eq_post P Dh encT decT qep s _ Q c st hgF]
    exact evalDist_runHop2Track_phase0_recvWithPost_le hX hdec hm r_L h0 Q c
      _ (Or.inr rfl) (fun _ => tr) k_oa d ε hd hph1 ih'

theorem evalDist_runHop2Track_phase0_le {ℓ : ℕ} {P : Params Bytes (BitVec 512)} {K : MlKem}
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (s : BitVec 256) (k : ℕ) (r_L : RootKey)
    (hph1 : ∀ c_chall, Hop2TrackPhase1Bound P K Dh encPt decT encT ℓ qep s k (r_L, c_chall))
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ) (hq : MakesAtMostQueries oa rem)
    (m : ℕ) (hm : m < k) (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (h0 : Hop2Phase0Inv P decT encT m st) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) oa st tr []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          oa st tr []] {true} +
      ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem m st tr with
  | pure a =>
    simp only [runHop2Track_pure, evalDist_unif_bind_const]
    exact le_self_add
  | query_bind t k_oa ih =>
    rw [MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
    simp only [runHop2Track_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · simp only [runHop2Track_unif]
      exact bind_unif_swap_evalDist_true_le _ _ _ _ fun a _ =>
        ih a rem (by simpa [MakesAtMostQueries] using hq.2 a) m hm st tr h0
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      simp_rw [runHop2Track_hop2LiftTrackHalted']
      refine bind_unif_swap_evalDist_true_le _ _ _ _ fun r hr => ?_
      have hle : (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      rcases r with ⟨⟨o_tr, s_tr⟩, tr'⟩
      rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) y_tr st.1 tr hr with hz1 | hr_base
      · rcases Prod.mk.inj hz1 with ⟨rfl, rfl⟩
        exact (ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
          m hm st tr' h0).trans (add_le_add le_rfl hle)
      · have hinv' :=
          transmitR_support_hop2FullInv P hcodec hL Dh encPt decT encT hX hdec qep y_tr st h0.inv
            (o_tr, s_tr) hr_base
        exact (ih o_tr (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 o_tr)
          m hm (s_tr, st.2) tr' (h0.of_st1_step s_tr hinv')).trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      simp_rw [runHop2Track_hop2LiftTrackHalted']
      refine bind_unif_swap_evalDist_true_le _ _ _ _ fun r hr => ?_
      have hle : (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      rcases r with ⟨⟨o_ch, s_ch⟩, tr'⟩
      rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) y_ch st.1 tr hr with hz1 | hr_base
      · rcases Prod.mk.inj hz1 with ⟨rfl, rfl⟩
        exact (ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
          m hm st tr' h0).trans (add_le_add le_rfl hle)
      · have hinv' :=
          challR_support_hop2FullInv P hcodec hL Dh encPt decT encT hX hdec qep y_ch st h0.inv
            (o_ch, s_ch) hr_base
        exact (ih o_ch (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 o_ch)
          m hm (s_ch, st.2) tr' (h0.of_st1_step s_ch hinv')).trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      have hL_eq := congrArg (fun f => 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= f] {true})
        (funext fun c_chall =>
          runHop2Track_deliver P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
            (Q, c) k_oa st tr [])
      have hR_eq := congrArg (fun f => 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= f] {true})
        (funext fun u_chall =>
          runHop2Track_deliver P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            (Q, c) k_oa st tr [])
      refine hL_eq.trans_le (le_trans ?_ (add_le_add hR_eq.symm.le le_rfl))
      have hd : ((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast (by omega : 6 * (rem - 1) + 5 ≤ 6 * rem)) zero_le
      refine evalDist_runHop2Track_phase0_deliver_le (qep := qep) hX hdec hm r_L tr h0 Q c k_oa
        (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) hd
        (fun c_chall r st' hrel1 =>
          hph1 c_chall (k_oa r) (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r)
            st' (updateKemFailOnDeliver P.C.F K tr (Q, c) r) hrel1)
        (fun r m' st' hm' h0' =>
          ih r (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r)
            m' hm' st' (updateKemFailOnDeliver P.C.F K tr (Q, c) r) h0')
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      simp_rw [runHop2Track_noTrack]
      have hd : ((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast (by omega : 6 * (rem - 1) + 5 ≤ 6 * rem)) zero_le
      refine evalDist_runHop2Track_phase0_inject_le hX hdec hm r_L tr h0 Q c k_oa
        (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) hd
        (fun c_chall r st' hrel1 =>
          hph1 c_chall (k_oa r) (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r)
            st' tr hrel1)
        (fun r m' st' hm' h0' =>
          ih r (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r)
            m' hm' st' tr h0')
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      have hL_eq := congrArg (fun f => 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= f] {true})
        (funext fun c_chall =>
          runHop2Track_corr P K Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
            y_corr k_oa st tr [])
      have hR_eq := congrArg (fun f => 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= f] {true})
        (funext fun u_chall =>
          runHop2Track_corr P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            y_corr k_oa st tr [])
      refine hL_eq.trans_le (le_trans ?_ (add_le_add hR_eq.symm.le le_rfl))
      refine bind_unif_swap_evalDist_true_le _ _ _ _ fun r hr => ?_
      have hinv' := corrR_support_hop2FullInv P decT encT y_corr st h0.inv r hr
      have hle : (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r.1)
        m hm (r.2, st.2) tr (h0.of_st1_step r.2 hinv')).trans (add_le_add le_rfl hle)

omit [SampleableType Pt] in
theorem prgRealExperiment_hop2PrgRedKTrackHalted_succ_eq {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    (expandPRG P.C.F).prgRealExperiment
        (hop2PrgRedKTrackHalted P K ℓ Dh encPt encT decT qep s (k + 1) A) =
      (do
        let u_chall ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let u1 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let I0 := Dh.dh x (Dh.dh alice Dh.base)
        let spk := (KeyPair.generate P.C x).publicKey
        let sessA := ((SessionState.new currentVersion P.idA P.idB 0
          (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
          (KeyPair.generate P.C alice) ⟨u1, 0⟩
        let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
        let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
        let initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
          { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
        let aux0 : Hop2Aux Pt :=
          { made := [((0, I0), u1)]
            idx := fun Q => match Q with | .A => some 1 | .B => some 0
            coins := fun Q => match Q with | .A => alice | .B => x }
        let tr₀ : KemFailSessionTrack P.C.F Bytes := (initKemFailTrack P.C.F pqr, [])
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          A (initSt, aux0) tr₀ []) := by
  unfold PRGScheme.prgRealExperiment hop2PrgRedKTrackHalted
  refine bind_congr fun u_chall => ?_
  change simulateQ (pureStepImpl _)
    (hop2GameTrackHalted P K ℓ Dh encT decT qep s (pureStepHyb (k + 1) _ _) A) = _
  unfold hop2GameTrackHalted
  rw [simulateQ_bind, simulateQ_pureStepImpl_liftM]
  refine bind_congr fun b => ?_
  rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
  refine bind_congr fun ck0 => ?_
  rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
  refine bind_congr fun x => ?_
  rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
  refine bind_congr fun alice => ?_
  rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
  refine bind_congr fun pqr => ?_
  rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
  refine bind_congr fun u1 => ?_
  rw [simulateQ_bind]
  simp only [simulateQ_pure]
  exact simulateQ_prfReal_hop2ImplTrackHalted_eq_runHop2Track P K Dh encT decT qep s
    (k + 1) _ _ A _ _

theorem evalDist_hop2PrfRedKTrackHalted_true_le_hop2PrgRedKTrackHalted_succ_of_phase1 {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep q : ℕ) (s : BitVec 256) (k : ℕ)
    (hph1 : ∀ rc_L, Hop2TrackPhase1Bound P K Dh encPt decT encT ℓ qep s k rc_L)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) :
    𝒟[(extractPRF P.C.F encPt).branch true
        (hop2PrfRedKTrackHalted P K ℓ Dh encT decT qep s k A)] {true} ≤
      𝒟[(expandPRG P.C.F).prgRealExperiment
        (hop2PrgRedKTrackHalted P K ℓ Dh encPt encT decT qep s (k + 1) A)] {true} +
        ((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
  rw [evalDist_branch_true_eq_lazyImpl, prgRealExperiment_hop2PrgRedKTrackHalted_succ_eq]
  have hunfold :
      (simulateQ (lazyImpl (Pt := Pt))
        (hop2PrfRedKTrackHalted P K ℓ Dh encT decT qep s k A)).run' [] =
      (do
        let r ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let c_chall ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let u1 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck1 := if k = 0 then c_chall else u1
        let I0 := Dh.dh x (Dh.dh alice Dh.base)
        let spk := (KeyPair.generate P.C x).publicKey
        let sessA := ((SessionState.new currentVersion P.idA P.idB 0
          (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
          (KeyPair.generate P.C alice) ⟨ck1, 0⟩
        let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
        let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
        let initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
          { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
        let aux0 : Hop2Aux Pt :=
          { made := [((0, I0), ck1)]
            idx := fun Q => match Q with | .A => some 1 | .B => some 0
            coins := fun Q => match Q with | .A => alice | .B => x }
        let tr₀ : KemFailSessionTrack P.C.F Bytes := (initKemFailTrack P.C.F pqr, [])
        runHop2Track P K Dh encT decT qep s (hop2HybPrf k (r, c_chall))
          A (initSt, aux0) tr₀ []) := by
    unfold hop2PrfRedKTrackHalted
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun r => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun c_chall => ?_
    unfold hop2GameTrackHalted
    rw [simulateQ_bind, simulateQ_lazyImpl_liftM, stateT_run'_lift_bind]
    refine bind_congr fun b => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun ck0 => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun x => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun alice => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun pqr => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun u1 => ?_
    rfl
  rw [hunfold]
  refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun r _ => ?_
  rw [evalDist_unif_bind6_swap, evalDist_unif_bind6_swap]
  refine bind_evalDist_true_le_of_support ($ᵗ Bool) _ _ _ fun b _ => ?_
  refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ _ fun ck0 _ => ?_
  refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ _ fun x _ => ?_
  refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ _ fun alice _ => ?_
  refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ _ fun pqr _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp only [↓reduceIte, evalDist_unif_bind_const]
    refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ _ fun ck1 _ => ?_
    have h0 := hop2Phase0Inv_init (ℓ := ℓ) P decT encT b ck0 x alice pqr ck1
      (Dh.dh x (Dh.dh alice Dh.base))
    have hrel1 := hop2Phase1Rel_of_phase0_self 0 _ h0 (fun _ => rfl)
    exact hph1 (r, ck1) A q hq _ (initKemFailTrack P.C.F pqr, []) hrel1
  · refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ _ fun u1 _ => ?_
    simp only [Nat.ne_of_gt hk_pos, ↓reduceIte]
    have h0 := hop2Phase0Inv_init (ℓ := ℓ) P decT encT b ck0 x alice pqr u1
      (Dh.dh x (Dh.dh alice Dh.base))
    exact evalDist_runHop2Track_phase0_le hcodec hL hX hdec qep s k r
      (fun c_chall => hph1 (r, c_chall)) A q hq 0 hk_pos _
      (initKemFailTrack P.C.F pqr, []) h0

end Phase0

end Computational.Proofs.E2E.HaltedSpkHop2Phase0
