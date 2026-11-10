/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkHop2Core
public import Computational.Proofs.E2E.SpkHop1Phases01A
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins

/-!
# Tracker-Halted Hop-2 Phase 1

Lifts Phase 1 of the Hop-2 `k → k + 1` hybrid step onto `runHop2Track`, coupling `hop2HybPrf k` and
`hop2HybPrg (k + 1)` across shared `KemFailSessionTrack` state under `Hop2TrackPhase2Bound`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSpkHop2Phase1

open scoped BigOperators ENNReal
open Classical OracleComp OracleSpec
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  challRTrackHalted transmitRTrackHalted)
open Computational.Proofs.E2E.HaltedSpkDefs (challRTrackHalted_support hop2ImplTrackHalted
  transmitRTrackHalted_support updateKemFailOnDeliver)
open Computational.Proofs.E2E.HaltedSpkHop2Core (evalDist_runHop2Track_tbl_discard runHop2Track
  runHop2Track_bind_query runHop2Track_corr runHop2Track_deliver
  runHop2Track_hop2LiftTrackHalted' runHop2Track_noTrack runHop2Track_pure runHop2Track_unif)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (GhostState KeyPair LengthsOk Params PublicKey SenderChain
  SessionState SignalMessage)
open CryptoGames.MACScheme (evalQuery)
open CryptoGames.Ratchet (RootKey padOrTruncatePlain rootExpand)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh ratchetKeyAdmissible)
open CryptoGames.SM (MakesAtMostQueries RecvResult corrR spec)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes Hop2Out configRefuseEarlyBobCorr hop2Deliver hop2Inject
  hop2Lazy hop2Recv hop2Unif sessionSchemeU)
open CryptoVerification.E2E.SpkHop1 (Hop2FullInv Hop2Phase1Rel Hop2Phase2Rel Hop2State Hop2WindowInv
  IsDeliverInTransitOrInjectPost IsGoodDeliverOrInjectPost badDeliverRc badDeliverRc_prob_le
  bind_apply_le_add_of_evalDist_le_on_good_window bind_evalDist_true_le_of_good_rc
  bind_evalDist_true_le_of_support bind_or_evalDist_true_le challR_support_hop2FullInv
  corrR_support_hop2FullInv dh_lookup_isSome_prob_le_hop2CreateCollUnit evalDist_bind_unif_swap
  evalDist_unif_bind_const hop2CreateCollUnit hop2CreateOutChain hop2CreateOutChain_eq_of_tryDecrypt
  hop2CreateOutL hop2CreateOutL_eq_of_tryDecrypt hop2DeliverPost hop2Deliver_run_eq_post
  hop2HybPrf hop2HybPrg hop2InjectPost hop2InjectPost_eq_of_not_commit hop2Inject_run_eq_post
  hop2NonDhOut_snd_none hop2OffChainOut hop2OffChainOut_some_props hop2Phase1Rel_of_post
  hop2Phase2Rel_of_create_commit hop2Recv_run_at_create_prf hop2Recv_run_at_succ
  hop2Recv_run_of_idx_none hop2Recv_run_of_idx_some_non_dh hop2Recv_run_of_le_made_none
  hop2Recv_run_of_succ_eq_made_some hop2SteppedGhost lazyImpl partyOfParity
  party_eq_partyOfParity_or_succ simulateQ_lazyImpl_evalQuery simulateQ_lazyImpl_hop2Unif
  simulateQ_lazyImpl_map_evalQuery simulateQ_lazyImpl_map_hop2Lazy stateT_lift_probComp_run
  steppedSessBase transmitR_support_hop2FullInv)

section Phase1

attribute [local irreducible] updateKemFailOnDeliver

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## Halted send preservation of `Hop2FullInv` -/

theorem transmitRTrackHalted_support_hop2FullInv {ℓ : ℕ} (P : Params Bytes (BitVec 512))
    (K : MlKem) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (qep : ℕ) (x : Party × Plain ℓ × Option (BitVec 512))
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes) (hinv : Hop2FullInv P decT encT st) :
    ∀ z ∈ support (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) x).run st.1).run tr),
      Hop2FullInv P decT encT (z.1.2, st.2) := fun z hz => by
  rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) x st.1 tr hz with hnone | hmem
  · rw [congrArg Prod.snd hnone]; exact hinv
  · exact transmitR_support_hop2FullInv P hcodec hL Dh encPt decT encT hX hdec qep x st hinv z.1 hmem

theorem challRTrackHalted_support_hop2FullInv {ℓ : ℕ} (P : Params Bytes (BitVec 512))
    (K : MlKem) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (qep : ℕ)
    (x : Party × Plain ℓ × Plain ℓ × Option (BitVec 512))
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes) (hinv : Hop2FullInv P decT encT st) :
    ∀ z ∈ support (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) x).run st.1).run tr),
      Hop2FullInv P decT encT (z.1.2, st.2) := fun z hz => by
  rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) x st.1 tr hz with hnone | hmem
  · rw [congrArg Prod.snd hnone]; exact hinv
  · exact challR_support_hop2FullInv P hcodec hL Dh encPt decT encT hX hdec qep x st hinv z.1 hmem

/-! ## Phase 1 receive and step couplings -/

/-- Tracker-halted Phase 2 contract for hybrid transition `k → k + 1` from a shared tracker `tr`. -/
abbrev Hop2TrackPhase2Bound
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ℓ qep : ℕ) (s : BitVec 256) (k : ℕ) (rc_L : RootKey × BitVec 256) : Prop :=
  ∀ (u_chall : BitVec 256) (Q_create : Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ), MakesAtMostQueries oa rem →
    ∀ (sL : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
      (tL : List (Pt × BitVec 256)) (sR : Hop2State Pt ℓ),
    Hop2Phase2Rel P decT encT k u_chall Q_create sL tL sR →
    Hop2WindowInv P sR.1 →
    𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) oa sL tr tL] {true} ≤
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) oa sR tr []] {true} +
      ((5 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_phase1_of_pure_recv {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : RootKey × BitVec 256)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (Q : Party) (c : Bytes) (rc : BitVec 256) (o : Hop2Out Pt ℓ)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s Q c rc st_R post)
    (hrun_L : (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k rc_L) (st_R.1.st Q) c rc).run st_L =
      pure (o, st_L))
    (hrun_R : ∀ u_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
        (st_R.1.st Q) c rc).run st_R = pure (o, st_R))
    (ho_upd : ∀ x ∈ o, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL (tr_next r) tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            (k_oa r) sR (tr_next r) []] {true} + ε) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) (st_R.1.st Q) c rc).run st_L)).run tbl
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          (st_R.1.st Q) c rc).run st_R)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} + ε := by
  rw [hrun_L]
  simp only [hrun_R, simulateQ_pure, StateT.run_pure, pure_bind]
  have hsupp_R : ((o, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) 0)
        (st_R.1.st Q) c rc).run st_R)).run []) := by
    rw [hrun_R 0]; simp [simulateQ_pure, StateT.run_pure]
  have hinv' : Hop2FullInv P decT encT (post o st_R).2 :=
    hpost.preserves_hop2FullInv hrel.inv_R ((o, st_R), []) hsupp_R
  have hpost_rel := hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost o st_L st_R tbl hinv'
    ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
    hrel.lazy_le_k hrel.tbl_eq ho_upd
  rw [hpost_rel.1]
  exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_phase1_of_lazy_pk1 {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : RootKey × BitVec 256)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (c : Bytes) (rc : BitVec 256) (msg : SignalMessage) (T : Pt) (sc : SenderChain)
    (hidx_R : st_R.2.idx (st_R.1.st (partyOfParity (k + 1))).party = some (k + 1))
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind : ((st_R.1.st (partyOfParity (k + 1))).session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : (st_R.1.st (partyOfParity (k + 1))).session.senderChain = some sc)
    (hQ0_R : Dh.dh (st_R.2.coins (st_R.1.st (partyOfParity (k + 1))).party) T ≠ 0)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s (partyOfParity (k + 1)) c rc st_R post)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL (tr_next r) tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            (k_oa r) sR (tr_next r) []] {true} + ε) :
    let Q1 := partyOfParity (k + 1)
    let g := st_R.1.st Q1
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L)).run tbl
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} + ε := by
  intro Q1 g
  have hidx_L : st_L.2.idx g.party = some (k + 1) := by rw [hrel.idx_eq]; exact hidx_R
  have hQ0_L : Dh.dh (st_L.2.coins g.party) T ≠ 0 := by rw [hrel.coins_eq]; exact hQ0_R
  set Q_in := Dh.dh (st_R.2.coins g.party) T
  have hrun_L := hop2Recv_run_at_succ P Dh encT decT k rc_L g c rc st_L msg T sc
    hidx_L htry hfind hdec hT hsc hQ0_L
  rw [hrel.coins_eq] at hrun_L
  have hrun_R : ∀ u_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R =
      (fun r => (hop2OffChainOut P ℓ g msg sc rc r.1, r.2)) <$>
        (hop2Lazy (k + 1) Q_in).run st_R := fun u_chall =>
    hop2Recv_run_of_le_made_none P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) (k + 1)
      g c rc st_R msg T sc hidx_R (by simp) htry hfind hdec hT hsc hQ0_R (hrel.made_k1_none Q_in)
  have h_upd : ∀ u : BitVec 256, ∀ x ∈ hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u,
      x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩ := by
    intro u x hx
    rcases x with ⟨⟨st', t', i', m'⟩, upd⟩
    have hp :=
      hop2OffChainOut_some_props P g msg sc rc u (hrel.inv_R.sender_inv Q1) st' t' i' m' upd hx
    exact Or.inr ⟨rc, hp.1⟩
  rw [hrun_L, simulateQ_lazyImpl_map_evalQuery]
  simp only [hrun_R, simulateQ_lazyImpl_map_hop2Lazy, ← hrel.tbl_eq Q_in]
  cases hlook : tbl.lookup Q_in with
  | some u0 =>
    simp only [pure_bind]
    set o := hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u0
    have hsupp_R : ((o, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) 0) g c rc).run st_R)).run []) := by
      rw [hrun_R 0, simulateQ_lazyImpl_map_hop2Lazy]
      simp only [← hrel.tbl_eq Q_in, hlook, support_pure, Set.mem_singleton_iff]
      rfl
    have hinv' : Hop2FullInv P decT encT (post o st_R).2 :=
      hpost.preserves_hop2FullInv hrel.inv_R ((o, st_R), []) hsupp_R
    have hpost_rel := hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost o st_L st_R tbl hinv'
      ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
      hrel.lazy_le_k hrel.tbl_eq (h_upd u0)
    rw [hpost_rel.1]
    exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)
  | none =>
    simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    rw [evalDist_bind_unif_swap ($ᵗ BitVec 256)]
    refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ ε fun u _ => ?_
    set o := hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u
    set st2_R : Hop2State Pt ℓ :=
      (st_R.1, { st_R.2 with lazy := ((k + 1, Q_in), u) :: st_R.2.lazy })
    have hsupp_R : ((o, st2_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) 0) g c rc).run st_R)).run []) := by
      rw [hrun_R 0, simulateQ_lazyImpl_map_hop2Lazy]
      simp only [← hrel.tbl_eq Q_in, hlook, map_eq_bind_pure_comp, Function.comp_apply,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      exact ⟨u, by simp, rfl⟩
    have hinv' : Hop2FullInv P decT encT (post o st2_R).2 :=
      hpost.preserves_hop2FullInv hrel.inv_R ((o, st2_R), []) hsupp_R
    have hlazy_le_k : ∀ t ≤ k, ∀ Q', st_L.2.lazy.lookup (t, Q') = st2_R.2.lazy.lookup (t, Q') := by
      intro t ht Q'
      have hne : (t, Q') ≠ (k + 1, Q_in) := by
        intro heq; rcases Prod.mk.inj heq with ⟨rfl, _⟩; omega
      dsimp only [st2_R]
      simp [List.lookup, beq_eq_false_iff_ne.mpr hne, hrel.lazy_le_k t ht Q']
    have htbl_eq : ∀ Q', ((Q_in, u) :: tbl).lookup Q' = st2_R.2.lazy.lookup (k + 1, Q') := by
      intro Q'
      by_cases hQ' : Q' = Q_in
      · subst hQ'; dsimp only [st2_R]; simp [List.lookup]
      · have hne : (k + 1, Q') ≠ (k + 1, Q_in) := fun heq => hQ' (Prod.mk.inj heq).2
        dsimp only [st2_R]
        simp [List.lookup, beq_eq_false_iff_ne.mpr hQ', beq_eq_false_iff_ne.mpr hne, hrel.tbl_eq Q']
    have hpost_rel := hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost o st_L st2_R
      ((Q_in, u) :: tbl) hinv'
      ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
      hlazy_le_k htbl_eq (h_upd u)
    rw [hpost_rel.1]
    exact ih' _ _ _ _ hpost_rel.2 (le_refl _)

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_phase1_of_lazy_pk {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : RootKey × BitVec 256)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (c : Bytes) (rc : BitVec 256) (msg : SignalMessage) (T : Pt) (sc : SenderChain)
    (hidx_R : st_R.2.idx (st_R.1.st (partyOfParity k)).party = some k)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind : ((st_R.1.st (partyOfParity k)).session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : (st_R.1.st (partyOfParity k)).session.senderChain = some sc)
    (hQ0_R : Dh.dh (st_R.2.coins (st_R.1.st (partyOfParity k)).party) T ≠ 0)
    (hmade_R : st_R.2.made.lookup (k,
        Dh.dh (st_R.2.coins (st_R.1.st (partyOfParity k)).party) T) = none)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s (partyOfParity k) c rc st_R post)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL (tr_next r) tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            (k_oa r) sR (tr_next r) []] {true} + ε) :
    let Q := partyOfParity k
    let g := st_R.1.st Q
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L)).run tbl
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} + ε := by
  intro Q g
  have hidx_L : st_L.2.idx g.party = some k := by rw [hrel.idx_eq]; exact hidx_R
  have hQ0_L : Dh.dh (st_L.2.coins g.party) T ≠ 0 := by rw [hrel.coins_eq]; exact hQ0_R
  set Q_in := Dh.dh (st_R.2.coins g.party) T
  have hmade_L : st_L.2.made.lookup (k, Dh.dh (st_L.2.coins g.party) T) = none := by
    rw [hrel.made_eq, hrel.coins_eq]; exact hmade_R
  have hrun_L := hop2Recv_run_of_le_made_none P Dh encT decT (hop2HybPrf k rc_L) k
    g c rc st_L msg T sc hidx_L (by simp) htry hfind hdec hT hsc hQ0_L hmade_L
  rw [hrel.coins_eq] at hrun_L
  change (hop2Recv P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L =
      (fun r => (hop2OffChainOut P ℓ g msg sc rc r.1, r.2)) <$> (hop2Lazy k Q_in).run st_L at hrun_L
  have hrun_R : ∀ u_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R =
      (fun r => (hop2OffChainOut P ℓ g msg sc rc r.1, r.2)) <$>
        (hop2Lazy k Q_in).run st_R := fun u_chall =>
    hop2Recv_run_of_le_made_none P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) k
      g c rc st_R msg T sc hidx_R (by simp) htry hfind hdec hT hsc hQ0_R hmade_R
  have h_upd : ∀ u : BitVec 256, ∀ x ∈ hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u,
      x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩ := by
    intro u x hx
    rcases x with ⟨⟨st', t', i', m'⟩, upd⟩
    have hp :=
      hop2OffChainOut_some_props P g msg sc rc u (hrel.inv_R.sender_inv Q) st' t' i' m' upd hx
    exact Or.inr ⟨rc, hp.1⟩
  rw [hrun_L, simulateQ_lazyImpl_map_hop2Lazy]
  simp only [hrun_R, simulateQ_lazyImpl_map_hop2Lazy, hrel.lazy_le_k k (le_refl k) Q_in]
  cases hlook : st_R.2.lazy.lookup (k, Q_in) with
  | some u0 =>
    simp only [pure_bind]
    set o := hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u0
    have hsupp_R : ((o, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) 0) g c rc).run st_R)).run []) := by
      rw [hrun_R 0, simulateQ_lazyImpl_map_hop2Lazy]
      simp only [hlook, support_pure, Set.mem_singleton_iff]
      rfl
    have hinv' : Hop2FullInv P decT encT (post o st_R).2 :=
      hpost.preserves_hop2FullInv hrel.inv_R ((o, st_R), []) hsupp_R
    have hpost_rel := hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost o st_L st_R tbl hinv'
      ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
      hrel.lazy_le_k hrel.tbl_eq (h_upd u0)
    rw [hpost_rel.1]
    exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)
  | none =>
    simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    rw [evalDist_bind_unif_swap ($ᵗ BitVec 256)]
    refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ ε fun u _ => ?_
    set o := hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u
    set st2_L : Hop2State Pt ℓ :=
      (st_L.1, { st_L.2 with lazy := ((k, Q_in), u) :: st_L.2.lazy })
    set st2_R : Hop2State Pt ℓ :=
      (st_R.1, { st_R.2 with lazy := ((k, Q_in), u) :: st_R.2.lazy })
    have hsupp_R : ((o, st2_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) 0) g c rc).run st_R)).run []) := by
      rw [hrun_R 0, simulateQ_lazyImpl_map_hop2Lazy]
      simp only [hlook, map_eq_bind_pure_comp, Function.comp_apply,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      exact ⟨u, by simp, rfl⟩
    have hinv' : Hop2FullInv P decT encT (post o st2_R).2 :=
      hpost.preserves_hop2FullInv hrel.inv_R ((o, st2_R), []) hsupp_R
    have hlazy_le_k : ∀ t ≤ k, ∀ Q', st2_L.2.lazy.lookup (t, Q') = st2_R.2.lazy.lookup (t, Q') := by
      intro t ht Q'
      dsimp only [st2_L, st2_R]
      by_cases heq : ((t, Q') == (k, Q_in)) = true
      · simp [List.lookup, heq]
      · have hne : ((t, Q') == (k, Q_in)) = false := Bool.eq_false_iff.mpr heq
        simp [List.lookup, hne, hrel.lazy_le_k t ht Q']
    have htbl_eq : ∀ Q', tbl.lookup Q' = st2_R.2.lazy.lookup (k + 1, Q') := by
      intro Q'
      have hne : (k + 1, Q') ≠ (k, Q_in) := by
        intro heq; rcases Prod.mk.inj heq with ⟨h1, _⟩; omega
      dsimp only [st2_R]
      simp [List.lookup, beq_eq_false_iff_ne.mpr hne, hrel.tbl_eq Q']
    have hpost_rel := hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost o st2_L st2_R tbl hinv'
      ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
      hlazy_le_k htbl_eq (h_upd u)
    rw [hpost_rel.1]
    exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)

theorem evalDist_runHop2Track_phase1_of_create_pk {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : RootKey × BitVec 256)
    (hph2 : Hop2TrackPhase2Bound P K Dh encPt decT encT ℓ qep s k rc_L)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (c : Bytes) (msg : SignalMessage) (T : Pt) (sc : SenderChain) (ckR : BitVec 256)
    (hidx_R : st_R.2.idx (st_R.1.st (partyOfParity k)).party = some k)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind : ((st_R.1.st (partyOfParity k)).session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true)
    (hdec_T : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : (st_R.1.st (partyOfParity k)).session.senderChain = some sc)
    (hQ0_R : Dh.dh (st_R.2.coins (st_R.1.st (partyOfParity k)).party) T ≠ 0)
    (hmade_R : st_R.2.made.lookup (k,
        Dh.dh (st_R.2.coins (st_R.1.st (partyOfParity k)).party) T) = some ckR)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsDeliverInTransitOrInjectPost (Pt := Pt) P qep s (partyOfParity k) c st_R.1 post)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem_next : ℕ) (hq_k : ∀ r, MakesAtMostQueries (k_oa r) rem_next)
    (d_ih ε : ℝ≥0∞)
    (hd_ih : d_ih + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hd_ph2 : ((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
      ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤ ε)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL (tr_next r) tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            (k_oa r) sR (tr_next r) []] {true} + d_ih) :
    let Q := partyOfParity k
    let g := st_R.1.st Q
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L)).run tbl
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R)).run []
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)] {true} + ε := by
  intro Q g
  have hidx_L : st_L.2.idx g.party = some k := by rw [hrel.idx_eq]; exact hidx_R
  have hQ0_L : Dh.dh (st_L.2.coins g.party) T ≠ 0 := by rw [hrel.coins_eq]; exact hQ0_R
  have hmade_L : st_L.2.made.lookup (k, Dh.dh (st_L.2.coins g.party) T) = some ckR := by
    rw [hrel.made_eq, hrel.coins_eq]; exact hmade_R
  have hrun_L : ∀ rc, (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L =
      (fun u => (hop2CreateOutL P ℓ g msg sc rc ckR u, st_L)) <$>
        evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh rc T) := fun rc =>
    hop2Recv_run_at_create_prf P Dh encPt encT decT hX k rc_L g c rc st_L msg T sc ckR
      hidx_L htry hfind hdec_T hT hsc hQ0_L hmade_L
  have hrun_R : ∀ rc u_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R =
      pure (hop2CreateOutChain P ℓ (k + 1) (Dh.dh rc T) g msg sc rc ckR
        (rootExpand P.C.F (keyToBytes32 u_chall)).2, st_R) := fun rc u_chall =>
    hop2Recv_run_of_succ_eq_made_some P Dh encPt encT decT hX
      (hop2HybPrg P encPt (k + 1) u_chall) k g c rc st_R msg T sc ckR
      hidx_R rfl htry hfind hdec_T hT hsc hQ0_R hmade_R
  have hinv_step : ∀ rc u_chall, badDeliverRc P st_R Q rc = false → Hop2FullInv P decT encT
      (post (hop2CreateOutChain P ℓ (k + 1) (Dh.dh rc T) g msg sc rc ckR
        (rootExpand P.C.F (keyToBytes32 u_chall)).2) st_R).2 := fun rc u_chall hgood_rc => by
    have hsupp : ((hop2CreateOutChain P ℓ (k + 1) (Dh.dh rc T) g msg sc rc ckR
        (rootExpand P.C.F (keyToBytes32 u_chall)).2, st_R), []) ∈
        support ((simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R)).run []) := by
      rw [hrun_R rc u_chall]; simp [simulateQ_pure, StateT.run_pure]
    exact (hpost.withGoodRc hgood_rc).preserves_hop2FullInv hrel.inv_R _ hsupp
  set prev := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
  have hout_L : ∀ rc u, hop2CreateOutL (Pt := Pt) P ℓ g msg sc rc ckR u =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper 0 (steppedSessBase g msg prev ckR) with
      | (.error _, _) => none
      | (.ok m, s_base) => some ((hop2SteppedGhost P g s_base rc
          (rootExpand P.C.F (keyToBytes32 u)).1 (rootExpand P.C.F (keyToBytes32 u)).2,
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨none, rc, none⟩) :=
    fun rc u => hop2CreateOutL_eq_of_tryDecrypt P g msg sc rc ckR u hfind
  have hout_R : ∀ rc ckS, hop2CreateOutChain (Pt := Pt) P ℓ (k + 1) (Dh.dh rc T) g msg sc rc ckR ckS =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper 0 (steppedSessBase g msg prev ckR) with
      | (.error _, _) => none
      | (.ok m, s_base) => some ((hop2SteppedGhost P g s_base rc 0 ckS,
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m),
          some ⟨some (k + 2), rc, some ((k + 1, Dh.dh rc T), ckS)⟩) :=
    fun rc ckS => hop2CreateOutChain_eq_of_tryDecrypt P (k + 1) (Dh.dh rc T) g msg sc rc ckR ckS hfind
  rcases htr0 : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper 0 (steppedSessBase g msg prev ckR) with ⟨r_tr, s_base⟩
  cases r_tr with
  | error e =>
    refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q _ _ d_ih ε hd_ih
      fun rc hgood_rc => ?_
    rw [hrun_L rc]
    simp only [hout_L rc, htr0, map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind,
      simulateQ_lazyImpl_evalQuery, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind, hrun_R rc, hout_R rc]
    have hdisc := congrArg (fun d => d {true})
      (evalDist_runHop2Track_tbl_discard P K Dh encT decT qep s (hop2HybPrf k rc_L)
        (k_oa (post none st_L).1) (post none st_L).2 (tr_next (post none st_L).1) tbl (Dh.dh rc T))
    dsimp only [] at hdisc; rw [hdisc]
    have hinv0 : Hop2FullInv P decT encT (post none st_R).2 := by
      have h0 := hinv_step rc 0 hgood_rc; rw [hout_R rc, htr0] at h0; exact h0
    have hpost_rel := hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost none st_L st_R tbl hinv0
      ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ hrel.lazy_le_k hrel.tbl_eq (fun _ hx => by cases hx)
    rw [hpost_rel.1]; exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)
  | ok m_plain =>
    by_cases hcomm : (∃ r_rec, post = hop2DeliverPost P s Q c g r_rec) ∨
        (post = hop2InjectPost P qep s Q c g ∧ ¬ (qep + 1 < g.epoch + 1) ∧
          st_R.1.trivial 3 ⟨Q.other, g.epoch + 1, msg.counter.toNat + 1⟩ = true)
    · have hM := CryptoGames.LibsignalSM.Proofs.Refinement.libX25519Rel_model hX
      have hbad_le : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
          fun rc => pure (badDeliverRc P st_R Q rc || (tbl.lookup (Dh.dh rc T)).isSome)] {true} ≤
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        (bind_or_evalDist_true_le ($ᵗ BitVec 256) _ _).trans
          (add_le_add (badDeliverRc_prob_le P Dh encPt decT encT hX hdec st_R Q)
            (dh_lookup_isSome_prob_le_hop2CreateCollUnit Dh hM.dh_ne_zero T (fun h0 => hT (Or.inl h0)) tbl))
      have hstep := (bind_apply_le_add_of_evalDist_le_on_good_window ($ᵗ BitVec 256)
        (fun rc => do
          let z ← (simulateQ (lazyImpl (Pt := Pt))
            ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L)).run tbl
          runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
            (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)
        (fun rc => ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => do
          let z ← (simulateQ (lazyImpl (Pt := Pt))
            ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R)).run []
          runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2)
        (fun rc => badDeliverRc P st_R Q rc || (tbl.lookup (Dh.dh rc T)).isSome)
        (((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (fun rc hgood => by
          obtain ⟨hgood_rc, hgood_tbl⟩ := Bool.or_eq_false_iff.mp hgood
          rw [hrun_L rc, simulateQ_lazyImpl_map_evalQuery]
          have hlook : tbl.lookup (Dh.dh rc T) = none := by
            cases h : tbl.lookup (Dh.dh rc T) with | none => rfl | some v => rw [h] at hgood_tbl; cases hgood_tbl
          simp only [pure_bind, hlook, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply,
            bind_assoc, hrun_R rc, simulateQ_pure]
          refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ _ fun u_chall _ => ?_
          rw [hout_L rc u_chall, hout_R rc, htr0]; dsimp only []
          have hinv_u : Hop2FullInv P decT encT
              (post (some ((hop2SteppedGhost P g s_base rc 0 (rootExpand P.C.F (keyToBytes32 u_chall)).2,
                g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain),
                some ⟨some (k + 2), rc, some ((k + 1, Dh.dh rc T),
                  (rootExpand P.C.F (keyToBytes32 u_chall)).2)⟩)) st_R).2 := by
            have h0 := hinv_step rc u_chall hgood_rc; rw [hout_R rc, htr0] at h0; exact h0
          have hph2_rel := hop2Phase2Rel_of_create_commit (s_base := s_base) (rc := rc)
            (u_chall := u_chall) (Q_create := Dh.dh rc T) (m_plain := m_plain) (msg := msg)
            hrel hpost.toIsDeliverOrInjectPost hcomm hinv_u.toHop2GameInv
          rw [hph2_rel.1]
          exact hph2 u_chall (Dh.dh rc T) _ rem_next (hq_k _) _ _ _ _ hph2_rel.2 hinv_u.winInv)).trans
        (add_le_add_right hbad_le _)
      rw [add_assoc] at hstep; exact hstep.trans (add_le_add le_rfl hd_ph2)
    · rcases hpost.toIsDeliverOrInjectPost with ⟨r_rec, hdel⟩ | hinj
      · exact absurd (Or.inl ⟨r_rec, hdel⟩) hcomm
      · have hnc_R : ¬ (¬ (qep + 1 < g.epoch + 1) ∧
            st_R.1.trivial 3 ⟨Q.other, g.epoch + 1, msg.counter.toNat + 1⟩ = true) :=
          fun h => hcomm (Or.inr ⟨hinj, h.1, h.2⟩)
        have hnc_L : ¬ (¬ (qep + 1 < g.epoch + 1) ∧
            st_L.1.trivial 3 ⟨Q.other, g.epoch + 1, msg.counter.toNat + 1⟩ = true) := by
          rw [hrel.st1_eq]; exact hnc_R
        set o_dummy : Hop2Out Pt ℓ :=
          some ((g, g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain), none)
        refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q _ _ d_ih ε hd_ih
          fun rc hgood_rc => ?_
        rw [hrun_L rc]
        have hpost_L_eq : ∀ u, post (some ((hop2SteppedGhost P g s_base rc
            (rootExpand P.C.F (keyToBytes32 u)).1 (rootExpand P.C.F (keyToBytes32 u)).2,
            g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain),
            some ⟨none, rc, none⟩)) st_L = post o_dummy st_L := fun u => by
          rw [hinj]; exact hop2InjectPost_eq_of_not_commit P qep s Q c g _ _ _ _ _ _ _ st_L hnc_L
        have hpost_R_eq : ∀ u_chall, post (some ((hop2SteppedGhost P g s_base rc 0
            (rootExpand P.C.F (keyToBytes32 u_chall)).2,
            g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain),
            some ⟨some (k + 2), rc, some ((k + 1, Dh.dh rc T),
              (rootExpand P.C.F (keyToBytes32 u_chall)).2)⟩)) st_R = post o_dummy st_R := fun u_chall => by
          rw [hinj]; exact hop2InjectPost_eq_of_not_commit P qep s Q c g _ _ _ _ _ _ _ st_R hnc_R
        simp only [hout_L rc, htr0, map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind,
          simulateQ_lazyImpl_evalQuery, simulateQ_pure, StateT.run_bind, StateT.run_pure,
          bind_assoc, pure_bind, hrun_R rc, hout_R rc, hpost_L_eq, hpost_R_eq]
        have hdisc := congrArg (fun d => d {true})
          (evalDist_runHop2Track_tbl_discard P K Dh encT decT qep s (hop2HybPrf k rc_L)
            (k_oa (post o_dummy st_L).1) (post o_dummy st_L).2 (tr_next (post o_dummy st_L).1) tbl (Dh.dh rc T))
        dsimp only [] at hdisc; rw [hdisc]
        have hinv0 : Hop2FullInv P decT encT (post o_dummy st_R).2 := by
          have h0 := hinv_step rc 0 hgood_rc; rw [hout_R rc, htr0, hpost_R_eq 0] at h0; exact h0
        have ho_upd : ∀ x ∈ o_dummy, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩ := fun x hx => by
          simp only [o_dummy, Option.mem_def, Option.some.injEq] at hx; subst hx; exact Or.inl rfl
        have hpost_rel := hop2Phase1Rel_of_post hrel (Or.inr hinj) o_dummy st_L st_R tbl hinv0
          ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ hrel.lazy_le_k hrel.tbl_eq ho_upd
        rw [hpost_rel.1]
        exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)

theorem evalDist_runHop2Track_phase1_recvWithPost_le {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : RootKey × BitVec 256)
    (hph2 : Hop2TrackPhase2Bound P K Dh encPt decT encT ℓ qep s k rc_L)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R) (Q : Party) (c : Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsDeliverInTransitOrInjectPost (Pt := Pt) P qep s Q c st_R.1 post)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem_next : ℕ) (hq_k : ∀ r, MakesAtMostQueries (k_oa r) rem_next) (d_ih ε : ℝ≥0∞)
    (hd_ih : d_ih + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hd_ph2 : ((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
      ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤ ε)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR → tL.length ≤ tbl.length + 1 →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL (tr_next r) tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            (k_oa r) sR (tr_next r) []] {true} + d_ih) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybPrf k rc_L) (st_L.1.st Q) c rc).run st_L
        return post res.1 res.2)).run tbl
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L)
        (k_oa z.1.1) z.1.2 (tr_next z.1.1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          (st_R.1.st Q) c rc).run st_R
        return post res.1 res.2)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa z.1.1) z.1.2 (tr_next z.1.1) z.2)] {true} + ε := by
  have hg_eq : st_L.1.st Q = st_R.1.st Q := by rw [hrel.st1_eq]
  rw [hg_eq]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
    stateT_lift_probComp_run, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
  rw [evalDist_bind_unif_swap ($ᵗ BitVec 256)]
  rcases party_eq_partyOfParity_or_succ k Q with rfl | rfl
  · set Q0 := partyOfParity k; set g := st_R.1.st Q0
    have hp_R : g.party = Q0 := hrel.inv_R.party_eq Q0
    rcases hrel.idx_pk_R with hnone_R | hsome_R
    · refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q0 _ _ d_ih ε hd_ih
        fun rc hgood_rc => ?_
      have hidx_R : st_R.2.idx g.party = none := by rw [hp_R]; exact hnone_R
      have hidx_L : st_L.2.idx g.party = none := by rw [hrel.idx_eq]; exact hidx_R
      refine evalDist_runHop2Track_phase1_of_pure_recv rc_L hrel Q0 c rc _ post
        (hpost.withGoodRc hgood_rc)
        (hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrf k rc_L) g c rc st_L hidx_L)
        (fun u_chall => hop2Recv_run_of_idx_none P Dh encT decT
          (hop2HybPrg P encPt (k + 1) u_chall) g c rc st_R hidx_R)
        (fun x hx => by simp only [Option.mem_def, Option.map_eq_some_iff] at hx; rcases hx with ⟨_, _, rfl⟩; exact Or.inl rfl)
        tr_next k_oa d_ih ih'
    · have hidx_R : st_R.2.idx g.party = some k := by rw [hp_R]; exact hsome_R
      have hidx_L : st_L.2.idx g.party = some k := by rw [hrel.idx_eq]; exact hidx_R
      by_cases hdh : ∃ msg T sc, SignalMessage.tryFrom P.codec c = .ok msg ∧
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true ∧
          decT msg.senderRatchetKey = some T ∧ ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
          g.session.senderChain = some sc ∧ Dh.dh (st_R.2.coins g.party) T ≠ 0
      · rcases hdh with ⟨msg, T, sc, htry, hfind, hdec_T, hT, hsc, hQ0_R⟩
        cases hmade_R : st_R.2.made.lookup (k, Dh.dh (st_R.2.coins g.party) T) with
        | none =>
          refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q0 _ _ d_ih ε hd_ih
            fun rc hgood_rc => evalDist_runHop2Track_phase1_of_lazy_pk rc_L hrel c rc msg T sc
              hidx_R htry hfind hdec_T hT hsc hQ0_R hmade_R post (hpost.withGoodRc hgood_rc) tr_next k_oa d_ih ih'
        | some ckR =>
          exact evalDist_runHop2Track_phase1_of_create_pk hX hdec rc_L hph2 hrel c msg T sc ckR
            hidx_R htry hfind hdec_T hT hsc hQ0_R hmade_R post hpost tr_next k_oa rem_next hq_k d_ih ε hd_ih hd_ph2 ih'
      · refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q0 _ _ d_ih ε hd_ih
          fun rc hgood_rc => ?_
        have hdh_L : ¬ (∃ msg T sc, SignalMessage.tryFrom P.codec c = .ok msg ∧
            (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true ∧
            decT msg.senderRatchetKey = some T ∧ ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
            g.session.senderChain = some sc ∧ Dh.dh (st_L.2.coins g.party) T ≠ 0) := by
          rw [hrel.coins_eq]; exact hdh
        exact evalDist_runHop2Track_phase1_of_pure_recv rc_L hrel Q0 c rc _ post
          (hpost.withGoodRc hgood_rc)
          (hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrf k rc_L) k g c rc st_L hidx_L hdh_L)
          (fun u_chall => hop2Recv_run_of_idx_some_non_dh P Dh encT decT
            (hop2HybPrg P encPt (k + 1) u_chall) k g c rc st_R hidx_R hdh)
          (fun x hx => Or.inl (hop2NonDhOut_snd_none P g c rc x hx)) tr_next k_oa d_ih ih'
  · set Q1 := partyOfParity (k + 1); set g := st_R.1.st Q1
    have hp_R : g.party = Q1 := hrel.inv_R.party_eq Q1
    refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q1 _ _ d_ih ε hd_ih
      fun rc hgood_rc => ?_
    rcases hrel.idx_pk1_R with hnone_R | hsome_R
    · have hidx_R : st_R.2.idx g.party = none := by rw [hp_R]; exact hnone_R
      have hidx_L : st_L.2.idx g.party = none := by rw [hrel.idx_eq]; exact hidx_R
      exact evalDist_runHop2Track_phase1_of_pure_recv rc_L hrel Q1 c rc _ post
        (hpost.withGoodRc hgood_rc)
        (hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrf k rc_L) g c rc st_L hidx_L)
        (fun u_chall => hop2Recv_run_of_idx_none P Dh encT decT
          (hop2HybPrg P encPt (k + 1) u_chall) g c rc st_R hidx_R)
        (fun x hx => by simp only [Option.mem_def, Option.map_eq_some_iff] at hx; rcases hx with ⟨_, _, rfl⟩; exact Or.inl rfl)
        tr_next k_oa d_ih ih'
    · have hidx_R : st_R.2.idx g.party = some (k + 1) := by rw [hp_R]; exact hsome_R
      have hidx_L : st_L.2.idx g.party = some (k + 1) := by rw [hrel.idx_eq]; exact hidx_R
      by_cases hdh : ∃ msg T sc, SignalMessage.tryFrom P.codec c = .ok msg ∧
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true ∧
          decT msg.senderRatchetKey = some T ∧ ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
          g.session.senderChain = some sc ∧ Dh.dh (st_R.2.coins g.party) T ≠ 0
      · rcases hdh with ⟨msg, T, sc, htry, hfind, hdec_T, hT, hsc, hQ0_R⟩
        exact evalDist_runHop2Track_phase1_of_lazy_pk1 rc_L hrel c rc msg T sc
          hidx_R htry hfind hdec_T hT hsc hQ0_R post (hpost.withGoodRc hgood_rc) tr_next k_oa d_ih ih'
      · have hdh_L : ¬ (∃ msg T sc, SignalMessage.tryFrom P.codec c = .ok msg ∧
            (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true ∧
            decT msg.senderRatchetKey = some T ∧ ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
            g.session.senderChain = some sc ∧ Dh.dh (st_L.2.coins g.party) T ≠ 0) := by
          rw [hrel.coins_eq]; exact hdh
        exact evalDist_runHop2Track_phase1_of_pure_recv rc_L hrel Q1 c rc _ post
          (hpost.withGoodRc hgood_rc)
          (hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrf k rc_L) (k + 1) g c rc st_L hidx_L hdh_L)
          (fun u_chall => hop2Recv_run_of_idx_some_non_dh P Dh encT decT
            (hop2HybPrg P encPt (k + 1) u_chall) (k + 1) g c rc st_R hidx_R hdh)
          (fun x hx => Or.inl (hop2NonDhOut_snd_none P g c rc x hx)) tr_next k_oa d_ih ih'

theorem evalDist_runHop2Track_phase1_deliver_le {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : RootKey × BitVec 256)
    (hph2 : Hop2TrackPhase2Bound P K Dh encPt decT encT ℓ qep s k rc_L)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (tr : KemFailSessionTrack P.C.F Bytes) (Q : Party) (c : Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem_next : ℕ) (hq_k : ∀ r, MakesAtMostQueries (k_oa r) rem_next)
    (d_ih ε : ℝ≥0∞)
    (hd_ih : d_ih + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hd_ph2 : ((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
      ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤ ε)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL
          (updateKemFailOnDeliver P.C.F K tr (Q, c) r) tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (k_oa r) sR
            (updateKemFailOnDeliver P.C.F K tr (Q, c) r) []] {true} + d_ih) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrf k rc_L) (Q, c)).run st_L)).run tbl
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa z.1.1) z.1.2
        (updateKemFailOnDeliver P.C.F K tr (Q, c) z.1.1) z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrg P encPt (k + 1) u_chall) (Q, c)).run st_R)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (k_oa z.1.1) z.1.2
        (updateKemFailOnDeliver P.C.F K tr (Q, c) z.1.1) z.2)] {true} + ε := by
  have hwin_eq : st_L.1.win = st_R.1.win := by rw [hrel.st1_eq]
  have hin_eq : st_L.1.inTransit Q.other c = st_R.1.inTransit Q.other c := by rw [hrel.st1_eq]
  have hd_le : d_ih ≤ ε := le_self_add.trans hd_ih
  by_cases hwin : st_R.1.win = true
  · have hwin_L : st_L.1.win = true := hwin_eq.trans hwin
    have hL : (hop2Deliver P Dh encT decT s (hop2HybPrf k rc_L) (Q, c)).run st_L = pure (none, st_L) := by
      unfold hop2Deliver; simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin_L, ↓reduceIte, StateT.run_pure]
    have hR : ∀ u_chall, (hop2Deliver P Dh encT decT s (hop2HybPrg P encPt (k + 1) u_chall) (Q, c)).run st_R =
        pure (none, st_R) := fun _ => by
      unfold hop2Deliver; simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte, StateT.run_pure]
    simp only [hL, hR, simulateQ_pure, StateT.run_pure, pure_bind]
    exact (ih' none st_L tbl st_R hrel (Nat.le_succ _)).trans (add_le_add le_rfl hd_le)
  · have hwin_R : st_R.1.win = false := Bool.eq_false_iff.mpr hwin
    have hwin_L : st_L.1.win = false := hwin_eq.trans hwin_R
    cases hin_R : st_R.1.inTransit Q.other c with
    | none =>
      have hin_L : st_L.1.inTransit Q.other c = none := hin_eq.trans hin_R
      have hL : (hop2Deliver P Dh encT decT s (hop2HybPrf k rc_L) (Q, c)).run st_L = pure (none, st_L) := by
        unfold hop2Deliver
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin_L, Bool.false_eq_true, ↓reduceIte, hin_L, StateT.run_pure]
      have hR : ∀ u_chall, (hop2Deliver P Dh encT decT s (hop2HybPrg P encPt (k + 1) u_chall) (Q, c)).run st_R =
          pure (none, st_R) := fun _ => by
        unfold hop2Deliver
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin_R, Bool.false_eq_true, ↓reduceIte, hin_R, StateT.run_pure]
      simp only [hL, hR, simulateQ_pure, StateT.run_pure, pure_bind]
      exact (ih' none st_L tbl st_R hrel (Nat.le_succ _)).trans (add_le_add le_rfl hd_le)
    | some r =>
      have hin_L : st_L.1.inTransit Q.other c = some r := hin_eq.trans hin_R
      rw [hop2Deliver_run_eq_post P Dh encT decT s (hop2HybPrf k rc_L) Q c st_L r hwin_L hin_L]
      simp only [hop2Deliver_run_eq_post P Dh encT decT s _ Q c st_R r hwin_R hin_R]
      have hpost_eq : hop2DeliverPost (Pt := Pt) (ℓ := ℓ) P s Q c (st_L.1.st Q) r =
          hop2DeliverPost (Pt := Pt) (ℓ := ℓ) P s Q c (st_R.1.st Q) r := by rw [hrel.st1_eq]
      simp only [hpost_eq]
      exact evalDist_runHop2Track_phase1_recvWithPost_le (qep := qep) hX hdec rc_L hph2 hrel Q c
        (hop2DeliverPost P s Q c (st_R.1.st Q) r) (Or.inl ⟨r, hin_R, rfl⟩)
        (updateKemFailOnDeliver P.C.F K tr (Q, c)) k_oa rem_next hq_k d_ih ε hd_ih hd_ph2 ih'

theorem evalDist_runHop2Track_phase1_inject_le {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : RootKey × BitVec 256)
    (hph2 : Hop2TrackPhase2Bound P K Dh encPt decT encT ℓ qep s k rc_L)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (tr : KemFailSessionTrack P.C.F Bytes) (Q : Party) (c : Bytes)
    (k_oa : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem_next : ℕ) (hq_k : ∀ r, MakesAtMostQueries (k_oa r) rem_next)
    (d_ih ε : ℝ≥0∞)
    (hd_ih : d_ih + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hd_ph2 : ((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
      ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤ ε)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tr tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            (k_oa r) sR tr []] {true} + d_ih) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrf k rc_L) (Q, c)).run st_L)).run tbl
      runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa z.1.1) z.1.2 tr z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (Q, c)).run st_R)).run []
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
        (k_oa z.1.1) z.1.2 tr z.2)] {true} + ε := by
  have hg_eq : (st_L.1.win || (st_L.1.inTransit Q.other c).isSome || !(st_L.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
      (st_R.1.win || (st_R.1.inTransit Q.other c).isSome || !(st_R.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := by rw [hrel.st1_eq]
  have hd_le : d_ih ≤ ε := le_self_add.trans hd_ih
  by_cases hg : (st_R.1.win || (st_R.1.inTransit Q.other c).isSome || !(st_R.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · have hg_L : (st_L.1.win || (st_L.1.inTransit Q.other c).isSome || !(st_L.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hg_eq.trans hg
    have hL : (hop2Inject P Dh encT decT qep s (hop2HybPrf k rc_L) (Q, c)).run st_L = pure (none, st_L) := by
      unfold hop2Inject; simp only [StateT.run_bind, StateT.run_get, pure_bind, hg_L, ↓reduceIte, StateT.run_pure]
    have hR : ∀ u_chall, (hop2Inject P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (Q, c)).run st_R =
        pure (none, st_R) := fun _ => by
      unfold hop2Inject; simp only [StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte, StateT.run_pure]
    simp only [hL, hR, simulateQ_pure, StateT.run_pure, pure_bind]
    exact (ih' none st_L tbl st_R hrel (Nat.le_succ _)).trans (add_le_add le_rfl hd_le)
  · have hg_R : (st_R.1.win || (st_R.1.inTransit Q.other c).isSome || !(st_R.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
    have hg_L : (st_L.1.win || (st_L.1.inTransit Q.other c).isSome || !(st_L.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := hg_eq.trans hg_R
    rw [hop2Inject_run_eq_post P Dh encT decT qep s (hop2HybPrf k rc_L) Q c st_L hg_L]
    simp only [hop2Inject_run_eq_post P Dh encT decT qep s _ Q c st_R hg_R]
    have hpost_eq : hop2InjectPost (Pt := Pt) (ℓ := ℓ) P qep s Q c (st_L.1.st Q) =
        hop2InjectPost (Pt := Pt) (ℓ := ℓ) P qep s Q c (st_R.1.st Q) := by rw [hrel.st1_eq]
    simp only [hpost_eq]
    exact evalDist_runHop2Track_phase1_recvWithPost_le hX hdec rc_L hph2 hrel Q c
      (hop2InjectPost P qep s Q c (st_R.1.st Q)) (Or.inr rfl) (fun _ => tr)
      k_oa rem_next hq_k d_ih ε hd_ih hd_ph2 ih'

/-! ## Phase 1 coupling -/

theorem evalDist_runHop2Track_phase1_le {ℓ : ℕ} {P : Params Bytes (BitVec 512)} {K : MlKem}
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (s : BitVec 256) (k : ℕ) (rc_L : RootKey × BitVec 256)
    (hph2 : Hop2TrackPhase2Bound P K Dh encPt decT encT ℓ qep s k rc_L)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ) (hq : MakesAtMostQueries oa rem)
    (st_L : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (st_R : Hop2State Pt ℓ)
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R) :
    𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) oa st_L tr tbl] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          oa st_R tr []] {true} +
      ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem st_L tr tbl st_R with
  | pure a =>
    simp only [runHop2Track_pure, evalDist_unif_bind_const, hrel.bad_eq]
    exact le_self_add
  | query_bind t k_oa ih =>
    rw [MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
    rw [runHop2Track_bind_query]
    simp only [runHop2Track_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2Track_unif]
      simp only [runHop2Track_unif]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      exact bind_evalDist_true_le_of_support _ _ _ _ fun a _ =>
        ih a rem (by simpa [MakesAtMostQueries] using hq.2 a) st_L tr tbl st_R hrel
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_hop2LiftTrackHalted', hrel.st1_eq]
      simp only [runHop2Track_hop2LiftTrackHalted']
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
      have hinv' := transmitRTrackHalted_support_hop2FullInv P K hcodec hL Dh encPt decT encT
        hX hdec qep y_tr st_R tr hrel.inv_R r hr
      have hle : (((6 * (rem - 1) + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r.1.1)
        (r.1.2, st_L.2) r.2 tbl (r.1.2, st_R.2) (hrel.of_st1_step r.1.2 hinv')).trans
        (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_hop2LiftTrackHalted', hrel.st1_eq]
      simp only [runHop2Track_hop2LiftTrackHalted']
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
      have hinv' := challRTrackHalted_support_hop2FullInv P K hcodec hL Dh encPt decT encT
        hX hdec qep y_ch st_R tr hrel.inv_R r hr
      have hle : (((6 * (rem - 1) + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r.1.1)
        (r.1.2, st_L.2) r.2 tbl (r.1.2, st_R.2) (hrel.of_st1_step r.1.2 hinv')).trans
        (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      have hL_eq := congrArg (fun x => 𝒟[x] {true})
        (runHop2Track_deliver P K Dh encT decT qep s (hop2HybPrf k rc_L) (Q, c) k_oa st_L tr tbl)
      have hR_eq := congrArg (fun f => 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= f] {true})
        (funext fun u_chall => runHop2Track_deliver P K Dh encT decT qep s
          (hop2HybPrg P encPt (k + 1) u_chall) (Q, c) k_oa st_R tr [])
      refine hL_eq.trans_le (le_trans ?_ (add_le_add hR_eq.symm.le le_rfl))
      have hd_ih : ((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega :
          6 * (rem - 1) + (tbl.length + 1) + 5 ≤ 6 * rem + tbl.length)) zero_le
      have hd_ph2 : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul, ← add_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega :
          5 * (rem - 1) + (5 + tbl.length) ≤ 6 * rem + tbl.length)) zero_le
      refine evalDist_runHop2Track_phase1_deliver_le (qep := qep) hX hdec rc_L hph2 hrel tr Q c k_oa
        (rem - 1) (fun r => by simpa [MakesAtMostQueries] using hq.2 r)
        (((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) hd_ih hd_ph2
        (fun r sL tL sR hrel' hlen => ?_)
      have hle : (((6 * (rem - 1) + tL.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r)
        sL (updateKemFailOnDeliver P.C.F K tr (Q, c) r) tL sR hrel').trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_noTrack]; simp only [runHop2Track_noTrack]
      have hd_ih : ((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega :
          6 * (rem - 1) + (tbl.length + 1) + 5 ≤ 6 * rem + tbl.length)) zero_le
      have hd_ph2 : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul, ← add_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega :
          5 * (rem - 1) + (5 + tbl.length) ≤ 6 * rem + tbl.length)) zero_le
      refine evalDist_runHop2Track_phase1_inject_le hX hdec rc_L hph2 hrel tr Q c k_oa
        (rem - 1) (fun r => by simpa [MakesAtMostQueries] using hq.2 r)
        (((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) hd_ih hd_ph2
        (fun r sL tL sR hrel' hlen => ?_)
      have hle : (((6 * (rem - 1) + tL.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r)
        sL tr tL sR hrel').trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2ImplTrackHalted]
      have hL_eq := congrArg (fun x => 𝒟[x] {true})
        (runHop2Track_corr P K Dh encT decT qep s (hop2HybPrf k rc_L) y_corr k_oa st_L tr tbl)
      have hR_eq := congrArg (fun f => 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= f] {true})
        (funext fun u_chall => runHop2Track_corr P K Dh encT decT qep s
          (hop2HybPrg P encPt (k + 1) u_chall) y_corr k_oa st_R tr [])
      refine hL_eq.trans_le (le_trans ?_ (add_le_add hR_eq.symm.le le_rfl))
      rw [hrel.st1_eq, OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
      have hinv' := corrR_support_hop2FullInv P decT encT y_corr st_R hrel.inv_R r hr
      have hle : (((6 * (rem - 1) + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r.1)
        (r.2, st_L.2) tr tbl (r.2, st_R.2) (hrel.of_st1_step r.2 hinv')).trans
        (add_le_add le_rfl hle)

end Phase1

end Computational.Proofs.E2E.HaltedSpkHop2Phase1
