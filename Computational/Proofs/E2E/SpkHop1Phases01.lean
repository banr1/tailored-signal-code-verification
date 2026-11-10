/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1Phases01A

@[expose] public section

/-!
# Hop 2 Phase 0 and the PRF-to-PRG Step

Couples `hop2HybPrf k` and `hop2HybPrg (k + 1)` in Phase 0 (before table `k` is created), bounds
the random-function world of `hop2PrfRedK k` by the real PRG experiment of `hop2PrgRedK (k + 1)`,
and defines the reference receive steps and `SpkRefInv` invariant for `h_init`.
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

section Phase0

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

/-! ## Phase 0 -/

/-- Phase 0 invariant at stage `m < k`, before table `k` is created. -/
structure Hop2Phase0Inv {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (m : ℕ) (st : Hop2State Pt ℓ) : Prop where
  inv : Hop2FullInv P decT encT st
  idx_pm : st.2.idx (partyOfParity m) = none ∨ st.2.idx (partyOfParity m) = some m
  idx_pm1 : st.2.idx (partyOfParity (m + 1)) = none ∨ st.2.idx (partyOfParity (m + 1)) = some (m +
      1)
  made_gt : ∀ t > m, ∀ Q, st.2.made.lookup (t, Q) = none
  lazy_gt : ∀ t > m + 1, ∀ Q, st.2.lazy.lookup (t, Q) = none

omit [Zero Pt] [SampleableType Pt] in
theorem Hop2Phase0Inv.of_st1_step {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {m : ℕ} {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (st1' : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hinv' : Hop2FullInv P decT encT (st1', st.2)) :
    Hop2Phase0Inv P decT encT m (st1', st.2) :=
  ⟨hinv', h0.idx_pm, h0.idx_pm1, h0.made_gt, h0.lazy_gt⟩

omit [Zero Pt] [SampleableType Pt] in
theorem hop2Phase1Rel_of_phase0_self {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (k : ℕ) (st : Hop2State Pt ℓ)
    (h0 : Hop2Phase0Inv P decT encT k st)
    (hlazy_k1 : ∀ Q, st.2.lazy.lookup (k + 1, Q) = none) :
    Hop2Phase1Rel P decT encT k st [] st :=
  ⟨h0.inv, rfl, rfl, rfl, rfl, rfl, h0.idx_pm, h0.idx_pm1,
   h0.made_gt (k + 1) (Nat.lt_succ_self k), fun _ _ _ => rfl,
   fun Q => (hlazy_k1 Q).symm⟩

omit [Zero Pt] [SampleableType Pt] in
theorem hop2Phase0Inv_init {ℓ : ℕ} (P : Params Bytes PQC)
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
    Hop2Phase0Inv P decT encT 0 (initSt, aux0) := by
  intro spk sessA stA stB initSt aux0
  refine ⟨hop2FullInv_init P decT encT b ck0 x alice pqr ck1 I0,
    Or.inr rfl, Or.inr rfl, ?_, fun _ _ _ => rfl⟩
  intro t ht Q
  have hne : (t, Q) ≠ (0, I0) := by
    intro h; rcases Prod.mk.inj h with ⟨h1, _⟩; omega
  dsimp only [aux0]
  simp [List.lookup, beq_eq_false_iff_ne.mpr hne]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem IsDeliverOrInjectPost.aux_cases {ℓ : ℕ} {P : Params Bytes PQC}
    {qep : ℕ} {s : BitVec 256} {Q : Party} {c : Bytes} {g₀ : GhostState Bytes}
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverOrInjectPost (Pt := Pt) P qep s Q c g₀ post)
    (o : Hop2Out Pt ℓ) (st2 : Hop2State Pt ℓ) :
    (post o st2).2.2.lazy = st2.2.lazy ∧
    (((post o st2).2.2.idx = st2.2.idx ∧ (post o st2).2.2.made = st2.2.made) ∨
      ∃ st' t' i' m' u, o = some ((st', t', i', m'), u) ∧
        (post o st2).2.2.idx = (hop2Commit st2.2 Q u).idx ∧
        (post o st2).2.2.made = (hop2Commit st2.2 Q u).made) := by
  rcases hpost with ⟨r, rfl⟩ | rfl
  · cases o with
    | none => exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | some val =>
      rcases val with ⟨⟨st', t', i', m'⟩, u⟩
      dsimp only [hop2DeliverPost]
      refine ⟨?_, Or.inr ⟨st', t', i', m', u, rfl, rfl, rfl⟩⟩
      cases u <;> rfl
  · cases o with
    | none => exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | some val =>
      rcases val with ⟨⟨st', t', i', m'⟩, u⟩
      dsimp only [hop2InjectPost]
      by_cases hqep : qep + 1 < t'
      · simp [hqep]
      · by_cases htriv : st2.1.trivial 3 ⟨Q.other, t', i'⟩ = true
        · simp only [hqep, ↓reduceIte, htriv]
          refine ⟨?_, Or.inr ⟨st', t', i', m', u, rfl, ?_, ?_⟩⟩
          · cases u <;> rfl
          · cases u <;> rfl
          · cases u <;> rfl
        · have htrivF : st2.1.trivial 3 ⟨Q.other, t', i'⟩ = false := Bool.eq_false_iff.mpr htriv
          simp [hqep, htrivF]

omit [Zero Pt] [SampleableType Pt] in
theorem hop2Phase0Inv_of_post {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {m : ℕ} {Q : Party} {c : Bytes}
    {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverOrInjectPost (Pt := Pt) P qep s Q c (st.1.st Q) post)
    (o : Hop2Out Pt ℓ) (st2 : Hop2State Pt ℓ)
    (hinv' : Hop2FullInv P decT encT (post o st2).2)
    (hidx2 : st2.2.idx = st.2.idx)
    (hmade2 : st2.2.made = st.2.made)
    (hlazy2 : ∀ t > m + 1, ∀ Q', st2.2.lazy.lookup (t, Q') = none)
    (h_upd : ∀ x ∈ o, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩) :
    Hop2Phase0Inv P decT encT m (post o st2).2 := by
  obtain ⟨hlazy_post, hcases⟩ := hpost.aux_cases o st2
  have hmade_post : (post o st2).2.2.made = st.2.made := by
    rcases hcases with ⟨_, hm⟩ | ⟨st', t', i', m', u, ho, _, hm⟩
    · exact hm.trans hmade2
    · rw [hm]
      rcases h_upd ((st', t', i', m'), u) ho with rfl | ⟨rc', rfl⟩ <;> exact hmade2
  have hidx_cases : ∀ R : Party,
      (post o st2).2.2.idx R = st.2.idx R ∨ (post o st2).2.2.idx R = none := by
    intro R
    rcases hcases with ⟨hi, _⟩ | ⟨st', t', i', m', u, ho, hi, _⟩
    · exact Or.inl (by rw [hi, hidx2])
    · rw [hi]
      rcases h_upd ((st', t', i', m'), u) ho with rfl | ⟨rc', rfl⟩
      · exact Or.inl (by simp [hop2Commit, hidx2])
      · by_cases hR : R = Q
        · subst hR; exact Or.inr (by simp [hop2Commit])
        · exact Or.inl (by simp [hop2Commit, Function.update_of_ne hR, hidx2])
  refine ⟨hinv', ?_, ?_,
    fun t ht Q' => by rw [hmade_post]; exact h0.made_gt t ht Q',
    fun t ht Q' => by rw [hlazy_post]; exact hlazy2 t ht Q'⟩
  · rcases hidx_cases (partyOfParity m) with heq | hnone
    · rw [heq]; exact h0.idx_pm
    · exact Or.inl hnone
  · rcases hidx_cases (partyOfParity (m + 1)) with heq | hnone
    · rw [heq]; exact h0.idx_pm1
    · exact Or.inl hnone

omit [Zero Pt] [SampleableType Pt] in
theorem hop2Phase0Inv_of_create_commit {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {m : ℕ} {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (rc : BitVec 256) (Q_out : Pt) (ckS : BitVec 256)
    (st_next : Hop2State Pt ℓ)
    (hinv' : Hop2FullInv P decT encT st_next)
    (hlazy_next : st_next.2.lazy = st.2.lazy)
    (hidx_next : st_next.2.idx = (hop2Commit st.2 (partyOfParity m)
      (some ⟨some (m + 2), rc, some ((m + 1, Q_out), ckS)⟩)).idx)
    (hmade_next : st_next.2.made = (hop2Commit st.2 (partyOfParity m)
      (some ⟨some (m + 2), rc, some ((m + 1, Q_out), ckS)⟩)).made) :
    Hop2Phase0Inv P decT encT (m + 1) st_next ∧
    (∀ t > m + 1, ∀ Q', st_next.2.lazy.lookup (t, Q') = none) := by
  have hlazy_gt : ∀ t > m + 1, ∀ Q', st_next.2.lazy.lookup (t, Q') = none := by
    intro t ht Q'; rw [hlazy_next]; exact h0.lazy_gt t ht Q'
  refine ⟨⟨hinv', ?_, ?_, ?_, fun t ht Q' => hlazy_gt t (by omega) Q'⟩, hlazy_gt⟩
  · have hne : partyOfParity (m + 1) ≠ partyOfParity m := partyOfParity_succ_ne m
    have hidx_eq : st_next.2.idx (partyOfParity (m + 1)) = st.2.idx (partyOfParity (m + 1)) := by
      rw [hidx_next]; simp [hop2Commit, Function.update_of_ne hne]
    rw [hidx_eq]; exact h0.idx_pm1
  · have hpar : partyOfParity ((m + 1) + 1) = partyOfParity m := partyOfParity_add_two m
    rw [hpar, hidx_next]
    exact Or.inr (by simp [hop2Commit])
  · intro t ht Q'
    have hne : (t, Q') ≠ (m + 1, Q_out) := by
      intro h; rcases Prod.mk.inj h with ⟨h1, _⟩; omega
    rw [hmade_next]
    simp [hop2Commit, List.lookup, beq_eq_false_iff_ne.mpr hne, h0.made_gt t (by omega) Q']

omit [SampleableType Pt] in
theorem simulateQ_lazyImpl_hop2Recv_of_le_made_none {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (t : ℕ)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : SenderChain)
    (hidx : st.2.idx g.party = some t)
    (htle : t ≤ h.k)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : g.session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0)
    (hmade : st.2.made.lookup (t, Dh.dh (st.2.coins g.party) T) = none)
    (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt)) ((hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st)).run tbl =
      let Q_in := Dh.dh (st.2.coins g.party) T
      match st.2.lazy.lookup (t, Q_in) with
      | some u => pure ((hop2OffChainOut P ℓ g msg sc rc u, st), tbl)
      | none => (fun u => ((hop2OffChainOut P ℓ g msg sc rc u,
          (st.1, { st.2 with lazy := ((t, Q_in), u) :: st.2.lazy })), tbl)) <$>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
  rw [hop2Recv_run_of_le_made_none P Dh encT decT h t g c rc st msg T sc
    hidx htle htry hfind hdec hT hsc hQ0 hmade, simulateQ_lazyImpl_map_hop2Lazy]
  rfl

theorem simulateQ_lazyImpl_hop2Recv_of_succ_lt_made_some {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (h : Hop2Hyb Pt) (t : ℕ)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : SenderChain) (ckR : BitVec 256)
    (hidx : st.2.idx g.party = some t)
    (htlt : t + 1 < h.k)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : g.session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0)
    (hmade : st.2.made.lookup (t, Dh.dh (st.2.coins g.party) T) = some ckR)
    (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt)) ((hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st)).run tbl =
      (fun ckS => ((hop2CreateOutChain P ℓ (t + 1) (Dh.dh rc T) g msg sc rc ckR ckS, st), tbl)) <$>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
  rw [hop2Recv_run_of_succ_lt_made_some P Dh encPt encT decT hX h t g c rc st msg T sc ckR
    hidx htlt htry hfind hdec hT hsc hQ0 hmade]
  simp [map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind,
    simulateQ_lazyImpl_hop2Unif, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]

theorem evalDist_hop2Recv_create_of_post_const {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (qep : ℕ) (s : BitVec 256) (h : Hop2Hyb Pt) (m : ℕ)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : SenderChain) (ckR : BitVec 256)
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
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (o0 : Hop2Out Pt ℓ)
    (hconst : ∀ ckS, post (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS) st =
        post o0 st)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT h g c rc).run st)).run []
      runHop2 P Dh encT decT qep s h (k_oa (post z.1.1 z.1.2).1) (post z.1.1 z.1.2).2 z.2)] {true} =
    𝒟[runHop2 P Dh encT decT qep s h (k_oa (post o0 st).1) (post o0 st).2 []] {true} := by
  rcases Nat.lt_or_eq_of_le hmle with hlt | heq
  · rw [simulateQ_lazyImpl_hop2Recv_of_succ_lt_made_some P Dh encPt encT decT hX h m
      g c rc st msg T sc ckR hidx hlt htry hfind hdec hT hsc hQ0 hmade []]
    simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, hconst]
    exact evalDist_unif_bind_const _
  · rw [hop2Recv_run_of_succ_eq_made_some P Dh encPt encT decT hX h m
      g c rc st msg T sc ckR hidx heq htry hfind hdec hT hsc hQ0 hmade]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, hconst]

omit [SampleableType Pt] in
theorem evalDist_runHop2_phase0_of_pure_recv {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k) (r_L : Ratchet.RootKey)
    {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes) (rc : BitVec 256)
    (o : Hop2Out Pt ℓ)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s Q c rc st post)
    (hrun_L : ∀ c_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k (r_L, c_chall)) (st.1.st Q) c rc).run st =
      pure (o, st))
    (hrun_R : ∀ u_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k +
          1) u_chall) (st.1.st Q) c rc).run st =
      pure (o, st))
    (h_upd : ∀ x ∈ o, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + ε) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) (st.1.st Q) c rc).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) (st.1.st Q) c rc).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} + ε := by
  have hsupp_R : ((o, st), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
          1) 0) (st.1.st Q) c rc).run st)).run []) := by
    rw [hrun_R 0, simulateQ_pure, StateT.run_pure]
    simp only [support_pure, Set.mem_singleton_iff]
  have hinv' : Hop2FullInv P decT encT (post o st).2 :=
    hpost.preserves_hop2FullInv h0.inv ((o, st), []) hsupp_R
  have h0' :=
      hop2Phase0Inv_of_post h0 hpost.toIsDeliverOrInjectPost o st hinv' rfl rfl h0.lazy_gt h_upd
  simp only [hrun_L, hrun_R, simulateQ_pure, StateT.run_pure, pure_bind]
  exact ih' (post o st).1 m (post o st).2 hm h0'

omit [SampleableType Pt] in
theorem evalDist_runHop2_phase0_of_lazy {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k m t : ℕ} (hm : m < k) (ht : t ≤ m + 1)
    (r_L : Ratchet.RootKey) {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes) (rc : BitVec 256) (msg : SignalMessage) (T : Pt) (sc : SenderChain)
    (hidx : st.2.idx (st.1.st Q).party = some t)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind : ((st.1.st Q).session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : (st.1.st Q).session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins (st.1.st Q).party) T ≠ 0)
    (hmade : st.2.made.lookup (t, Dh.dh (st.2.coins (st.1.st Q).party) T) = none)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s Q c rc st post)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + ε) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) (st.1.st Q) c rc).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) (st.1.st Q) c rc).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} + ε := by
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
    fun c_chall => simulateQ_lazyImpl_hop2Recv_of_le_made_none P Dh encT decT (hop2HybPrf k (r_L,
        c_chall)) t
      g c rc st msg T sc hidx htk htry hfind hdec hT hsc hQ0 hmade []
  have hrun_R : ∀ u_chall,
      (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) g c rc).run st)).run [] =
      match st.2.lazy.lookup (t, Q_in) with
      | some u => pure ((hop2OffChainOut P ℓ g msg sc rc u, st), [])
      | none => (fun u => ((hop2OffChainOut P ℓ g msg sc rc u,
          (st.1, { st.2 with lazy := ((t, Q_in), u) :: st.2.lazy })), [])) <$>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :=
    fun u_chall => simulateQ_lazyImpl_hop2Recv_of_le_made_none P Dh encT decT (hop2HybPrg P encPt (k
        + 1) u_chall) t
      g c rc st msg T sc hidx htk1 htry hfind hdec hT hsc hQ0 hmade []
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
        hop2Phase0Inv_of_post h0 hpost.toIsDeliverOrInjectPost o st hinv' rfl rfl h0.lazy_gt (h_upd
        u0)
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

theorem evalDist_runHop2_phase0_of_create_pm {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT)
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k)
    (r_L : Ratchet.RootKey) {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (c : Bytes) (rc : BitVec 256) (msg : SignalMessage) (T : Pt) (sc : SenderChain) (ckR :
        BitVec 256)
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
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s (partyOfParity m) c rc st post)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (ε : ℝ≥0∞)
    (hph1 : ∀ c_chall r st', Hop2Phase1Rel P decT encT k st' [] st' →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + ε)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + ε) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L,
            c_chall)) (st.1.st (partyOfParity m)) c rc).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) (st.1.st (partyOfParity m)) c rc).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} + ε := by
  set Q := partyOfParity m
  set g := st.1.st Q
  have hmk : m + 1 ≤ k := by omega
  have hmk1 : m + 1 < k + 1 := by omega
  have hrun_R : ∀ u_chall,
      (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) g c rc).run st)).run [] =
      (fun ckS => ((hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS, st), [])) <$>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :=
    fun u_chall => simulateQ_lazyImpl_hop2Recv_of_succ_lt_made_some P Dh encPt encT decT hX
      (hop2HybPrg P encPt (k +
          1) u_chall) m g c rc st msg T sc ckR hidx hmk1 htry hfind hdec hT hsc hQ0 hmade []
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
  have hout_eq : ∀ ckS, hop2CreateOutChain (Pt := Pt) P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper 0 (steppedSessBase g msg prev ckR) with
      | (.error _, _) => none
      | (.ok m_plain, s_base) =>
        some ((hop2SteppedGhost P g s_base rc 0 ckS,
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain),
          some ⟨some (m + 2), rc, some ((m + 1, Dh.dh rc T), ckS)⟩) :=
    fun ckS => hop2CreateOutChain_eq_of_tryDecrypt P (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS hfind
  rcases htr0 : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper 0 (steppedSessBase g msg prev ckR) with ⟨r_tr, s_base⟩
  cases r_tr with
  | error _ =>
    have hconst : ∀ ckS, post (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS) st =
        post none st := fun ckS => by rw [hout_eq ckS, htr0]
    have hL_eq : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc).run st)).run []
        runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa (post z.1.1 z.1.2).1)
          (post z.1.1 z.1.2).2 z.2)] {true} =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
          (k_oa (post none st).1) (post none st).2 []] {true} :=
      bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun c_chall =>
        evalDist_hop2Recv_create_of_post_const P Dh encPt encT decT hX qep s
          (hop2HybPrf k (r_L, c_chall)) m g c rc st msg T sc ckR
          hidx hmk htry hfind hdec hT hsc hQ0 hmade post none hconst k_oa
    have hR_eq : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st)).run []
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa (post z.1.1 z.1.2).1)
          (post z.1.1 z.1.2).2 z.2)] {true} =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          (k_oa (post none st).1) (post none st).2 []] {true} :=
      bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun u_chall =>
        evalDist_hop2Recv_create_of_post_const P Dh encPt encT decT hX qep s
          (hop2HybPrg P encPt (k + 1) u_chall) m g c rc st msg T sc ckR
          hidx (Nat.le_of_lt hmk1) htry hfind hdec hT hsc hQ0 hmade post none hconst k_oa
    rw [hL_eq, hR_eq]
    have hinv' : Hop2FullInv P decT encT (post none st).2 := by
      have h1 := hpost.preserves_hop2FullInv h0.inv _ (hsupp_R 0)
      rw [hout_eq 0, htr0] at h1
      exact h1
    have h0' :=
        hop2Phase0Inv_of_post h0 hpost.toIsDeliverOrInjectPost none st hinv' rfl rfl h0.lazy_gt (by
        simp)
    exact ih' (post none st).1 m (post none st).2 hm h0'
  | ok m_plain =>
    have ho_some : ∀ ckS, hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS =
        some ((hop2SteppedGhost P g s_base rc 0 ckS,
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain),
          some ⟨some (m + 2), rc, some ((m + 1, Dh.dh rc T), ckS)⟩) :=
      fun ckS => by rw [hout_eq ckS, htr0]
    by_cases hcomm : (∃ r_rec, post = hop2DeliverPost P s Q c g r_rec) ∨
        (post = hop2InjectPost P qep s Q c g ∧ ¬ (qep + 1 < g.epoch + 1) ∧
          st.1.trivial 3 ⟨Q.other, g.epoch + 1, msg.counter.toNat + 1⟩ = true)
    · have h0_step : ∀ ckS,
          Hop2Phase0Inv P decT encT (m + 1)
            (post (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS) st).2 ∧
          (∀ t > m + 1, ∀ Q',
            (post (hop2CreateOutChain P ℓ (m +
                1) (Dh.dh rc T) g msg sc rc ckR ckS) st).2.2.lazy.lookup
              (t, Q') = none) := by
        intro ckS
        set o := hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS
        have hinv' := hpost.preserves_hop2FullInv h0.inv ((o, st), []) (hsupp_R ckS)
        rcases hcomm with ⟨r_rec, rfl⟩ | ⟨rfl, hqep_le, htriv⟩
        · have hpost_aux : (hop2DeliverPost P s Q c g r_rec o st).2.2 =
              { hop2Commit st.2 Q (some ⟨some (m + 2), rc, some ((m + 1, Dh.dh rc T), ckS)⟩) with
                bad := st.2.bad || hop2BadAt P s g c } := by
            dsimp only [o]; rw [ho_some ckS]; rfl
          exact hop2Phase0Inv_of_create_commit h0 rc (Dh.dh rc T) ckS _ hinv'
            (by rw [hpost_aux]; rfl)
            (by rw [hpost_aux])
            (by rw [hpost_aux])
        · have hpost_aux : (hop2InjectPost P qep s Q c g o st).2.2 =
              hop2Commit { st.2 with bad := st.2.bad || hop2BadAt P s g c } Q
                (some ⟨some (m + 2), rc, some ((m + 1, Dh.dh rc T), ckS)⟩) := by
            dsimp only [o]; rw [ho_some ckS]
            dsimp only [hop2InjectPost]
            simp [hqep_le, htriv]
          exact hop2Phase0Inv_of_create_commit h0 rc (Dh.dh rc T) ckS _ hinv'
            (by rw [hpost_aux]; rfl)
            (by rw [hpost_aux]; rfl)
            (by rw [hpost_aux]; rfl)
      rcases Nat.lt_or_eq_of_le hmk with hlt | heq
      · have hrun_L : ∀ c_chall,
            (simulateQ (lazyImpl (Pt := Pt))
              ((hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k (r_L,
                  c_chall)) g c rc).run st)).run [] =
            (fun ckS => ((hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR ckS, st),
                [])) <$>
              ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :=
          fun c_chall => simulateQ_lazyImpl_hop2Recv_of_succ_lt_made_some P Dh encPt encT decT hX
            (hop2HybPrf k (r_L,
                c_chall)) m g c rc st msg T sc ckR hidx hlt htry hfind hdec hT hsc hQ0 hmade []
        simp only [hrun_L, hrun_R, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc,
            pure_bind]
        refine bind_unif_swap_evalDist_true_le ($ᵗ BitVec 256) _ _ ε fun ckS _ => ?_
        exact ih' _ (m + 1) _ hlt (h0_step ckS).1
      · have hrun_L : ∀ c_chall,
            (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc).run st =
            pure (hop2CreateOutChain P ℓ (m + 1) (Dh.dh rc T) g msg sc rc ckR c_chall, st) :=
          fun c_chall => hop2Recv_run_of_succ_eq_made_some P Dh encPt encT decT hX
            (hop2HybPrf k (r_L,
                c_chall)) m g c rc st msg T sc ckR hidx heq htry hfind hdec hT hsc hQ0 hmade
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
          rw [ho_some ckS, ho_some 0]
          exact hop2InjectPost_eq_of_not_commit P qep s Q c g _ _ _ _ _ _ _ st hnc
        have hL_eq : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
            let z ← (simulateQ (lazyImpl (Pt := Pt))
              ((hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc).run st)).run []
            runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
              (k_oa (hop2InjectPost P qep s Q c g z.1.1 z.1.2).1)
              (hop2InjectPost P qep s Q c g z.1.1 z.1.2).2 z.2)] {true} =
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
            runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall))
              (k_oa (hop2InjectPost P qep s Q c g o0 st).1)
              (hop2InjectPost P qep s Q c g o0 st).2 []] {true} :=
          bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun c_chall =>
            evalDist_hop2Recv_create_of_post_const P Dh encPt encT decT hX qep s
              (hop2HybPrf k (r_L, c_chall)) m g c rc st msg T sc ckR
              hidx hmk htry hfind hdec hT hsc hQ0 hmade (hop2InjectPost P qep s Q c g) o0 hconst
                  k_oa
        have hR_eq : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
            let z ← (simulateQ (lazyImpl (Pt := Pt))
              ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st)).run []
            runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
              (k_oa (hop2InjectPost P qep s Q c g z.1.1 z.1.2).1)
              (hop2InjectPost P qep s Q c g z.1.1 z.1.2).2 z.2)] {true} =
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
            runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
              (k_oa (hop2InjectPost P qep s Q c g o0 st).1)
              (hop2InjectPost P qep s Q c g o0 st).2 []] {true} :=
          bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun u_chall =>
            evalDist_hop2Recv_create_of_post_const P Dh encPt encT decT hX qep s
              (hop2HybPrg P encPt (k + 1) u_chall) m g c rc st msg T sc ckR
              hidx (Nat.le_of_lt hmk1) htry hfind hdec hT hsc hQ0 hmade (hop2InjectPost P qep s Q c
                  g) o0 hconst k_oa
        simp only [hpost_inj]
        rw [hL_eq, hR_eq]
        have hinv' : Hop2FullInv P decT encT (hop2InjectPost P qep s Q c g o0 st).2 := by
          have h1 := hpost.preserves_hop2FullInv h0.inv ((o0, st), []) (hsupp_R 0)
          simpa only [hpost_inj] using h1
        have hnc_aux : (hop2InjectPost P qep s Q c g o0 st).2.2 =
            { st.2 with bad := st.2.bad || hop2BadAt P s g c } := by
          dsimp only [o0]; rw [ho_some 0]
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

theorem evalDist_runHop2_phase0_recvWithPost_le {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k) (r_L : Ratchet.RootKey)
    {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsDeliverInTransitOrInjectPost (Pt := Pt) P qep s Q c st.1 post)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (d ε : ℝ≥0∞)
    (hd : d + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hph1 : ∀ c_chall r st', Hop2Phase1Rel P decT encT k st' [] st' →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + d)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + d) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybPrf k (r_L, c_chall)) (st.1.st Q) c rc).run st
        return post res.1 res.2)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa z.1.1) z.1.2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) (st.1.st Q) c rc).run st
        return post res.1 res.2)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
          1) u_chall) (k_oa z.1.1) z.1.2 z.2)] {true} + ε := by
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
      refine evalDist_runHop2_phase0_of_pure_recv hm r_L h0 Q0 c rc
        (((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none)))
        post hpost_rc hrun_L hrun_R ?_ k_oa d ih'
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
          exact evalDist_runHop2_phase0_of_lazy hm (Nat.le_succ m) r_L h0 Q0 c rc msg T sc
            hidx htry hfind hdec_T hT hsc hQ0 hmade post hpost_rc k_oa d ih'
        | some ckR =>
          exact evalDist_runHop2_phase0_of_create_pm hX hm r_L h0 c rc msg T sc ckR
            hidx htry hfind hdec_T hT hsc hQ0 hmade post hpost_rc k_oa d hph1 ih'
      · have hrun_L := fun c_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrf k (r_L, c_chall))
            m g c rc st hidx hdh
        have hrun_R := fun u_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
            m g c rc st hidx hdh
        exact evalDist_runHop2_phase0_of_pure_recv hm r_L h0 Q0 c rc (hop2NonDhOut P ℓ g c rc)
          post hpost_rc hrun_L hrun_R
          (fun x hx => Or.inl (hop2NonDhOut_snd_none P g c rc x hx)) k_oa d ih'
  · set Q1 := partyOfParity (m + 1)
    set g := st.1.st Q1
    have hp : g.party = Q1 := h0.inv.party_eq Q1
    rcases h0.idx_pm1 with hnone | hsome
    · have hidx : st.2.idx g.party = none := by rw [hp]; exact hnone
      have hrun_L := fun c_chall =>
        hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrf k (r_L, c_chall)) g c rc st hidx
      have hrun_R := fun u_chall =>
        hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc st hidx
      refine evalDist_runHop2_phase0_of_pure_recv hm r_L h0 Q1 c rc
        (((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none)))
        post hpost_rc hrun_L hrun_R ?_ k_oa d ih'
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
        exact evalDist_runHop2_phase0_of_lazy hm (le_refl (m + 1)) r_L h0 Q1 c rc msg T sc
          hidx htry hfind hdec_T hT hsc hQ0 hmade post hpost_rc k_oa d ih'
      · have hrun_L := fun c_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrf k (r_L, c_chall))
            (m + 1) g c rc st hidx hdh
        have hrun_R := fun u_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
            (m + 1) g c rc st hidx hdh
        exact evalDist_runHop2_phase0_of_pure_recv hm r_L h0 Q1 c rc (hop2NonDhOut P ℓ g c rc)
          post hpost_rc hrun_L hrun_R
          (fun x hx => Or.inl (hop2NonDhOut_snd_none P g c rc x hx)) k_oa d ih'

theorem evalDist_runHop2_phase0_deliver_le {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k) (r_L : Ratchet.RootKey)
    {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (d ε : ℝ≥0∞)
    (hd : d + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hph1 : ∀ c_chall r st', Hop2Phase1Rel P decT encT k st' [] st' →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + d)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + d) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrf k (r_L, c_chall)) (Q, c)).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa z.1.1) z.1.2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrg P encPt (k + 1) u_chall) (Q, c)).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
          1) u_chall) (k_oa z.1.1) z.1.2 z.2)] {true} + ε := by
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
      exact evalDist_runHop2_phase0_recvWithPost_le (qep := qep) hX hdec hm r_L h0 Q c
        _ (Or.inl ⟨r_rec, hin, rfl⟩) k_oa d ε hd hph1 ih'

theorem evalDist_runHop2_phase0_inject_le {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k m : ℕ} (hm : m < k) (r_L : Ratchet.RootKey)
    {st : Hop2State Pt ℓ}
    (h0 : Hop2Phase0Inv P decT encT m st)
    (Q : Party) (c : Bytes)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (d ε : ℝ≥0∞)
    (hd : d + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hph1 : ∀ c_chall r st', Hop2Phase1Rel P decT encT k st' [] st' →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + d)
    (ih' : ∀ r m' st', m' < k → Hop2Phase0Inv P decT encT m' st' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa r) st' []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa r) st' []] {true} + d) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (Q, c)).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) (k_oa z.1.1) z.1.2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (Q,
            c)).run st)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
          1) u_chall) (k_oa z.1.1) z.1.2 z.2)] {true} + ε := by
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
    exact evalDist_runHop2_phase0_recvWithPost_le hX hdec hm r_L h0 Q c
      _ (Or.inr rfl) k_oa d ε hd hph1 ih'

theorem evalDist_runHop2_phase0_le {ℓ : ℕ} {P : Params Bytes PQC}
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (s : BitVec 256) (k : ℕ) (r_L : Ratchet.RootKey)
    (hph2 : ∀ c_chall, Hop2Phase2Bound P Dh encPt decT encT ℓ qep s k (r_L, c_chall))
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem : ℕ) (hq : SM.MakesAtMostQueries oa rem)
    (m : ℕ) (hm : m < k) (st : Hop2State Pt ℓ)
    (h0 : Hop2Phase0Inv P decT encT m st) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_chall =>
      runHop2 P Dh encT decT qep s (hop2HybPrf k (r_L, c_chall)) oa st []] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) oa st []] {true} +
      ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem m st with
  | pure a =>
    simp only [runHop2_pure, evalDist_unif_bind_const]
    exact le_self_add
  | query_bind t k_oa ih =>
    rw [SM.MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
    simp only [runHop2_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · simp only [runHop2_unif]
      exact bind_unif_swap_evalDist_true_le _ _ _ _ fun a _ =>
        ih a rem (by simpa [SM.MakesAtMostQueries] using hq.2 a) m hm st h0
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      simp only [runHop2_hop2Lift']
      refine bind_unif_swap_evalDist_true_le _ _ _ _ fun r hr => ?_
      have hinv' :=
          transmitR_support_hop2FullInv P hcodec hL Dh encPt decT encT hX hdec qep y_tr st h0.inv r
          hr
      have hle : (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
        m hm (r.2, st.2) (h0.of_st1_step r.2 hinv')).trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      simp only [runHop2_hop2Lift']
      refine bind_unif_swap_evalDist_true_le _ _ _ _ fun r hr => ?_
      have hinv' :=
          challR_support_hop2FullInv P hcodec hL Dh encPt decT encT hX hdec qep y_ch st h0.inv r hr
      have hle : (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
        m hm (r.2, st.2) (h0.of_st1_step r.2 hinv')).trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      have hd : ((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 6 * (rem - 1) +
            5 ≤ 6 * rem)) zero_le
      refine evalDist_runHop2_phase0_deliver_le (qep := qep) hX hdec hm r_L h0 Q c k_oa
        (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) hd
        (fun c_chall r st' hrel1 => ?_)
        (fun r m' st' hm' h0' => ?_)
      · have h1 := evalDist_runHop2_phase1_le hcodec hL hX hdec qep s k (r_L, c_chall)
          (hph2 c_chall) (k_oa r) (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r)
          st' [] st' hrel1
        simpa only [List.length_nil, add_zero] using h1
      · exact ih r (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r)
          m' hm' st' h0'
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      have hd : ((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 6 * (rem - 1) +
            5 ≤ 6 * rem)) zero_le
      refine evalDist_runHop2_phase0_inject_le hX hdec hm r_L h0 Q c k_oa
        (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) hd
        (fun c_chall r st' hrel1 => ?_)
        (fun r m' st' hm' h0' => ?_)
      · have h1 := evalDist_runHop2_phase1_le hcodec hL hX hdec qep s k (r_L, c_chall)
          (hph2 c_chall) (k_oa r) (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r)
          st' [] st' hrel1
        simpa only [List.length_nil, add_zero] using h1
      · exact ih r (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r)
          m' hm' st' h0'
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      simp only [runHop2_hop2Lift']
      refine bind_unif_swap_evalDist_true_le _ _ _ _ fun r hr => ?_
      have hinv' := corrR_support_hop2FullInv P decT encT y_corr st h0.inv r hr
      have hle : (((6 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
        m hm (r.2, st.2) (h0.of_st1_step r.2 hinv')).trans (add_le_add le_rfl hle)

theorem stateT_run'_lift_bind {S α β : Type} (p : ProbComp α)
    (f : α → StateT S ProbComp β) (s : S) :
    (do let x ← (StateT.lift p : StateT S ProbComp α); f x).run' s =
      (do let x ← p; (f x).run' s) := by
  change (Prod.fst <$> (do let x ← (StateT.lift p : StateT S ProbComp α); f x).run s) =
    (do let x ← p; Prod.fst <$> (f x).run s)
  rw [StateT.run_bind, stateT_lift_probComp_run]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

theorem evalDist_unif_bind6_swap
    (f : BitVec 256 → Bool → BitVec 256 → BitVec 256 → BitVec 256 → BitVec 256 → BitVec 256 →
        ProbComp Bool) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
      ($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u1 =>
      f u b ck0 x alice pqr u1] {true} =
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u1 =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
      f u b ck0 x alice pqr u1] {true} := by
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ Bool)]
  refine bind_evalDist_true_eq ($ᵗ Bool) _ _ fun b => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun ck0 => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun x => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun pqr => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]

omit [SampleableType Pt] in
theorem prgRealExperiment_hop2PrgRedK_succ_eq {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    (Ratchet.expandPRG P.C.F).prgRealExperiment
        (hop2PrgRedK P ℓ Dh encPt encT decT qep s (k + 1) A) =
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
        let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
          { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
        let aux0 : Hop2Aux Pt :=
          { made := [((0, I0), u1)]
            idx := fun Q => match Q with | .A => some 1 | .B => some 0
            coins := fun Q => match Q with | .A => alice | .B => x }
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) A (initSt, aux0) []) := by
  unfold PRGScheme.prgRealExperiment hop2PrgRedK
  refine bind_congr fun u_chall => ?_
  change simulateQ (pureStepImpl _) (hop2Game P ℓ Dh encT decT qep s (pureStepHyb (k +
      1) _ _) A) = _
  unfold hop2Game
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
  exact simulateQ_prfReal_hop2Impl_eq_runHop2 P Dh encT decT qep s (k + 1) _ _ A _

theorem evalDist_hop2PrfRedK_true_le_hop2PrgRedK_succ_of_phase2 {ℓ : ℕ}
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep q : ℕ) (s : BitVec 256) (k : ℕ)
    (hph2 : ∀ rc_L, Hop2Phase2Bound P Dh encPt decT encT ℓ qep s k rc_L)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
    (hq : SM.MakesAtMostQueries A q) :
    𝒟[(extractPRF P.C.F encPt).branch true (hop2PrfRedK P ℓ Dh encT decT qep s k A)] {true} ≤
      𝒟[(Ratchet.expandPRG P.C.F).prgRealExperiment
        (hop2PrgRedK P ℓ Dh encPt encT decT qep s (k + 1) A)] {true} +
        ((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
  rw [evalDist_branch_true_eq_lazyImpl, prgRealExperiment_hop2PrgRedK_succ_eq]
  have hunfold :
      (simulateQ (lazyImpl (Pt := Pt))
        (hop2PrfRedK P ℓ Dh encT decT qep s k A)).run' [] =
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
        let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
          { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
        let aux0 : Hop2Aux Pt :=
          { made := [((0, I0), ck1)]
            idx := fun Q => match Q with | .A => some 1 | .B => some 0
            coins := fun Q => match Q with | .A => alice | .B => x }
        runHop2 P Dh encT decT qep s (hop2HybPrf k (r, c_chall)) A (initSt, aux0) []) := by
    unfold hop2PrfRedK
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun r => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun c_chall => ?_
    unfold hop2Game
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
    have h0 := hop2Phase0Inv_init (ℓ :=
        ℓ) P decT encT b ck0 x alice pqr ck1 (Dh.dh x (Dh.dh alice Dh.base))
    have hrel1 := hop2Phase1Rel_of_phase0_self 0 _ h0 (fun _ => rfl)
    have h1 := evalDist_runHop2_phase1_le hcodec hL hX hdec qep s 0 (r, ck1)
      (hph2 (r, ck1)) A q hq _ [] _ hrel1
    simpa only [List.length_nil, add_zero] using h1
  · refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ _ fun u1 _ => ?_
    simp only [Nat.ne_of_gt hk_pos, ↓reduceIte]
    have h0 := hop2Phase0Inv_init (ℓ :=
        ℓ) P decT encT b ck0 x alice pqr u1 (Dh.dh x (Dh.dh alice Dh.base))
    exact evalDist_runHop2_phase0_le hcodec hL hX hdec qep s k r
      (fun c_chall => hph2 (r, c_chall)) A q hq 0 hk_pos _ h0

theorem evalDist_hop2PrfRedK_true_le_hop2PrgRedK_succ {ℓ : ℕ}
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep q : ℕ) (s : BitVec 256) (k : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
    (hq : SM.MakesAtMostQueries A q) :
    𝒟[(extractPRF P.C.F encPt).branch true (hop2PrfRedK P ℓ Dh encT decT qep s k A)] {true} ≤
      𝒟[(Ratchet.expandPRG P.C.F).prgRealExperiment
        (hop2PrgRedK P ℓ Dh encPt encT decT qep s (k + 1) A)] {true} +
        ((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
  evalDist_hop2PrfRedK_true_le_hop2PrgRedK_succ_of_phase2 P hcodec hL Dh encPt encT decT hX hdec
    qep q s k
    (fun rc_L u_chall Q_create oa rem hq_oa sL tL sR hrel hwin =>
      evalDist_runHop2_phase2_le_createColl hcodec hL hX hdec hz qep s k rc_L u_chall Q_create
        oa rem hq_oa sL tL sR hrel hwin)
    A hq

end Phase0

section HInit

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

open CryptoGames.LibsignalSM.Proofs.Refinement

/-! ## Reference receive steps for `h_init` -/

theorem evalDist_apply_eq_beq (mx : ProbComp Bool) (v : Bool) :
    𝒟[mx] {v} = 𝒟[(· == v) <$> mx] {true} := by
  rw [map_eq_bind_pure_comp, evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
        Measurable.of_discrete.aemeasurable]
  calc 𝒟[mx] {v}
      = ∫⁻ b, Set.indicator {v} 1 b ∂𝒟[mx] :=
        (MeasureTheory.lintegral_indicator_one MeasurableSet.of_discrete).symm
    _ = ∫⁻ b, 𝒟[pure (b == v)] {true} ∂𝒟[mx] := by
        refine MeasureTheory.lintegral_congr fun b => ?_
        cases b <;> cases v <;> simp

theorem bind_evalDist_true_le_add_two_of_support {α : Type} (mx : ProbComp α)
    (f g h : α → ProbComp Bool) (d : ℝ≥0∞)
    (hle : ∀ a ∈ support mx, 𝒟[f a] {true} ≤ 𝒟[g a] {true} + 𝒟[h a] {true} + d) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} + 𝒟[mx >>= h] {true} + d := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using hle a (by simp)
  | query_bind t k ih =>
    have h1 : ∀ (m : unifSpec.Range t → ProbComp Bool),
        𝒟[(OracleSpec.query (spec := unifSpec) t : ProbComp _) >>= m] {true} =
          ∫⁻ u, 𝒟[m u] {true} ∂𝒟[(OracleSpec.query (spec := unifSpec) t : ProbComp _)] :=
              fun m => by
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    rw [bind_assoc, bind_assoc, bind_assoc, h1, h1, h1]
    have hd : d = ∫⁻ _u, d ∂𝒟[(OracleSpec.query (spec := unifSpec) t : ProbComp _)] := by
      rw [MeasureTheory.lintegral_const, evalDist_apply_univ_eq_one, mul_one]
    rw [hd, ← MeasureTheory.lintegral_add_left Measurable.of_discrete,
      ← MeasureTheory.lintegral_add_right _ Measurable.of_discrete]
    refine MeasureTheory.lintegral_mono fun u => ih u fun a ha =>
      hle a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

theorem isAliceSpkQuery_prob_le_hop2GuessUnit (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (Q : Party) (gA : GhostState Bytes) (c : Bytes) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      pure (isAliceSpkQuery P (KeyPair.generate P.C x).publicKey Q gA c)] {true} ≤
      hop2GuessUnit Dh := by
  unfold isAliceSpkQuery
  by_cases hQA : (Q == .A && decide (0 ∈ gA.chainEpochs)) = true
  · simp only [hQA, Bool.true_and]
    cases SignalMessage.tryFrom P.codec c with
    | error _ =>
      dsimp only []
      rw [OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
      simp
    | ok msg =>
      exact generate_publicKey_eq_prob_le_hop2GuessUnit P Dh encPt decT encT hX hdec
        msg.senderRatchetKey
  · simp only [Bool.not_eq_true] at hQA
    simp only [hQA, Bool.false_and, OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
    simp

/-- Canonical lazy-table version of `receiveSpk` using `s`. -/
def stepReceiveSpk (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (L : List (Pt × BitVec 256)) :
    ProbComp (Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × List (Pt × BitVec 256)) :=
  if g.party == .B && g.epoch == 0 then
    stepReceiveB0 P ℓ Dh encT decT s g c rc L
  else
    pure ((sessionSchemeU P ℓ).receive g c rc, L)

omit [SampleableType Pt] in
theorem receiveSpk_true_tableFor_bind {Key α : Type}
    (mac : MACScheme Key Pt (BitVec 256)) (P : Params Bytes PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔ Dh.dh s P_pt =
        Dh.dh s P')
    (key : Key) (x : BitVec 256) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (L : List (Pt × BitVec 256))
    (F : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × PRFState Key Pt (BitVec 256) →
        ProbComp α) :
    ((simulateQ (prfOracleImpl mac) (receiveSpk P ℓ Dh encT decT x g c rc)).run
        ⟨key, true, tableFor Dh x L⟩ >>= F) =
      (stepReceiveSpk P ℓ Dh encT decT s g c rc L >>= fun r =>
        F (r.1, ⟨key, true, tableFor Dh x r.2⟩)) := by
  unfold receiveSpk stepReceiveSpk
  by_cases hB0 : (g.party == .B && g.epoch == 0) = true
  · simp only [hB0, ↓reduceIte]
    rw [receiveB0_eq_bind_receiveB0Post]
    unfold stepReceiveB0
    cases SignalMessage.tryFrom P.codec c with
    | error _ => simp [StateT.run_pure]
    | ok msg =>
      dsimp only []
      cases decT msg.senderRatchetKey with
      | none => simp [StateT.run_pure]
      | some T =>
        dsimp only []
        by_cases hcond : T = 0 ∨ encT T ≠ msg.senderRatchetKey
        · simp [hcond, StateT.run_pure]
        · simp only [hcond, ↓reduceIte, simulateQ_bind, simulateQ_prfOracleImpl_evalQuery,
            simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
          rw [prfEval_true_tableFor_bind mac Dh s hker key x T L]
  · simp [hB0, StateT.run_pure]

theorem receiveB0Post_patchBobSpk (P : Params Bytes PQC) (ℓ : ℕ)
    (kp : KeyPair) (ck0 : BitVec 256) (g : GhostState Bytes)
    (msg : SignalMessage) (rc prk : BitVec 256) :
    receiveB0Post P ℓ (patchBobSpk kp ck0 g) msg rc prk =
      receiveB0Post P ℓ g msg rc prk := by
  unfold patchBobSpk setBobSpk receiveB0Post
  by_cases h : g.epoch = 0 <;> simp [h]

omit [SampleableType Pt] in
theorem stepReceiveB0_patchBobSpk (P : Params Bytes PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (kp : KeyPair) (ck0 : BitVec 256) (g : GhostState Bytes)
    (c : Bytes) (rc : BitVec 256) (L : List (Pt × BitVec 256)) :
    stepReceiveB0 P ℓ Dh encT decT s (patchBobSpk kp ck0 g) c rc L =
      stepReceiveB0 P ℓ Dh encT decT s g c rc L := by
  unfold stepReceiveB0
  cases SignalMessage.tryFrom P.codec c with
  | error _ => rfl
  | ok msg =>
    dsimp only []
    cases decT msg.senderRatchetKey with
    | none => rfl
    | some T =>
      dsimp only []
      split
      · rfl
      · simp only [receiveB0Post_patchBobSpk]

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_prfOracleImpl_liftM_bind {Key α β : Type}
    (mac : MACScheme Key Pt (BitVec 256)) (oa : ProbComp α)
    (st_prf : PRFState Key Pt (BitVec 256))
    (F : α × PRFState Key Pt (BitVec 256) → ProbComp β) :
    ((simulateQ (prfOracleImpl mac)
      (liftM oa : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α)).run st_prf >>= F) =
    (oa >>= fun a => F (a, st_prf)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [StateT.run_pure]
  | query_bind t k ih =>
    change ((liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) >>= fun u =>
        (simulateQ (prfOracleImpl mac) (liftM (k u))).run st_prf >>= F) =
      ((liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) >>= fun u =>
        k u >>= fun a => F (a, st_prf))
    exact bind_congr fun u => ih u

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_prfOracleImpl_liftSpkGameM_bind {Key α β : Type} {ℓ : ℕ}
    (mac : MACScheme Key Pt (BitVec 256))
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (st_prf : PRFState Key Pt (BitVec 256))
    (F : (α × SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) × PRFState Key Pt (BitVec 256) →
        ProbComp β) :
    ((simulateQ (prfOracleImpl mac) ((liftSpkGameM m).run st)).run st_prf >>= F) =
    (m.run st >>= fun z => F (z, st_prf)) :=
  simulateQ_prfOracleImpl_liftM_bind mac (m.run st) st_prf F

/-- Reference receive step in `runSpkRef`, rejecting queries that hit `spk_s` on Alice's epoch-0 chain. -/
def stepReceiveRef (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256)
    (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes) (rc : BitVec 256)
    (L : List (Pt × BitVec 256)) :
    ProbComp (Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × List (Pt × BitVec 256)) :=
  if (sRef.st Q).party == .B && (sRef.st Q).epoch == 0 then
    stepReceiveB0 P ℓ Dh encT decT s (sRef.st Q) c rc L
  else if isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c then
    pure (none, L)
  else
    pure ((sessionSchemeU P ℓ).receive (sRef.st Q) c rc, L)

@[simp] theorem stateT_lift_run_any {σ : Type} {m : Type → Type} [Monad m] {α : Type}
    (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) :=
  rfl

abbrev SpkTabSt (Pt : Type) (ℓ : ℕ) :=
  SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × List (Pt × BitVec 256)

def liftSpkTab {ℓ : ℕ} {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α) :
    StateT (SpkTabSt Pt ℓ) ProbComp α :=
  StateT.mk fun ⟨st, L⟩ => do
    let (a, st') ← m.run st
    return (a, (st', L))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem liftSpkTab_run {ℓ : ℕ} {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (L : List (Pt × BitVec 256)) :
    (liftSpkTab m).run (st, L) = (m.run st >>= fun r => pure (r.1, (r.2, L))) :=
  rfl

def deliverSpkStep (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ)))
      (StateT (SpkTabSt Pt ℓ) ProbComp) :=
  fun ⟨Q, c⟩ => StateT.mk fun ⟨st, L⟩ => do
    if st.win then return (none, (st, L))
    match st.inTransit Q.other c with
    | none => return (none, (st, L))
    | some r =>
      let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let (res, L') ← stepReceiveSpk P ℓ Dh encT decT s (st.st Q) c rc L
      match res with
      | none => return (some .rejected, (st, L'))
      | some (st', t', i', m') =>
        return (some (.accepted t' i' (if st.chall.contains r.pos then none else some m')),
          (st.accept Q st' r.pos, L'))

def injectSpkStep (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ)))
      (StateT (SpkTabSt Pt ℓ) ProbComp) :=
  fun ⟨Q, c⟩ => StateT.mk fun ⟨st, L⟩ => do
    if st.win || (st.inTransit Q.other c).isSome || !(st.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c) then
      return (none, (st, L))
    let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let (res, L') ← stepReceiveSpk P ℓ Dh encT decT s (st.st Q) c rc L
    match res with
    | none => return (some .rejected, (st, L'))
    | some (st', t', i', m') =>
      if qep + 1 < t' then return (some .rejected, (st, L'))
      let pos : SM.Pos := ⟨Q.other, t', i'⟩
      if st.trivial 3 pos then
        return (some (.accepted t' i' (some m')), (st.accept Q st' pos, L'))
      else
        return (some .rejected, ({ st with win := true }, L'))

def spkStepImpl (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) :
    QueryImpl (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
      (StateT (SpkTabSt Pt ℓ) ProbComp)
  | .inl u => StateT.lift (query (spec := unifSpec) u)
  | .inr (.inl (.inl (.inl (.inl x)))) =>
    liftSpkTab (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inl (.inr x)))) =>
    liftSpkTab (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inr x))) =>
    deliverSpkStep P ℓ Dh encT decT s x
  | .inr (.inl (.inr x)) =>
    injectSpkStep P ℓ Dh encT decT qep s x
  | .inr (.inr x) =>
    liftSpkTab (SM.corrR (configRefuseEarlyBobCorr decT encT) x)

omit [SampleableType Pt] in
theorem spkOracleImpl_true_tableFor_step_bind {Key α : Type} {ℓ : ℕ}
    (mac : MACScheme Key Pt (BitVec 256)) (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔ Dh.dh s P_pt =
        Dh.dh s P')
    (key : Key) (z : BitVec 256)
    (q : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (L : List (Pt × BitVec 256))
    (F : ((unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Range q ×
          SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ×
          PRFState Key Pt (BitVec 256) → ProbComp α) :
    ((simulateQ (prfOracleImpl mac)
        ((spkOracleImpl P ℓ Dh encT decT qep z q).run st)).run
        ⟨key, true, tableFor Dh z L⟩ >>= F) =
      ((spkStepImpl P ℓ Dh encT decT qep s q).run (st, L) >>= fun r =>
        F ((r.1, r.2.1), ⟨key, true, tableFor Dh z r.2.2⟩)) := by
  rcases q with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
  · dsimp only [spkOracleImpl, spkStepImpl]
    rw [stateT_lift_run_any, stateT_lift_run_any, simulateQ_bind]
    change ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun a =>
        (pure (a, (⟨key, true, tableFor Dh z L⟩ : PRFState Key Pt (BitVec 256))) >>= fun x =>
          (simulateQ (prfOracleImpl mac) (pure (x.1, st))).run x.2) >>= F) = _
    simp [StateT.run_pure]
  · dsimp only [spkOracleImpl, spkStepImpl]
    rw [simulateQ_prfOracleImpl_liftSpkGameM_bind, liftSpkTab_run, bind_assoc]
    simp only [pure_bind]
  · dsimp only [spkOracleImpl, spkStepImpl]
    rw [simulateQ_prfOracleImpl_liftSpkGameM_bind, liftSpkTab_run, bind_assoc]
    simp only [pure_bind]
  · dsimp only [spkOracleImpl, spkStepImpl]
    unfold deliverSpk deliverSpkStep
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_mk]
    by_cases hw : st.win = true
    · simp [hw, StateT.run_pure]
    · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      cases st.inTransit Q.other c with
      | none => simp [StateT.run_pure]
      | some r =>
        simp only [stateT_lift_run_any, bind_assoc, pure_bind, simulateQ_bind,
          StateT.run_bind]
        rw [simulateQ_prfOracleImpl_liftM_bind]
        refine bind_congr fun rc => ?_
        rw [receiveSpk_true_tableFor_bind mac P ℓ Dh encT decT s hker key z (st.st Q) c rc L]
        refine bind_congr fun res => ?_
        rcases res with ⟨o, L'⟩
        cases o with
        | none => simp [StateT.run_pure]
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          simp [StateT.run_set, StateT.run_pure]
  · dsimp only [spkOracleImpl, spkStepImpl]
    unfold injectSpk injectSpkStep
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_mk]
    by_cases hg : (st.win || (st.inTransit Q.other c).isSome || !(st.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
    · simp [hg, StateT.run_pure]
    · simp only [hg, Bool.false_eq_true, ↓reduceIte, stateT_lift_run_any, bind_assoc,
        pure_bind, simulateQ_bind, StateT.run_bind]
      rw [simulateQ_prfOracleImpl_liftM_bind]
      refine bind_congr fun rc => ?_
      rw [receiveSpk_true_tableFor_bind mac P ℓ Dh encT decT s hker key z (st.st Q) c rc L]
      refine bind_congr fun res => ?_
      rcases res with ⟨o, L'⟩
      cases o with
      | none => simp [StateT.run_pure]
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        dsimp only []
        by_cases hcap : qep + 1 < t'
        · simp [hcap, StateT.run_pure]
        · simp only [hcap, ↓reduceIte]
          by_cases htriv : st.trivial 3 ⟨Q.other, t', i'⟩ = true
          · simp [htriv, StateT.run_set, StateT.run_pure]
          · simp [htriv, StateT.run_set, StateT.run_pure]
  · dsimp only [spkOracleImpl, spkStepImpl]
    rw [simulateQ_prfOracleImpl_liftSpkGameM_bind, liftSpkTab_run, bind_assoc]
    simp only [pure_bind]

omit [SampleableType Pt] in
theorem simulateQ_prfOracleImpl_spkOracleImpl_bind {Key α β : Type} {ℓ : ℕ}
    (mac : MACScheme Key Pt (BitVec 256)) (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔ Dh.dh s P_pt =
        Dh.dh s P')
    (key : Key) (z : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (L : List (Pt × BitVec 256))
    (F : (β × SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ×
          PRFState Key Pt (BitVec 256) → ProbComp α) :
    ((simulateQ (prfOracleImpl mac)
        ((simulateQ (spkOracleImpl P ℓ Dh encT decT qep z) oa).run st)).run
        ⟨key, true, tableFor Dh z L⟩ >>= F) =
      ((simulateQ (spkStepImpl P ℓ Dh encT decT qep s) oa).run (st, L) >>= fun r =>
        F ((r.1, r.2.1), ⟨key, true, tableFor Dh z r.2.2⟩)) := by
  induction oa using OracleComp.inductionOn generalizing st L with
  | pure a => simp [StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    rw [spkOracleImpl_true_tableFor_step_bind mac P Dh encT decT qep s hker key z t st L]
    refine bind_congr fun r => ih r.1 r.2.1 r.2.2

def SpkRefInv {ℓ : ℕ} (P : Params Bytes PQC) (spk : PublicKey) (sRef : GameSt Bytes ℓ) : Prop :=
  GameInv P spk { sRef with win := false } ∧ (sRef.st .B).party = .B

theorem spkRefInv_party_eq {ℓ : ℕ} {P : Params Bytes PQC} {spk : PublicKey}
    {sRef : GameSt Bytes ℓ} (hinv : SpkRefInv P spk sRef) (Q : Party) :
    (sRef.st Q).party = Q := by
  cases Q with
  | A => exact hinv.1.1.1
  | B => exact hinv.2

theorem gameInv_of_spkRefInv_win_false {ℓ : ℕ} {P : Params Bytes PQC} {spk : PublicKey}
    {sRef : GameSt Bytes ℓ} (hinv : SpkRefInv P spk sRef) (hw : sRef.win = false) :
    GameInv P spk sRef := by
  have h1 := hinv.1
  have heq : { sRef with win := false } = sRef := by
    cases sRef; simp only [← hw]
  rwa [heq] at h1

theorem spkRefInv_of_gameInv {ℓ : ℕ} {P : Params Bytes PQC} {spk : PublicKey}
    {sRef : GameSt Bytes ℓ} (hinv : GameInv P spk sRef) (hB : (sRef.st .B).party = .B) :
    SpkRefInv P spk sRef := by
  unfold SpkRefInv
  have heq : { sRef with win := false } = sRef := by
    have hw := hinv.2.2.2.1
    cases sRef; simp only [← hw]
  rw [heq]
  exact ⟨hinv, hB⟩

theorem spkRefInv_with_win_true {ℓ : ℕ} {P : Params Bytes PQC} {spk : PublicKey}
    {sRef : GameSt Bytes ℓ} (hinv : SpkRefInv P spk sRef) :
    SpkRefInv P spk { sRef with win := true } :=
  hinv

theorem spkRefInv_initGameSpkRef (P : Params Bytes PQC) (ℓ : ℕ)
    (b : Bool) (s prk alice pqr : BitVec 256) :
    SpkRefInv P (KeyPair.generate P.C s).publicKey (initGameSpkRef P ℓ b s prk alice pqr) :=
  spkRefInv_of_gameInv (gameInv_initGameSpkRef P ℓ b s prk alice pqr) rfl

theorem receiveB0Post_party (P : Params Bytes PQC) (ℓ : ℕ)
    (g : GhostState Bytes) (msg : SignalMessage) (rc prk : BitVec 256)
    (g' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (h : receiveB0Post P ℓ g msg rc prk = some (g', t', i', m')) :
    g'.party = g.party := by
  unfold receiveB0Post at h
  dsimp only [] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _, _, _⟩
      rfl

omit [SampleableType Pt] in
theorem stepReceiveB0_support_props {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (spk : PublicKey) (sRef : GameSt Bytes ℓ)
    (c : Bytes) (rc : BitVec 256) (L : List (Pt × BitVec 256))
    (hinv : SpkRefInv P spk sRef) (hw : sRef.win = false) :
    ∀ res ∈ support (stepReceiveB0 P ℓ Dh encT decT s (sRef.st .B) c rc L),
      ∀ g' t' i' m', res.1 = some (g', t', i', m') →
        t' = 1 ∧ g'.epoch = 1 ∧ g'.party = .B ∧
        (∀ kp ck0, patchBobSpk kp ck0 g' = g' ∧ patchBob ck0 g' = g') ∧
        (∀ pos, SpkRefInv P spk (sRef.accept .B g' pos)) := by
  have hginv := gameInv_of_spkRefInv_win_false hinv hw
  intro res hres g' t' i' m' hsome
  unfold stepReceiveB0 at hres
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ =>
    rw [htry] at hres
    simp only [support_pure, Set.mem_singleton_iff] at hres
    rw [hres] at hsome; cases hsome
  | ok msg =>
    rw [htry] at hres
    dsimp only [] at hres
    cases hdec : decT msg.senderRatchetKey with
    | none =>
      rw [hdec] at hres
      simp only [support_pure, Set.mem_singleton_iff] at hres
      rw [hres] at hsome; cases hsome
    | some T =>
      rw [hdec] at hres
      dsimp only [] at hres
      by_cases hbad : T = 0 ∨ encT T ≠ msg.senderRatchetKey
      · simp only [hbad, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hres
        rw [hres] at hsome; cases hsome
      · simp only [hbad, ↓reduceIte, support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff, exists_prop] at hres
        rcases hres with ⟨r, hr, hres_eq⟩
        rw [hres_eq] at hsome
        have hpost := receiveB0Post_preserves_BobInv P ℓ (sRef.epoch .B) (sRef.st .B)
          msg rc r.1 g' t' i' m' hginv.2.1 hsome
        have hg_party : g'.party = .B :=
          (receiveB0Post_party P ℓ (sRef.st .B) msg rc r.1 g' t' i' m' hsome).trans hinv.2
        refine ⟨hpost.2.1, hpost.2.2.1, hg_party, hpost.2.2.2, ?_⟩
        intro pos
        refine spkRefInv_of_gameInv ⟨?_, ?_, ?_, hw, ?_⟩ ?_
        · dsimp only [GameState.accept, GameState.delete]
          rw [Function.update_of_ne (by decide)]; exact hginv.1
        · dsimp only [GameState.accept, GameState.delete]
          rw [Function.update_self]; exact hpost.1 _
        · dsimp only [GameState.accept, GameState.delete]
          have hne : ¬ (Party.A = Party.B ∧ 0 = pos.epoch) := by rintro ⟨h, _⟩; cases h
          simp only [hne, ↓reduceIte]; exact hginv.2.2.1
        · intro rec' hrec'
          dsimp only [GameState.accept, GameState.delete] at hrec'
          exact hginv.2.2.2.2 rec' (List.mem_of_mem_filter hrec')
        · dsimp only [GameState.accept, GameState.delete]
          rw [Function.update_self]; exact hg_party

theorem patchAlice_party (ck0 : BitVec 256) (g : GhostState Bytes) :
    (patchAlice ck0 g).party = g.party := by
  unfold patchAlice setAliceSpkKey; split <;> rfl

theorem patchAlicePub_party (spk : PublicKey) (g : GhostState Bytes) :
    (patchAlicePub spk g).party = g.party := by
  unfold patchAlicePub setAliceSpkPub; split <;> rfl

theorem patchBobSpk_party (kp : KeyPair) (ck0 : BitVec 256) (g : GhostState Bytes) :
    (patchBobSpk kp ck0 g).party = g.party := by
  unfold patchBobSpk setBobSpk; split <;> rfl

theorem patchGameSpk_party_eq {ℓ : ℕ} (C : Crypto) (z ck0 : BitVec 256)
    (sRef : GameSt Bytes ℓ) (Q : Party) :
    ((patchGameSpk C z ck0 sRef).st Q).party = (sRef.st Q).party := by
  cases Q with
  | A => simp [patchGameSpk_st_A, patchAlice_party, patchAlicePub_party]
  | B => simp [patchGameSpk_st_B, patchBobSpk_party]

theorem patchAlice_epoch (ck0 : BitVec 256) (g : GhostState Bytes) :
    (patchAlice ck0 g).epoch = g.epoch := by
  unfold patchAlice setAliceSpkKey; split <;> rfl

theorem patchAlicePub_epoch (spk : PublicKey) (g : GhostState Bytes) :
    (patchAlicePub spk g).epoch = g.epoch := by
  unfold patchAlicePub setAliceSpkPub; split <;> rfl

theorem patchBobSpk_epoch (kp : KeyPair) (ck0 : BitVec 256) (g : GhostState Bytes) :
    (patchBobSpk kp ck0 g).epoch = g.epoch := by
  unfold patchBobSpk setBobSpk; split <;> rfl

theorem patchGameSpk_epoch_eq {ℓ : ℕ} (C : Crypto) (z ck0 : BitVec 256)
    (sRef : GameSt Bytes ℓ) (Q : Party) :
    ((patchGameSpk C z ck0 sRef).st Q).epoch = (sRef.st Q).epoch := by
  cases Q with
  | A => simp [patchGameSpk_st_A, patchAlice_epoch, patchAlicePub_epoch]
  | B => simp [patchGameSpk_st_B, patchBobSpk_epoch]

def patchRecvParty (C : Crypto) (z ck0 : BitVec 256) (Q : Party) (g : GhostState Bytes) :
    GhostState Bytes :=
  patchParty ck0 Q (patchPartyPub (KeyPair.generate C z).publicKey (KeyPair.generate C z) Q g)

theorem receiveB0Post_map_patchRecvParty (P : Params Bytes PQC) (ℓ : ℕ)
    (z ck0 : BitVec 256) (g : GhostState Bytes) (msg : SignalMessage) (rc prk : BitVec 256) :
    (receiveB0Post P ℓ g msg rc prk).map
        (fun y => (patchRecvParty P.C z ck0 .B y.1, y.2.1, y.2.2.1, y.2.2.2)) =
      receiveB0Post P ℓ g msg rc prk := by
  unfold receiveB0Post
  dsimp only []
  split
  · rfl
  · split
    · rfl
    · dsimp only [Option.map, patchRecvParty, patchParty, patchPartyPub, patchBob, patchBobSpk]
      simp

omit [SampleableType Pt] in
theorem stepReceiveB0_map_patchRecvParty (P : Params Bytes PQC) (ℓ : ℕ) (Dh :
    DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s z ck0 : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (L : List (Pt × BitVec 256)) :
    (fun res => (res.1.map (fun y => (patchRecvParty P.C z ck0 .B y.1, y.2.1, y.2.2.1, y.2.2.2)),
        res.2)) <$>
        stepReceiveB0 P ℓ Dh encT decT s g c rc L =
      stepReceiveB0 P ℓ Dh encT decT s g c rc L := by
  unfold stepReceiveB0
  cases SignalMessage.tryFrom P.codec c with
  | error _ => simp
  | ok msg =>
    dsimp only []
    cases decT msg.senderRatchetKey with
    | none => simp
    | some T =>
      dsimp only []
      split
      · simp
      · simp only [map_bind, map_pure, receiveB0Post_map_patchRecvParty]

omit [SampleableType Pt] in
theorem stepReceiveSpk_patchGameSpk_of_not_spk {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s z ck0 : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes) (rc : BitVec 256)
    (L : List (Pt × BitVec 256))
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (hw : sRef.win = false)
    (hnspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = false)
    (hnspk_z : isAliceSpkQuery P (KeyPair.generate P.C z).publicKey Q (sRef.st .A) c = false) :
    stepReceiveSpk P ℓ Dh encT decT s ((patchGameSpk P.C z ck0 sRef).st Q) c rc L =
      (fun res => (res.1.map (fun y => (patchRecvParty P.C z ck0 Q y.1, y.2.1, y.2.2.1, y.2.2.2)),
          res.2)) <$>
        stepReceiveRef P ℓ Dh encT decT s sRef Q c rc L := by
  unfold stepReceiveSpk stepReceiveRef
  have hp_eq := patchGameSpk_party_eq P.C z ck0 sRef Q
  have hep_eq := patchGameSpk_epoch_eq P.C z ck0 sRef Q
  rw [hp_eq, hep_eq]
  have hpQ := spkRefInv_party_eq hinv Q
  by_cases hB0 : ((sRef.st Q).party == .B && (sRef.st Q).epoch == 0) = true
  · simp only [hB0, ↓reduceIte]
    have hQ : Q = .B := by
      simp only [hpQ, Bool.and_eq_true, beq_iff_eq] at hB0
      exact hB0.1
    subst hQ
    rw [patchGameSpk_st_B, stepReceiveB0_patchBobSpk, stepReceiveB0_map_patchRecvParty]
  · simp only [hB0, Bool.false_eq_true, ↓reduceIte, hnspk_s, map_pure]
    have hB_ne : Q = .B → (sRef.st .B).epoch ≠ 0 := by
      intro hQ h0; subst hQ; simp [hpQ, h0] at hB0
    have hginv := gameInv_of_spkRefInv_win_false hinv hw
    have hstep := (receive_patchGameSpk_of_not_spk P ℓ z ck0
      (KeyPair.generate P.C s).publicKey sRef Q c rc hginv hB_ne hnspk_s hnspk_z).1
    exact congrArg (fun o => pure (o, L)) hstep

omit [SampleableType Pt] in
theorem stepReceiveRef_support_spkRefInv {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (sRef : GameSt Bytes ℓ) (Q : Party) (c : Bytes) (rc : BitVec 256)
    (L : List (Pt × BitVec 256))
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (hw : sRef.win = false) :
    ∀ res ∈ support (stepReceiveRef P ℓ Dh encT decT s sRef Q c rc L),
      ∀ st' t' i' m', res.1 = some (st', t', i', m') →
        0 < t' ∧
        (∀ pos : SM.Pos, (Q = .A → 0 < pos.epoch) →
          SpkRefInv P (KeyPair.generate P.C s).publicKey (sRef.accept Q st' pos)) := by
  intro res hres st' t' i' m' hsome
  unfold stepReceiveRef at hres
  have hpQ := spkRefInv_party_eq hinv Q
  by_cases hB0 : ((sRef.st Q).party == .B && (sRef.st Q).epoch == 0) = true
  · simp only [hB0, ↓reduceIte] at hres
    have hQ : Q = .B := by
      simp only [hpQ, Bool.and_eq_true, beq_iff_eq] at hB0
      exact hB0.1
    subst hQ
    have hprops := stepReceiveB0_support_props P Dh encT decT s
      (KeyPair.generate P.C s).publicKey sRef c rc L hinv hw res hres st' t' i' m' hsome
    exact ⟨by omega, fun pos _ => hprops.2.2.2.2 pos⟩
  · simp only [hB0, Bool.false_eq_true, ↓reduceIte] at hres
    by_cases hspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = true
    · simp only [hspk, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hres
      rw [hres] at hsome; cases hsome
    · have hnspk : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c = false :=
        Bool.eq_false_iff.mpr hspk
      simp only [hspk, Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hres
      rw [hres] at hsome
      have hB_ne : Q = .B → (sRef.st .B).epoch ≠ 0 := by
        intro hQ h0; subst hQ; simp [hpQ, h0] at hB0
      have hginv := gameInv_of_spkRefInv_win_false hinv hw
      have hstep := (receive_patchGameSpk_of_not_spk P ℓ s 0
        (KeyPair.generate P.C s).publicKey sRef Q c rc hginv hB_ne hnspk hnspk).2
        st' t' i' m' hsome
      refine ⟨hstep.1, fun pos hpos => ?_⟩
      have hginv' := (hstep.2 pos hpos).2
      refine spkRefInv_of_gameInv hginv' ?_
      dsimp only [GameState.accept, GameState.delete]
      cases Q with
      | A =>
        rw [Function.update_of_ne (by decide)]
        exact hinv.2
      | B =>
        rw [Function.update_self]
        change (P.receive (sRef.st .B) c rc).map _ = some (st', t', i', m') at hsome
        simp only [Option.map_eq_some_iff] at hsome
        rcases hsome with ⟨⟨g', t₀, i₀, m_raw⟩, hrecv_raw, htuple⟩
        rcases Prod.mk.inj htuple with ⟨rfl, _⟩
        have hp_eq := (receive_noZero_props P P.idA (sRef.st .B) c rc
          hginv.2.1.1 hginv.2.1.2.1 hginv.2.1.2.2.1 g' t₀ i₀ m_raw hrecv_raw).1
        exact hp_eq.trans hinv.2

end HInit

end CryptoVerification.E2E.SpkHop1
