/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins

/-!
# Hop 2 Phase 1 of the Hybrid Transition

Couples `hop2HybPrf k` and `hop2HybPrg (k + 1)` in Phase 1 while table `k + 1` is lazily sampled
off-chain before on-chain creation, transitioning to `Hop2Phase2Rel` up to collision cost.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CryptoGames.HMAC CryptoGames.MACScheme CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq
open CryptoGames.CKA (DHFun)

section Phases01

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

theorem bind_evalDist_true_le_of_support {α : Type} (mx : ProbComp α)
    (f g : α → ProbComp Bool) (ε : ℝ≥0∞)
    (h : ∀ a ∈ support mx, 𝒟[f a] {true} ≤ 𝒟[g a] {true} + ε) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} + ε := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, bind_assoc]
    exact bind_le_add_of_support (liftM (OracleSpec.query t)) _ _ ε fun u _ =>
      ih u fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

theorem bind_apply_le_add_of_evalDist_le_on_good {α : Type} (mx : ProbComp α)
    (f g : α → ProbComp Bool) (bad : α → Bool)
    (hle : ∀ c, bad c = false → 𝒟[f c] {true} ≤ 𝒟[g c] {true}) :
    𝒟[mx >>= f] {true} ≤
      𝒟[mx >>= g] {true} + 𝒟[mx >>= fun c => pure (bad c)] {true} := by
  let : MeasurableSpace α := ⊤
  have h1 : ∀ (k : α → ProbComp Bool),
      𝒟[mx >>= k] {true} = ∫⁻ c, 𝒟[k c] {true} ∂𝒟[mx] := fun k => by
    rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable]
  rw [h1 f, h1 g, h1 (fun c => pure (bad c)),
    ← MeasureTheory.lintegral_add_left Measurable.of_discrete]
  refine MeasureTheory.lintegral_mono fun c => ?_
  rcases hbc : bad c
  · exact (hle c hbc).trans le_self_add
  · have htrue : 𝒟[(pure true : ProbComp Bool)] {true} = 1 := by simp
    rw [htrue]
    calc 𝒟[f c] {true} ≤ 𝒟[f c] Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := evalDist_apply_univ_eq_one _
      _ ≤ 𝒟[g c] {true} + 1 := le_add_self

theorem bind_or_evalDist_true_le {α : Type} (mx : ProbComp α) (b1 b2 : α → Bool) :
    𝒟[mx >>= fun a => pure (b1 a || b2 a)] {true} ≤
      𝒟[mx >>= fun a => pure (b1 a)] {true} + 𝒟[mx >>= fun a => pure (b2 a)] {true} := by
  refine bind_apply_le_add_of_evalDist_le_on_good mx
    (fun a => pure (b1 a || b2 a)) (fun a => pure (b1 a)) b2 (fun a hb2 => ?_)
  rw [hb2, Bool.or_false]

theorem evalDist_bind_unif_swap {α β : Type} [SampleableType α]
    (mx : ProbComp β) (f : α → β → ProbComp Bool) :
    𝒟[($ᵗ α : ProbComp α) >>= fun a => mx >>= fun b => f a b] {true} =
      𝒟[mx >>= fun b => ($ᵗ α : ProbComp α) >>= fun a => f a b] {true} := by
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ α) mx]

theorem bind_unif_swap_evalDist_true_le {α β : Type} [SampleableType α]
    (mx : ProbComp β) (f g : α → β → ProbComp Bool) (ε : ℝ≥0∞)
    (h : ∀ y ∈ support mx,
      𝒟[($ᵗ α : ProbComp α) >>= fun x => f x y] {true} ≤
      𝒟[($ᵗ α : ProbComp α) >>= fun x => g x y] {true} + ε) :
    𝒟[($ᵗ α : ProbComp α) >>= fun x => mx >>= fun y => f x y] {true} ≤
    𝒟[($ᵗ α : ProbComp α) >>= fun x => mx >>= fun y => g x y] {true} + ε := by
  rw [evalDist_bind_unif_swap mx f, evalDist_bind_unif_swap mx g]
  exact bind_evalDist_true_le_of_support mx _ _ ε h

/-! ## `hop2Recv` decomposition -/

omit [SampleableType Pt] in
theorem hop2Recv_run_of_le_made_none {ℓ : ℕ} (P : Params Bytes PQC)
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
    (hmade : st.2.made.lookup (t, Dh.dh (st.2.coins g.party) T) = none) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st =
      (fun r => (hop2OffChainOut P ℓ g msg sc rc r.1, r.2)) <$>
        (hop2Lazy t (Dh.dh (st.2.coins g.party) T)).run st := by
  have hkey : hop2LazyKey P Dh encT decT h g c st =
      some ((t, Dh.dh (st.2.coins g.party) T), msg, sc) := by
    unfold hop2LazyKey
    simp [htry, hidx, hfind, hdec, hT, hsc, hQ0, htle, hmade]
  simpa only [withLazy_self] using
    hop2Recv_run_of_hop2LazyKey_some P Dh encT decT h g c rc st.2.lazy st
      (t, Dh.dh (st.2.coins g.party) T) msg sc hkey

def hop2CreateOutL (P : Params Bytes PQC) (ℓ : ℕ) (g : GhostState Bytes)
    (msg : SignalMessage) (sc : SenderChain) (rc ckR u : BitVec 256) : Hop2Out Pt ℓ :=
  let (rk2, ckS) := Ratchet.rootExpand P.C.F (keyToBytes32 u)
  let prev := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
  let sess' : SessionState Bytes :=
    { g.session with
      previousCounter := prev
      rootKey := rk2
      receiverChains := RatchetState.evictReceiverChains
        (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
      senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ }
  match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess'
      with
  | (.error _, _) => none
  | (.ok m, s_out) =>
    let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
      ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
    some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
      g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨none, rc, none⟩)

def hop2CreateOutChain (P : Params Bytes PQC) (ℓ : ℕ) (j : ℕ) (Q_create : Pt)
    (g : GhostState Bytes) (msg : SignalMessage) (sc : SenderChain) (rc ckR ckS : BitVec 256) :
    Hop2Out Pt ℓ :=
  let prev := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
  let sess' : SessionState Bytes :=
    { g.session with
      previousCounter := prev
      rootKey := 0
      receiverChains := RatchetState.evictReceiverChains
        (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
      senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ }
  match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess'
      with
  | (.error _, _) => none
  | (.ok m, s_out) =>
    let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
      ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
    some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
      g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m),
      some ⟨some (j + 1), rc, some ((j, Q_create), ckS)⟩)

def hop2SteppedGhost (P : Params Bytes PQC) (g : GhostState Bytes)
    (s_base : SessionState Bytes) (rc : BitVec 256) (rk2 : Ratchet.RootKey) (ckS : BitVec 256) :
    GhostState Bytes :=
  let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
    ((g.chainEpochs.length + 1) - s_base.receiverChains.length)
  { g with
    session := { s_base with
      rootKey := rk2
      senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ }
    epoch := g.epoch + 1
    chainEpochs := epochs }

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2CreateOutL_eq_of_tryDecrypt {ℓ : ℕ} (P : Params Bytes PQC)
    (g : GhostState Bytes) (msg : SignalMessage) (sc : SenderChain)
    (rc ckR u : BitVec 256)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true) :
    let prev := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
    let (rk2, ckS) := Ratchet.rootExpand P.C.F (keyToBytes32 u)
    hop2CreateOutL (Pt := Pt) P ℓ g msg sc rc ckR u =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper 0 (steppedSessBase g msg prev ckR) with
      | (.error _, _) => none
      | (.ok m, s_base) =>
        some ((hop2SteppedGhost P g s_base rc rk2 ckS,
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨none, rc, none⟩) := by
  intro prev
  have hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
      none :=
    Option.isNone_iff_eq_none.mp hfind
  unfold hop2CreateOutL hop2SteppedGhost
  dsimp only []
  have hstep := tryDecryptFromRecord_steppedSess P g msg rc prev
    (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1 ckR
    (some ⟨KeyPair.generate P.C rc, ⟨(Ratchet.rootExpand P.C.F (keyToBytes32 u)).2, 0⟩⟩) hnone
  change (match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
      rc
      { steppedSessBase g msg prev ckR with
        rootKey := (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
        senderChain := some ⟨KeyPair.generate P.C rc,
            ⟨(Ratchet.rootExpand P.C.F (keyToBytes32 u)).2, 0⟩⟩ } with
    | (.error _, _) => none
    | (.ok m, s_out) => _) = _
  dsimp only [] at hstep
  rw [hstep, tryDecryptFromRecord_steppedSessBase_rc_irrel P g msg rc prev ckR hnone]
  rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
    msg .whisper 0 (steppedSessBase g msg prev ckR) with ⟨r_tr, s_base⟩
  cases r_tr <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2CreateOutChain_eq_of_tryDecrypt {ℓ : ℕ} (P : Params Bytes PQC)
    (j : ℕ) (Q_create : Pt)
    (g : GhostState Bytes) (msg : SignalMessage) (sc : SenderChain)
    (rc ckR ckS : BitVec 256)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true) :
    let prev := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
    hop2CreateOutChain (Pt := Pt) P ℓ j Q_create g msg sc rc ckR ckS =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper 0 (steppedSessBase g msg prev ckR) with
      | (.error _, _) => none
      | (.ok m, s_base) =>
        some ((hop2SteppedGhost P g s_base rc 0 ckS,
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m),
          some ⟨some (j + 1), rc, some ((j, Q_create), ckS)⟩) := by
  intro prev
  have hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
      none :=
    Option.isNone_iff_eq_none.mp hfind
  unfold hop2CreateOutChain hop2SteppedGhost
  dsimp only []
  have hstep := tryDecryptFromRecord_steppedSess P g msg rc prev 0 ckR
    (some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩) hnone
  change (match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
      rc
      { steppedSessBase g msg prev ckR with
        rootKey := 0
        senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ } with
    | (.error _, _) => none
    | (.ok m, s_out) => _) = _
  dsimp only [] at hstep
  rw [hstep, tryDecryptFromRecord_steppedSessBase_rc_irrel P g msg rc prev ckR hnone]
  rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
    msg .whisper 0 (steppedSessBase g msg prev ckR) with ⟨r_tr, s_base⟩
  cases r_tr <;> rfl

theorem hop2Recv_run_at_create_prf {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (k : ℕ) (rc_L : Ratchet.RootKey × BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : SenderChain) (ckR : BitVec 256)
    (hidx : st.2.idx g.party = some k)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : g.session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0)
    (hmade : st.2.made.lookup (k, Dh.dh (st.2.coins g.party) T) = some ckR) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st =
      (fun u => (hop2CreateOutL P ℓ g msg sc rc ckR u, st)) <$>
        evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh rc T) := by
  have hM := CryptoGames.LibsignalSM.Proofs.Refinement.libX25519Rel_model hX
  have hT0 : T ≠ 0 := fun h0 => hT (Or.inl h0)
  have hrc0 : Dh.dh rc T ≠ 0 := hM.dh_ne_zero rc T hT0
  have hnotlt : ¬ (k + 1 < k) := by omega
  unfold hop2Recv hop2DH hop2RecvHalf hop2SendHalf hop2CreateOutL
  simp only [htry, StateT.run_bind, StateT.run_get, pure_bind, hidx, hfind, ↓reduceIte,
    hdec, hT, hsc, hQ0, hop2HybPrf_k, le_refl, hmade, StateT.run_pure, stateT_lift_run_hop2,
    hrc0, hnotlt, Nat.add_one_ne_self, hop2HybPrf_step, map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun u => ?_
  dsimp only [Function.comp_apply]
  rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
    msg .whisper rc _ with ⟨r_tr, s_out⟩
  cases r_tr <;> simp [StateT.run_pure]

theorem hop2Recv_run_of_succ_lt_made_some {ℓ : ℕ} (P : Params Bytes PQC)
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
    (hmade : st.2.made.lookup (t, Dh.dh (st.2.coins g.party) T) = some ckR) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st =
      (fun ckS => (hop2CreateOutChain P ℓ (t + 1) (Dh.dh rc T) g msg sc rc ckR ckS, st)) <$>
        hop2Unif (Pt := Pt) := by
  have hM := CryptoGames.LibsignalSM.Proofs.Refinement.libX25519Rel_model hX
  have hT0 : T ≠ 0 := fun h0 => hT (Or.inl h0)
  have hrc0 : Dh.dh rc T ≠ 0 := hM.dh_ne_zero rc T hT0
  have htle : t ≤ h.k := by omega
  unfold hop2Recv hop2DH hop2RecvHalf hop2SendHalf hop2CreateOutChain
  simp only [htry, StateT.run_bind, StateT.run_get, pure_bind, hidx, hfind, ↓reduceIte,
    hdec, hT, hsc, hQ0, htle, hmade, StateT.run_pure, stateT_lift_run_hop2,
    hrc0, htlt, map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun ckS => ?_
  dsimp only [Function.comp_apply]
  rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
    msg .whisper rc _ with ⟨r_tr, s_out⟩
  cases r_tr <;> simp [StateT.run_pure]

theorem hop2Recv_run_of_succ_eq_made_some {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (h : Hop2Hyb Pt) (t : ℕ)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : SenderChain) (ckR : BitVec 256)
    (hidx : st.2.idx g.party = some t)
    (hteq : t + 1 = h.k)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : g.session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0)
    (hmade : st.2.made.lookup (t, Dh.dh (st.2.coins g.party) T) = some ckR) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st =
      pure (hop2CreateOutChain P ℓ (t + 1) (Dh.dh rc T) g msg sc rc ckR h.chall.2, st) := by
  have hM := CryptoGames.LibsignalSM.Proofs.Refinement.libX25519Rel_model hX
  have hT0 : T ≠ 0 := fun h0 => hT (Or.inl h0)
  have hrc0 : Dh.dh rc T ≠ 0 := hM.dh_ne_zero rc T hT0
  have htle : t ≤ h.k := by omega
  unfold hop2Recv hop2DH hop2RecvHalf hop2SendHalf hop2CreateOutChain
  simp only [htry, StateT.run_bind, StateT.run_get, pure_bind, hidx, hfind, ↓reduceIte,
    hdec, hT, hsc, hQ0, htle, hmade, StateT.run_pure, stateT_lift_run_hop2,
    hrc0, hteq, lt_self_iff_false]
  rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
    msg .whisper rc _ with ⟨r_tr, s_out⟩
  cases r_tr <;> rfl

end Phases01

end CryptoVerification.E2E.SpkHop1

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CryptoGames.HMAC CryptoGames.MACScheme CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq
open CryptoGames.CKA (DHFun)

section Phase1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

/-! ## Phase 1 -/

/-- Full Hop 2 game invariant: `Hop2GameInv` plus `Hop2WindowInv` on the game state. -/
structure Hop2FullInv {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (st : Hop2State Pt ℓ) : Prop extends Hop2GameInv P decT encT st where
  winInv : Hop2WindowInv P st.1

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2FullInv_init {ℓ : ℕ} (P : Params Bytes PQC)
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
    Hop2FullInv P decT encT (initSt, aux0) :=
  ⟨hop2GameInv_init P decT encT b ck0 x alice pqr ck1 I0,
   hop2WindowInv_init P b 0 ck0 x alice pqr ck1⟩

theorem transmitR_support_hop2FullInv {ℓ : ℕ} (P : Params Bytes PQC)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (x : Party × CBC.Plain ℓ × Option PQC)
    (st : Hop2State Pt ℓ) (hinv : Hop2FullInv P decT encT st) :
    ∀ z ∈ support ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st.1),
      Hop2FullInv P decT encT (z.2, st.2) :=
  fun z hz =>
    ⟨transmitR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep x st
        hinv.toHop2GameInv z hz,
     transmitR_support_hop2WindowInv P hcodec hL decT encT qep x st hinv.toHop2GameInv hinv.winInv z
         hz⟩

theorem challR_support_hop2FullInv {ℓ : ℕ} (P : Params Bytes PQC)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (st : Hop2State Pt ℓ) (hinv : Hop2FullInv P decT encT st) :
    ∀ z ∈ support ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st.1),
      Hop2FullInv P decT encT (z.2, st.2) :=
  fun z hz =>
    ⟨challR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep x st hinv.toHop2GameInv z
        hz,
     challR_support_hop2WindowInv P hcodec hL decT encT qep x st hinv.toHop2GameInv hinv.winInv z
         hz⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrR_support_hop2FullInv {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (x : Party)
    (st : Hop2State Pt ℓ) (hinv : Hop2FullInv P decT encT st) :
    ∀ z ∈ support ((SM.corrR (configRefuseEarlyBobCorr decT encT) x).run st.1),
      Hop2FullInv P decT encT (z.2, st.2) :=
  fun z hz =>
    ⟨corrR_support_hop2GameInv P decT encT x st hinv.toHop2GameInv z hz,
     corrR_support_hop2WindowInv P decT encT x st.1 hinv.winInv z hz⟩

def badDeliverRc {ℓ : ℕ} (P : Params Bytes PQC) (st : Hop2State Pt ℓ)
    (Q : Party) (rc : BitVec 256) : Bool :=
  decide ((st.1.st Q.other).session.receiverChains.length ≤ 5) &&
    hasKeyInChainsBool (KeyPair.generate P.C rc).publicKey
      (st.1.st Q.other).session.receiverChains

theorem badDeliverRc_prob_le {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (st : Hop2State Pt ℓ) (Q : Party) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
      fun rc => pure (badDeliverRc P st Q rc)] {true} ≤
      (5 : ℝ≥0∞) * hop2CreateCollUnit Dh := by
  unfold badDeliverRc
  by_cases hlen : (st.1.st Q.other).session.receiverChains.length ≤ 5
  · simp only [decide_eq_true hlen, Bool.true_and]
    have hcs_le : ((st.1.st Q.other).session.receiverChains.length : ℝ≥0∞) ≤ 5 :=
      Nat.cast_le.mpr hlen
    exact ((hasKeyInChainsBool_prob_le_hop2GuessUnit P Dh encPt decT encT hX hdec _).trans
      (mul_le_mul_of_nonneg_right hcs_le zero_le)).trans
      (mul_le_mul_of_nonneg_left (hop2GuessUnit_le_hop2CreateCollUnit P Dh encPt encT hX) zero_le)
  · simp [decide_eq_false hlen]

theorem bind_evalDist_true_le_of_good_rc {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (st : Hop2State Pt ℓ) (Q : Party)
    (f g : BitVec 256 → ProbComp Bool) (d ε : ℝ≥0∞)
    (hd : d + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (h : ∀ rc, badDeliverRc P st Q rc = false → 𝒟[f rc] {true} ≤ 𝒟[g rc] {true} + d) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= f] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= g] {true} + ε := by
  have h1 := (bind_apply_le_add_of_evalDist_le_on_good_window ($ᵗ BitVec 256) f g
    (badDeliverRc P st Q) d h).trans
    (add_le_add_right (badDeliverRc_prob_le P Dh encPt decT encT hX hdec st Q) _)
  rw [add_assoc] at h1
  exact h1.trans (add_le_add le_rfl hd)

theorem bind_unif_swap_evalDist_true_le_of_good_rc {α : Type} [SampleableType α]
    {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (st : Hop2State Pt ℓ) (Q : Party)
    (f g : α → BitVec 256 → ProbComp Bool) (d ε : ℝ≥0∞)
    (hd : d + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (h : ∀ rc, badDeliverRc P st Q rc = false →
      𝒟[($ᵗ α : ProbComp α) >>= fun x => f x rc] {true} ≤
      𝒟[($ᵗ α : ProbComp α) >>= fun x => g x rc] {true} + d) :
    𝒟[($ᵗ α : ProbComp α) >>= fun x => ($ᵗ BitVec 256 :
        ProbComp (BitVec 256)) >>= fun rc => f x rc] {true} ≤
    𝒟[($ᵗ α : ProbComp α) >>= fun x => ($ᵗ BitVec 256 :
        ProbComp (BitVec 256)) >>= fun rc => g x rc] {true} + ε := by
  rw [evalDist_bind_unif_swap ($ᵗ BitVec 256) f, evalDist_bind_unif_swap ($ᵗ BitVec 256) g]
  exact bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st Q _ _ d ε hd h

def IsDeliverInTransitOrInjectPost {ℓ : ℕ} (P : Params Bytes PQC) (qep : ℕ) (s : BitVec 256)
    (Q : Party) (c : Bytes) (st1 : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ →
        Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ) : Prop :=
  (∃ r, st1.inTransit Q.other c = some r ∧ post = hop2DeliverPost P s Q c (st1.st Q) r) ∨
    post = hop2InjectPost P qep s Q c (st1.st Q)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem IsDeliverInTransitOrInjectPost.toIsDeliverOrInjectPost {ℓ : ℕ} {P : Params Bytes PQC}
    {qep : ℕ} {s : BitVec 256} {Q : Party} {c : Bytes}
    {st1 : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverInTransitOrInjectPost (Pt := Pt) P qep s Q c st1 post) :
    IsDeliverOrInjectPost (Pt := Pt) P qep s Q c (st1.st Q) post := by
  rcases hpost with ⟨r, _, rfl⟩ | rfl
  · exact Or.inl ⟨r, rfl⟩
  · exact Or.inr rfl

def IsGoodDeliverOrInjectPost {ℓ : ℕ} (P : Params Bytes PQC)
    (qep : ℕ) (s : BitVec 256) (Q : Party) (c : Bytes) (rc : BitVec 256)
    (st : Hop2State Pt ℓ)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ →
        Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ) : Prop :=
  badDeliverRc P st Q rc = false ∧
    IsDeliverInTransitOrInjectPost (Pt := Pt) P qep s Q c st.1 post

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem IsDeliverInTransitOrInjectPost.withGoodRc {ℓ : ℕ} {P : Params Bytes PQC}
    {qep : ℕ} {s : BitVec 256} {Q : Party} {c : Bytes} {rc : BitVec 256}
    {st : Hop2State Pt ℓ}
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverInTransitOrInjectPost (Pt := Pt) P qep s Q c st.1 post)
    (hgood : badDeliverRc P st Q rc = false) :
    IsGoodDeliverOrInjectPost (Pt := Pt) P qep s Q c rc st post :=
  ⟨hgood, hpost⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem IsGoodDeliverOrInjectPost.toIsDeliverOrInjectPost {ℓ : ℕ} {P : Params Bytes PQC}
    {qep : ℕ} {s : BitVec 256} {Q : Party} {c : Bytes} {rc : BitVec 256}
    {st : Hop2State Pt ℓ}
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s Q c rc st post) :
    IsDeliverOrInjectPost (Pt := Pt) P qep s Q c (st.1.st Q) post :=
  hpost.2.toIsDeliverOrInjectPost

omit [SampleableType Pt] in
theorem IsGoodDeliverOrInjectPost.preserves_hop2FullInv {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt}
    {qep : ℕ} {s : BitVec 256} {h : Hop2Hyb Pt}
    {Q : Party} {c : Bytes} {rc : BitVec 256} {st : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)}
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s Q c rc st post)
    (hinv : Hop2FullInv P decT encT st)
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st)).run tbl)) :
    Hop2FullInv P decT encT (post z.1.1 z.1.2).2 := by
  refine ⟨hpost.toIsDeliverOrInjectPost.preserves_hop2GameInv hinv.toHop2GameInv z hz, ?_⟩
  rcases hpost.2 with ⟨r, hin, rfl⟩ | rfl
  · rcases hinv.winInv with hpos | hcore
    · have hdone := hop2Recv_support_done P Dh encT decT h (st.1.st Q) c rc st tbl z hz
      cases ho : z.1.1 with
      | none => dsimp only [hop2DeliverPost]; rw [hdone.1]; exact Or.inl hpos
      | some val =>
        rcases val with ⟨⟨st', t', i', m'⟩, u⟩
        left
        dsimp only [hop2DeliverPost, SM.GameState.accept, SM.GameState.delete]
        rw [hdone.1]
        cases Q with
        | A => rw [Function.update_self]; exact (hdone.2.2 st' t' i' m' u ho).2 hpos
        | B => rw [Function.update_of_ne (by decide)]; exact hpos
    · have hlen : (st.1.st Q.other).session.receiverChains.length ≤ 5 := by
        cases Q.other with
        | A => exact hcore.nA_le
        | B => exact hcore.csB_le
      have hgood := hpost.1
      have hkey : hasKeyInChainsBool (KeyPair.generate P.C rc).publicKey
          (st.1.st Q.other).session.receiverChains = false := by
        unfold badDeliverRc at hgood
        simpa [decide_eq_true hlen] using hgood
      exact hop2DeliverPost_preserves_hop2WindowInv P Dh encT decT s h Q c r rc st tbl
        (Or.inr hcore) hin hkey z hz
  · exact hop2InjectPost_preserves_hop2WindowInv P Dh encT decT qep s h Q c rc st tbl
      hinv.winInv z hz

/-- Phase 1 state relation between `hop2HybPrf k` and `hop2HybPrg (k + 1)` before table `k + 1` is created. -/
structure Hop2Phase1Rel {ℓ : ℕ} (P : Params Bytes PQC) (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (k : ℕ)
    (st_L : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) (st_R : Hop2State Pt ℓ) : Prop where
  inv_R : Hop2FullInv P decT encT st_R
  st1_eq : st_L.1 = st_R.1
  bad_eq : st_L.2.bad = st_R.2.bad
  idx_eq : st_L.2.idx = st_R.2.idx
  coins_eq : st_L.2.coins = st_R.2.coins
  made_eq : st_L.2.made = st_R.2.made
  idx_pk_R : st_R.2.idx (partyOfParity k) = none ∨ st_R.2.idx (partyOfParity k) = some k
  idx_pk1_R : st_R.2.idx (partyOfParity (k + 1)) = none ∨
    st_R.2.idx (partyOfParity (k + 1)) = some (k + 1)
  made_k1_none : ∀ Q, st_R.2.made.lookup (k + 1, Q) = none
  lazy_le_k : ∀ t ≤ k, ∀ Q, st_L.2.lazy.lookup (t, Q) = st_R.2.lazy.lookup (t, Q)
  tbl_eq : ∀ Q, tbl.lookup Q = st_R.2.lazy.lookup (k + 1, Q)

omit [Zero Pt] [SampleableType Pt] in
theorem Hop2Phase1Rel.of_st1_step {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {k : ℕ}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (s_R' : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hinv' : Hop2FullInv P decT encT (s_R', st_R.2)) :
    Hop2Phase1Rel P decT encT k (s_R', st_L.2) tbl (s_R', st_R.2) :=
  ⟨hinv', rfl, hrel.bad_eq, hrel.idx_eq, hrel.coins_eq, hrel.made_eq,
   hrel.idx_pk_R, hrel.idx_pk1_R, hrel.made_k1_none, hrel.lazy_le_k, hrel.tbl_eq⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem withLazy_nil_eq_of_fields {ℓ : ℕ} {st_L st_R : Hop2State Pt ℓ}
    (hst1 : st_L.1 = st_R.1) (hbad : st_L.2.bad = st_R.2.bad)
    (hidx : st_L.2.idx = st_R.2.idx) (hcoins : st_L.2.coins = st_R.2.coins)
    (hmade : st_L.2.made = st_R.2.made) :
    withLazy [] st_L = withLazy [] st_R := by
  rcases st_L with ⟨sL, lL, mL, iL, cL, bL⟩
  rcases st_R with ⟨sR, lR, mR, iR, cR, bR⟩
  dsimp only [] at hst1 hbad hidx hcoins hmade
  subst hst1; subst hbad; subst hidx; subst hcoins; subst hmade
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem hop2Phase1Rel_of_post {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k : ℕ} {Q : Party}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    {c : Bytes} {post : Hop2Out Pt ℓ → Hop2State Pt ℓ →
        Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverOrInjectPost (Pt := Pt) P qep s Q c (st_R.1.st Q) post)
    (o : Hop2Out Pt ℓ) (st2_L st2_R : Hop2State Pt ℓ) (tbl' : List (Pt × BitVec 256))
    (hinv' : Hop2FullInv P decT encT (post o st2_R).2)
    (hL : st2_L.1 = st_L.1 ∧ st2_L.2.bad = st_L.2.bad ∧ st2_L.2.idx = st_L.2.idx ∧
      st2_L.2.coins = st_L.2.coins ∧ st2_L.2.made = st_L.2.made)
    (hR : st2_R.1 = st_R.1 ∧ st2_R.2.bad = st_R.2.bad ∧ st2_R.2.idx = st_R.2.idx ∧
      st2_R.2.coins = st_R.2.coins ∧ st2_R.2.made = st_R.2.made)
    (hlazy_le_k : ∀ t ≤ k, ∀ Q', st2_L.2.lazy.lookup (t, Q') = st2_R.2.lazy.lookup (t, Q'))
    (htbl_eq : ∀ Q', tbl'.lookup Q' = st2_R.2.lazy.lookup (k + 1, Q'))
    (ho_upd : ∀ x ∈ o, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩) :
    (post o st2_L).1 = (post o st2_R).1 ∧
    Hop2Phase1Rel P decT encT k (post o st2_L).2 tbl' (post o st2_R).2 := by
  have hp := hpost.isHop2Post
  have hnil : withLazy [] st2_L = withLazy [] st2_R :=
    withLazy_nil_eq_of_fields
      (hL.1.trans (hrel.st1_eq.trans hR.1.symm))
      (hL.2.1.trans (hrel.bad_eq.trans hR.2.1.symm))
      (hL.2.2.1.trans (hrel.idx_eq.trans hR.2.2.1.symm))
      (hL.2.2.2.1.trans (hrel.coins_eq.trans hR.2.2.2.1.symm))
      (hL.2.2.2.2.trans (hrel.made_eq.trans hR.2.2.2.2.symm))
  have hcomm_L : post o st2_L =
      ((post o (withLazy [] st2_L)).1, withLazy st2_L.2.lazy (post o (withLazy [] st2_L)).2) := by
    simpa only [withLazy_withLazy,
        withLazy_self] using hp.withLazy_comm st2_L.2.lazy o (withLazy [] st2_L)
  have hcomm_R : post o st2_R =
      ((post o (withLazy [] st2_R)).1, withLazy st2_R.2.lazy (post o (withLazy [] st2_R)).2) := by
    simpa only [withLazy_withLazy,
        withLazy_self] using hp.withLazy_comm st2_R.2.lazy o (withLazy [] st2_R)
  have hout_eq : (post o st2_L).1 = (post o st2_R).1 := by
    rw [hcomm_L, hcomm_R, hnil]
  have hst1_eq : (post o st2_L).2.1 = (post o st2_R).2.1 := by
    rw [hcomm_L, hcomm_R, hnil]; rfl
  have hbad_eq : (post o st2_L).2.2.bad = (post o st2_R).2.2.bad := by
    rw [hcomm_L, hcomm_R, hnil]; rfl
  have hidx_eq : (post o st2_L).2.2.idx = (post o st2_R).2.2.idx := by
    rw [hcomm_L, hcomm_R, hnil]; rfl
  have hcoins_eq : (post o st2_L).2.2.coins = (post o st2_R).2.2.coins := by
    rw [hcomm_L, hcomm_R, hnil]; rfl
  have hmade_eq : (post o st2_L).2.2.made = (post o st2_R).2.2.made := by
    rw [hcomm_L, hcomm_R, hnil]; rfl
  have hlazy_L : (post o st2_L).2.2.lazy = st2_L.2.lazy := by
    rw [hcomm_L]; rfl
  have hlazy_R : (post o st2_R).2.2.lazy = st2_R.2.lazy := by
    rw [hcomm_R]; rfl
  have h_aux_R : ((post o st2_R).2.2.idx = st_R.2.idx ∧ (post o st2_R).2.2.made = st_R.2.made) ∨
      ((post o st2_R).2.2.idx = Function.update st_R.2.idx Q none ∧
       (post o st2_R).2.2.made = st_R.2.made) := by
    cases ho_case : o with
    | none =>
      rw [hp.on_none st2_R]
      exact Or.inl ⟨hR.2.2.1, hR.2.2.2.2⟩
    | some val =>
      rcases val with ⟨⟨st', t', i', m'⟩, u⟩
      rcases (hp.on_some st' t' i' m' u st2_R).2.2 with ⟨_, hidx', _, hmade'⟩ | ⟨_, hidx', _,
          hmade'⟩
      · exact Or.inl ⟨hidx'.trans hR.2.2.1, hmade'.trans hR.2.2.2.2⟩
      · rcases ho_upd ((st', t', i', m'), u) (by simp [ho_case]) with hnone | ⟨rc', hsome⟩
        · dsimp only [] at hnone; subst hnone
          exact Or.inl ⟨hidx'.trans hR.2.2.1, hmade'.trans hR.2.2.2.2⟩
        · dsimp only [] at hsome; subst hsome
          refine Or.inr ⟨?_, ?_⟩
          · rw [hidx']; dsimp only [hop2Commit]; rw [hR.2.2.1]
          · rw [hmade']; dsimp only [hop2Commit]; exact hR.2.2.2.2
  refine ⟨hout_eq, ⟨hinv', hst1_eq, hbad_eq, hidx_eq, hcoins_eq, hmade_eq, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rcases h_aux_R with ⟨hi, _⟩ | ⟨hi, _⟩
    · rw [hi]; exact hrel.idx_pk_R
    · rw [hi]
      by_cases hQ : partyOfParity k = Q
      · subst hQ; simp
      · rw [Function.update_of_ne hQ]; exact hrel.idx_pk_R
  · rcases h_aux_R with ⟨hi, _⟩ | ⟨hi, _⟩
    · rw [hi]; exact hrel.idx_pk1_R
    · rw [hi]
      by_cases hQ : partyOfParity (k + 1) = Q
      · subst hQ; simp
      · rw [Function.update_of_ne hQ]; exact hrel.idx_pk1_R
  · intro Q'
    rcases h_aux_R with ⟨_, hm⟩ | ⟨_, hm⟩ <;> (rw [hm]; exact hrel.made_k1_none Q')
  · intro t ht Q'
    rw [hlazy_L, hlazy_R]; exact hlazy_le_k t ht Q'
  · intro Q'
    rw [hlazy_R]; exact htbl_eq Q'

omit [Zero Pt] [SampleableType Pt] in
theorem patchGamePartyIdx_eq_self_of_phase1 {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {k : ℕ}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R) (rk : Ratchet.RootKey) :
    patchGamePartyIdx (k + 2) rk st_R.2.idx st_R.1 = st_R.1 := by
  have hne : ∀ Q : Party, st_R.2.idx Q ≠ some (k + 2) := by
    intro Q
    rcases party_eq_partyOfParity_or_succ k Q with rfl | rfl
    · rcases hrel.idx_pk_R with h0 | h1
      · simp [h0]
      · simp [h1]
    · rcases hrel.idx_pk1_R with h0 | h1
      · simp [h0]
      · simp [h1]
  unfold patchGamePartyIdx
  have hst : (fun Q => patchPartyIdx (k + 2) rk (st_R.2.idx Q) (st_R.1.st Q)) = st_R.1.st := by
    funext Q
    exact patchPartyIdx_of_ne (k + 2) rk (st_R.2.idx Q) (st_R.1.st Q) (hne Q)
  rw [hst]

omit [Zero Pt] [SampleableType Pt] in
theorem hop2Phase2Rel_of_create_commit {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k : ℕ} {u_chall : BitVec 256} {Q_create : Pt}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    {c : Bytes} {s_base : SessionState Bytes} {rc : BitVec 256}
    {m_plain : Bytes} {msg : SignalMessage}
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverOrInjectPost (Pt := Pt) P qep s (partyOfParity k) c
      (st_R.1.st (partyOfParity k)) post)
    (hcomm : (∃ r_rec, post =
        hop2DeliverPost P s (partyOfParity k) c (st_R.1.st (partyOfParity k)) r_rec) ∨
      (post = hop2InjectPost P qep s (partyOfParity k) c (st_R.1.st (partyOfParity k)) ∧
        ¬ (qep + 1 < (st_R.1.st (partyOfParity k)).epoch + 1) ∧
        st_R.1.trivial 3 ⟨(partyOfParity k).other, (st_R.1.st (partyOfParity k)).epoch + 1,
          msg.counter.toNat + 1⟩ = true))
    (hinv' : Hop2GameInv P decT encT
      (post (some ((hop2SteppedGhost P (st_R.1.st (partyOfParity k)) s_base rc 0
          (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2,
        (st_R.1.st (partyOfParity k)).epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain),
        some ⟨some (k + 2), rc,
          some ((k + 1, Q_create),
              (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2)⟩)) st_R).2) :
    let g := st_R.1.st (partyOfParity k)
    let rk_chall := (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).1
    let ck_chall := (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2
    let o_L : Hop2Out Pt ℓ :=
      some ((hop2SteppedGhost P g s_base rc rk_chall ck_chall,
        g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain), some ⟨none, rc, none⟩)
    let o_R : Hop2Out Pt ℓ :=
      some ((hop2SteppedGhost P g s_base rc 0 ck_chall,
        g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain),
        some ⟨some (k + 2), rc, some ((k + 1, Q_create), ck_chall)⟩)
    (post o_L st_L).1 = (post o_R st_R).1 ∧
    Hop2Phase2Rel P decT encT k u_chall Q_create
      (post o_L st_L).2 ((Q_create, u_chall) :: tbl) (post o_R st_R).2 := by
  intro g rk_chall ck_chall o_L o_R
  set Q := partyOfParity k
  set rk_chall := (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).1
  set ck_chall := (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2
  have hQ1_ne : partyOfParity (k + 1) ≠ Q := partyOfParity_succ_ne k
  have hst1 : st_L.1 = patchGamePartyIdx (k + 2) rk_chall st_R.2.idx st_R.1 := by
    rw [hrel.st1_eq, patchGamePartyIdx_eq_self_of_phase1 hrel rk_chall]
  have ho_map : o_L.map (·.1) = o_R.map (fun x =>
      (patchPartyIdx (k + 2) rk_chall ((hop2Commit st_R.2 Q x.2).idx Q) x.1.1, x.1.2)) := by
    dsimp only [o_L, o_R, Option.map, hop2Commit]
    rw [Function.update_self, patchPartyIdx_some_self]
    rfl
  have hother : ∀ x ∈ o_R, ∀ R ≠ Q, (hop2Commit st_R.2 Q x.2).idx R = st_R.2.idx R := by
    intro x hx R hR
    simp only [o_R, Option.mem_def, Option.some.injEq] at hx
    subst hx
    dsimp only [hop2Commit]
    exact Function.update_of_ne hR _ _
  have hstep := hpost.patchGamePartyIdx_step (k +
      2) rk_chall st_L st_R hst1 hrel.bad_eq o_L o_R ho_map hother
  have hcommit_R :
      (post o_L st_L).2.2.idx = Function.update st_L.2.idx Q none ∧
      (post o_L st_L).2.2.coins = Function.update st_L.2.coins Q rc ∧
      (post o_R st_R).2.2.idx = Function.update st_R.2.idx Q (some (k + 2)) ∧
      (post o_R st_R).2.2.coins = Function.update st_R.2.coins Q rc ∧
      (post o_R st_R).2.2.made = ((k + 1, Q_create), ck_chall) :: st_R.2.made := by
    rcases hcomm with ⟨r_rec, rfl⟩ | ⟨rfl, hqep, htriv⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · dsimp only [hop2InjectPost, o_L, o_R, g, Q] at hqep htriv ⊢
      rw [hrel.st1_eq]
      simp only [hqep, ↓reduceIte, htriv]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hstep.1, ⟨hinv', hstep.2.1, hstep.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hcommit_R.1, Function.update_self]
  · rw [hcommit_R.2.2.1, Function.update_self]; exact Or.inr rfl
  · rw [hcommit_R.1, hcommit_R.2.2.1, Function.update_of_ne hQ1_ne, Function.update_of_ne hQ1_ne,
      hrel.idx_eq]
  · rw [hcommit_R.2.2.1, Function.update_of_ne hQ1_ne]; exact hrel.idx_pk1_R
  · rw [hcommit_R.2.2.2.2]
    simp [List.lookup, ck_chall]
  · intro Q' hQ'
    rw [hcommit_R.2.2.2.2]
    have hne : (k + 1, Q') ≠ (k + 1, Q_create) := fun heq => hQ' (Prod.mk.inj heq).2
    simp [List.lookup, beq_eq_false_iff_ne.mpr hne, hrel.made_k1_none Q']
  · simp [List.lookup]
  · intro Q' hQ'
    rw [hstep.2.2.2.2.1]
    simp [List.lookup, beq_eq_false_iff_ne.mpr hQ', hrel.tbl_eq Q']
  · intro _
    rw [hcommit_R.2.1, hcommit_R.2.2.2.1, Function.update_of_ne hQ1_ne,
        Function.update_of_ne hQ1_ne, hrel.coins_eq]

omit [SampleableType Pt] in
theorem evalDist_runHop2_phase1_of_pure_recv {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (Q : Party) (c : Bytes) (rc : BitVec 256) (o : Hop2Out Pt ℓ)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s Q c rc st_R post)
    (hrun_L : (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k rc_L) (st_R.1.st Q) c rc).run st_L =
      pure (o, st_L))
    (hrun_R : ∀ u_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k +
          1) u_chall) (st_R.1.st Q) c rc).run st_R =
      pure (o, st_R))
    (ho_upd : ∀ x ∈ o, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa r) sR []] {true} + ε) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) (st_R.1.st Q) c rc).run st_L)).run tbl
      runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) (st_R.1.st Q) c rc).run st_R)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} + ε := by
  rw [hrun_L]
  simp only [hrun_R, simulateQ_pure, StateT.run_pure, pure_bind]
  have hsupp_R : ((o, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
          1) 0) (st_R.1.st Q) c rc).run st_R)).run []) := by
    rw [hrun_R 0]; simp [simulateQ_pure, StateT.run_pure]
  have hinv' : Hop2FullInv P decT encT (post o st_R).2 :=
    hpost.preserves_hop2FullInv hrel.inv_R ((o, st_R), []) hsupp_R
  have hpost_rel := hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost o st_L st_R tbl hinv'
    ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
    hrel.lazy_le_k hrel.tbl_eq ho_upd
  rw [hpost_rel.1]
  exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)

omit [SampleableType Pt] in
theorem evalDist_runHop2_phase1_of_lazy_pk1 {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
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
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s (partyOfParity (k + 1)) c rc st_R post)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa r) sR []] {true} + ε) :
    let Q1 := partyOfParity (k + 1)
    let g := st_R.1.st Q1
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L)).run tbl
      runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} + ε := by
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
    have hpost_rel := hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost o st_L st2_R ((Q_in,
        u) :: tbl) hinv'
      ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
      hlazy_le_k htbl_eq (h_upd u)
    rw [hpost_rel.1]
    exact ih' _ _ _ _ hpost_rel.2 (le_refl _)

omit [SampleableType Pt] in
theorem evalDist_runHop2_phase1_of_lazy_pk {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
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
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsGoodDeliverOrInjectPost (Pt := Pt) P qep s (partyOfParity k) c rc st_R post)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (ε : ℝ≥0∞)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa r) sR []] {true} + ε) :
    let Q := partyOfParity k
    let g := st_R.1.st Q
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L)).run tbl
      runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} + ε := by
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
    have hpost_rel :=
        hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost o st2_L st2_R tbl hinv'
      ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
      hlazy_le_k htbl_eq (h_upd u)
    rw [hpost_rel.1]
    exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2InjectPost_eq_of_not_commit {ℓ : ℕ} (P : Params Bytes PQC)
    (qep : ℕ) (s : BitVec 256) (Q : Party) (c : Bytes) (g₀ : GhostState Bytes)
    (st1' st2' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (u1 u2 : Option (Hop2Upd Pt)) (st : Hop2State Pt ℓ)
    (hnc : ¬ (¬ (qep + 1 < t') ∧ st.1.trivial 3 ⟨Q.other, t', i'⟩ = true)) :
    hop2InjectPost P qep s Q c g₀ (some ((st1', t', i', m'), u1)) st =
      hop2InjectPost P qep s Q c g₀ (some ((st2', t', i', m'), u2)) st := by
  dsimp only [hop2InjectPost]
  by_cases hqep : qep + 1 < t'
  · simp [hqep]
  · have htriv : st.1.trivial 3 ⟨Q.other, t', i'⟩ = false := by
      cases h : st.1.trivial 3 ⟨Q.other, t', i'⟩
      · rfl
      · exact absurd ⟨hqep, h⟩ hnc
    simp [hqep, htriv]

abbrev Hop2Phase2Bound (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ℓ qep : ℕ) (s : BitVec 256) (k : ℕ) (rc_L : Ratchet.RootKey × BitVec 256) : Prop :=
  ∀ (u_chall : BitVec 256) (Q_create : Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem : ℕ), SM.MakesAtMostQueries oa rem →
    ∀ (sL : Hop2State Pt ℓ) (tL : List (Pt × BitVec 256)) (sR : Hop2State Pt ℓ),
    Hop2Phase2Rel P decT encT k u_chall Q_create sL tL sR →
    Hop2WindowInv P sR.1 →
    𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) oa sL tL] {true} ≤
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) oa sR []] {true} +
      ((5 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh

theorem evalDist_runHop2_phase1_of_create_pk {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
    (hph2 : Hop2Phase2Bound P Dh encPt decT encT ℓ qep s k rc_L)
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
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsDeliverInTransitOrInjectPost (Pt := Pt) P qep s (partyOfParity k) c st_R.1 post)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem_next : ℕ) (hq_k : ∀ r, SM.MakesAtMostQueries (k_oa r) rem_next)
    (d_ih ε : ℝ≥0∞)
    (hd_ih : d_ih + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hd_ph2 : ((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
      ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤ ε)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa r) sR []] {true} + d_ih) :
    let Q := partyOfParity k
    let g := st_R.1.st Q
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L)).run tbl
      runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
        (post z.1.1 z.1.2).2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R)).run []
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) (k_oa (post z.1.1 z.1.2).1)
          (post z.1.1 z.1.2).2 z.2)] {true} + ε := by
  intro Q g
  have hidx_L : st_L.2.idx g.party = some k := by rw [hrel.idx_eq]; exact hidx_R
  have hQ0_L : Dh.dh (st_L.2.coins g.party) T ≠ 0 := by rw [hrel.coins_eq]; exact hQ0_R
  have hmade_L : st_L.2.made.lookup (k, Dh.dh (st_L.2.coins g.party) T) = some ckR := by
    rw [hrel.made_eq, hrel.coins_eq]; exact hmade_R
  have hrun_L : ∀ rc,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L =
      (fun u => (hop2CreateOutL P ℓ g msg sc rc ckR u, st_L)) <$>
        evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh rc T) := fun rc =>
    hop2Recv_run_at_create_prf P Dh encPt encT decT hX k rc_L g c rc st_L msg T sc ckR
      hidx_L htry hfind hdec_T hT hsc hQ0_L hmade_L
  have hrun_R : ∀ rc u_chall,
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R =
      pure (hop2CreateOutChain P ℓ (k + 1) (Dh.dh rc T) g msg sc rc ckR
        (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2, st_R) := fun rc u_chall =>
    hop2Recv_run_of_succ_eq_made_some P Dh encPt encT decT hX
      (hop2HybPrg P encPt (k + 1) u_chall) k g c rc st_R msg T sc ckR
      hidx_R rfl htry hfind hdec_T hT hsc hQ0_R hmade_R
  have hinv_step : ∀ rc u_chall, badDeliverRc P st_R Q rc = false →
      Hop2FullInv P decT encT
        (post (hop2CreateOutChain P ℓ (k + 1) (Dh.dh rc T) g msg sc rc ckR
          (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2) st_R).2 := by
    intro rc u_chall hgood_rc
    have hsupp : ((hop2CreateOutChain P ℓ (k + 1) (Dh.dh rc T) g msg sc rc ckR
        (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2, st_R), []) ∈
        support ((simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
              1) u_chall) g c rc).run st_R)).run []) := by
      rw [hrun_R rc u_chall]
      simp [simulateQ_pure, StateT.run_pure]
    exact (hpost.withGoodRc hgood_rc).preserves_hop2FullInv hrel.inv_R _ hsupp
  set prev := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
  have hout_L : ∀ rc u, hop2CreateOutL (Pt := Pt) P ℓ g msg sc rc ckR u =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper 0 (steppedSessBase g msg prev ckR) with
      | (.error _, _) => none
      | (.ok m, s_base) =>
        some ((hop2SteppedGhost P g s_base rc
          (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
          (Ratchet.rootExpand P.C.F (keyToBytes32 u)).2,
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨none, rc, none⟩) :=
    fun rc u => hop2CreateOutL_eq_of_tryDecrypt P g msg sc rc ckR u hfind
  have hout_R : ∀ rc ckS, hop2CreateOutChain (Pt := Pt) P ℓ (k +
      1) (Dh.dh rc T) g msg sc rc ckR ckS =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper 0 (steppedSessBase g msg prev ckR) with
      | (.error _, _) => none
      | (.ok m, s_base) =>
        some ((hop2SteppedGhost P g s_base rc 0 ckS,
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m),
          some ⟨some (k + 2), rc, some ((k + 1, Dh.dh rc T), ckS)⟩) :=
    fun rc ckS => hop2CreateOutChain_eq_of_tryDecrypt P (k +
        1) (Dh.dh rc T) g msg sc rc ckR ckS hfind
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
      (evalDist_runHop2_tbl_discard P Dh encT decT qep s (hop2HybPrf k rc_L)
        (k_oa (post none st_L).1) (post none st_L).2 tbl (Dh.dh rc T))
    dsimp only [] at hdisc
    rw [hdisc]
    have hinv0 : Hop2FullInv P decT encT (post none st_R).2 := by
      have h0 := hinv_step rc 0 hgood_rc
      rw [hout_R rc, htr0] at h0
      exact h0
    have hpost_rel :=
        hop2Phase1Rel_of_post hrel hpost.toIsDeliverOrInjectPost none st_L st_R tbl hinv0
      ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
      hrel.lazy_le_k hrel.tbl_eq (fun _ hx => by cases hx)
    rw [hpost_rel.1]
    exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)
  | ok m_plain =>
    by_cases hcomm : (∃ r_rec, post = hop2DeliverPost P s Q c g r_rec) ∨
        (post = hop2InjectPost P qep s Q c g ∧ ¬ (qep + 1 < g.epoch + 1) ∧
          st_R.1.trivial 3 ⟨Q.other, g.epoch + 1, msg.counter.toNat + 1⟩ = true)
    · have hM := CryptoGames.LibsignalSM.Proofs.Refinement.libX25519Rel_model hX
      have hT0 : T ≠ 0 := fun h0 => hT (Or.inl h0)
      have hbad_le : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
          fun rc => pure (badDeliverRc P st_R Q rc || (tbl.lookup (Dh.dh rc T)).isSome)] {true} ≤
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        (bind_or_evalDist_true_le ($ᵗ BitVec 256) _ _).trans
          (add_le_add (badDeliverRc_prob_le P Dh encPt decT encT hX hdec st_R Q)
            (dh_lookup_isSome_prob_le_hop2CreateCollUnit Dh hM.dh_ne_zero T hT0 tbl))
      have hstep := (bind_apply_le_add_of_evalDist_le_on_good_window ($ᵗ BitVec 256)
        (fun rc => do
          let z ← (simulateQ (lazyImpl (Pt := Pt))
            ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) g c rc).run st_L)).run tbl
          runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa (post z.1.1 z.1.2).1)
            (post z.1.1 z.1.2).2 z.2)
        (fun rc => ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => do
          let z ← (simulateQ (lazyImpl (Pt := Pt))
            ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall) g c rc).run st_R)).run []
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa (post z.1.1 z.1.2).1)
            (post z.1.1 z.1.2).2 z.2)
        (fun rc => badDeliverRc P st_R Q rc || (tbl.lookup (Dh.dh rc T)).isSome)
        (((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (fun rc hgood => by
          obtain ⟨hgood_rc, hgood_tbl⟩ := Bool.or_eq_false_iff.mp hgood
          rw [hrun_L rc, simulateQ_lazyImpl_map_evalQuery]
          have hlook : tbl.lookup (Dh.dh rc T) = none := by
            cases h : tbl.lookup (Dh.dh rc T) with
            | none => rfl
            | some v => rw [h] at hgood_tbl; cases hgood_tbl
          simp only [pure_bind, hlook, StateT.run_pure,
            map_eq_bind_pure_comp, Function.comp_apply, bind_assoc,
            hrun_R rc, simulateQ_pure]
          refine bind_evalDist_true_le_of_support ($ᵗ BitVec 256) _ _ _ fun u_chall _ => ?_
          rw [hout_L rc u_chall, hout_R rc, htr0]
          dsimp only []
          have hinv_u : Hop2FullInv P decT encT
              (post (some ((hop2SteppedGhost P g s_base rc 0
                (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2,
                g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain),
                some ⟨some (k + 2), rc, some ((k + 1, Dh.dh rc T),
                  (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2)⟩)) st_R).2 := by
            have h0 := hinv_step rc u_chall hgood_rc
            rw [hout_R rc, htr0] at h0
            exact h0
          have hph2_rel := hop2Phase2Rel_of_create_commit (s_base := s_base) (rc := rc)
            (u_chall := u_chall) (Q_create := Dh.dh rc T) (m_plain := m_plain) (msg := msg)
            hrel hpost.toIsDeliverOrInjectPost hcomm hinv_u.toHop2GameInv
          rw [hph2_rel.1]
          exact hph2 u_chall (Dh.dh rc T) _ rem_next (hq_k _) _ _ _ hph2_rel.2 hinv_u.winInv)).trans
        (add_le_add_right hbad_le _)
      rw [add_assoc] at hstep
      exact hstep.trans (add_le_add le_rfl hd_ph2)
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
            (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
            (Ratchet.rootExpand P.C.F (keyToBytes32 u)).2,
            g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain), some ⟨none, rc, none⟩)) st_L =
            post o_dummy st_L := fun u => by
          rw [hinj]
          exact hop2InjectPost_eq_of_not_commit P qep s Q c g _ _ _ _ _ _ _ st_L hnc_L
        have hpost_R_eq : ∀ u_chall, post (some ((hop2SteppedGhost P g s_base rc 0
            (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2,
            g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain),
            some ⟨some (k + 2), rc, some ((k + 1, Dh.dh rc T),
              (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2)⟩)) st_R =
            post o_dummy st_R := fun u_chall => by
          rw [hinj]
          exact hop2InjectPost_eq_of_not_commit P qep s Q c g _ _ _ _ _ _ _ st_R hnc_R
        simp only [hout_L rc, htr0, map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind,
          simulateQ_lazyImpl_evalQuery, simulateQ_pure, StateT.run_bind, StateT.run_pure,
          bind_assoc, pure_bind, hrun_R rc, hout_R rc, hpost_L_eq, hpost_R_eq]
        have hdisc := congrArg (fun d => d {true})
          (evalDist_runHop2_tbl_discard P Dh encT decT qep s (hop2HybPrf k rc_L)
            (k_oa (post o_dummy st_L).1) (post o_dummy st_L).2 tbl (Dh.dh rc T))
        dsimp only [] at hdisc
        rw [hdisc]
        have hinv0 : Hop2FullInv P decT encT (post o_dummy st_R).2 := by
          have h0 := hinv_step rc 0 hgood_rc
          rw [hout_R rc, htr0, hpost_R_eq 0] at h0
          exact h0
        have ho_upd : ∀ x ∈ o_dummy, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩ := by
          intro x hx
          simp only [o_dummy, Option.mem_def, Option.some.injEq] at hx
          subst hx; exact Or.inl rfl
        have hpost_rel := hop2Phase1Rel_of_post hrel (Or.inr hinj) o_dummy st_L st_R tbl hinv0
          ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
          hrel.lazy_le_k hrel.tbl_eq ho_upd
        rw [hpost_rel.1]
        exact ih' _ _ _ _ hpost_rel.2 (Nat.le_succ _)

theorem evalDist_runHop2_phase1_recvWithPost_le {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
    (hph2 : Hop2Phase2Bound P Dh encPt decT encT ℓ qep s k rc_L)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (Q : Party) (c : Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsDeliverInTransitOrInjectPost (Pt := Pt) P qep s Q c st_R.1 post)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem_next : ℕ) (hq_k : ∀ r, SM.MakesAtMostQueries (k_oa r) rem_next)
    (d_ih ε : ℝ≥0∞)
    (hd_ih : d_ih + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hd_ph2 : ((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
      ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤ ε)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa r) sR []] {true} + d_ih) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybPrf k rc_L) (st_L.1.st Q) c rc).run st_L
        return post res.1 res.2)).run tbl
      runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa z.1.1) z.1.2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) (st_R.1.st Q) c rc).run st_R
        return post res.1 res.2)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
          1) u_chall) (k_oa z.1.1) z.1.2 z.2)] {true} + ε := by
  have hg_eq : st_L.1.st Q = st_R.1.st Q := by rw [hrel.st1_eq]
  rw [hg_eq]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
    stateT_lift_probComp_run, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
  rw [evalDist_bind_unif_swap ($ᵗ BitVec 256)]
  rcases party_eq_partyOfParity_or_succ k Q with rfl | rfl
  · set Q0 := partyOfParity k
    set g := st_R.1.st Q0
    have hp_R : g.party = Q0 := hrel.inv_R.party_eq Q0
    rcases hrel.idx_pk_R with hnone_R | hsome_R
    · refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q0 _ _ d_ih ε hd_ih
        fun rc hgood_rc => ?_
      have hidx_R : st_R.2.idx g.party = none := by rw [hp_R]; exact hnone_R
      have hidx_L : st_L.2.idx g.party = none := by rw [hrel.idx_eq]; exact hidx_R
      have hrun_L := hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrf k rc_L) g c rc st_L hidx_L
      have hrun_R := fun u_chall =>
        hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) g c rc st_R hidx_R
      refine evalDist_runHop2_phase1_of_pure_recv rc_L hrel Q0 c rc _ post (hpost.withGoodRc
          hgood_rc)
        hrun_L hrun_R ?_ k_oa d_ih ih'
      intro x hx
      simp only [Option.mem_def, Option.map_eq_some_iff] at hx
      rcases hx with ⟨_, _, rfl⟩
      exact Or.inl rfl
    · have hidx_R : st_R.2.idx g.party = some k := by rw [hp_R]; exact hsome_R
      have hidx_L : st_L.2.idx g.party = some k := by rw [hrel.idx_eq]; exact hidx_R
      by_cases hdh : ∃ msg T sc,
          SignalMessage.tryFrom P.codec c = .ok msg ∧
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
              true ∧
          decT msg.senderRatchetKey = some T ∧
          ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
          g.session.senderChain = some sc ∧
          Dh.dh (st_R.2.coins g.party) T ≠ 0
      · rcases hdh with ⟨msg, T, sc, htry, hfind, hdec_T, hT, hsc, hQ0_R⟩
        cases hmade_R : st_R.2.made.lookup (k, Dh.dh (st_R.2.coins g.party) T) with
        | none =>
          refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q0 _ _ d_ih ε
              hd_ih
            fun rc hgood_rc => ?_
          exact evalDist_runHop2_phase1_of_lazy_pk rc_L hrel c rc msg T sc
            hidx_R htry hfind hdec_T hT hsc hQ0_R hmade_R post (hpost.withGoodRc hgood_rc) k_oa d_ih
                ih'
        | some ckR =>
          exact evalDist_runHop2_phase1_of_create_pk hX hdec rc_L hph2 hrel c msg T sc ckR
            hidx_R htry hfind hdec_T hT hsc hQ0_R hmade_R post hpost k_oa rem_next hq_k d_ih ε hd_ih
                hd_ph2 ih'
      · refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q0 _ _ d_ih ε
          hd_ih
          fun rc hgood_rc => ?_
        have hdh_L : ¬ (∃ msg T sc,
            SignalMessage.tryFrom P.codec c = .ok msg ∧
            (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone
                = true ∧
            decT msg.senderRatchetKey = some T ∧
            ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
            g.session.senderChain = some sc ∧
            Dh.dh (st_L.2.coins g.party) T ≠ 0) := by
          rw [hrel.coins_eq]; exact hdh
        have hrun_L := hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrf k rc_L)
          k g c rc st_L hidx_L hdh_L
        have hrun_R := fun u_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
            k g c rc st_R hidx_R hdh
        exact evalDist_runHop2_phase1_of_pure_recv rc_L hrel Q0 c rc _ post (hpost.withGoodRc
            hgood_rc)
          hrun_L hrun_R (fun x hx => Or.inl (hop2NonDhOut_snd_none P g c rc x hx)) k_oa d_ih ih'
  · set Q1 := partyOfParity (k + 1)
    set g := st_R.1.st Q1
    have hp_R : g.party = Q1 := hrel.inv_R.party_eq Q1
    refine bind_evalDist_true_le_of_good_rc P Dh encPt decT encT hX hdec st_R Q1 _ _ d_ih ε hd_ih
      fun rc hgood_rc => ?_
    rcases hrel.idx_pk1_R with hnone_R | hsome_R
    · have hidx_R : st_R.2.idx g.party = none := by rw [hp_R]; exact hnone_R
      have hidx_L : st_L.2.idx g.party = none := by rw [hrel.idx_eq]; exact hidx_R
      have hrun_L := hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrf k rc_L) g c rc st_L hidx_L
      have hrun_R := fun u_chall =>
        hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) g c rc st_R hidx_R
      refine evalDist_runHop2_phase1_of_pure_recv rc_L hrel Q1 c rc _ post (hpost.withGoodRc
          hgood_rc)
        hrun_L hrun_R ?_ k_oa d_ih ih'
      intro x hx
      simp only [Option.mem_def, Option.map_eq_some_iff] at hx
      rcases hx with ⟨_, _, rfl⟩
      exact Or.inl rfl
    · have hidx_R : st_R.2.idx g.party = some (k + 1) := by rw [hp_R]; exact hsome_R
      have hidx_L : st_L.2.idx g.party = some (k + 1) := by rw [hrel.idx_eq]; exact hidx_R
      by_cases hdh : ∃ msg T sc,
          SignalMessage.tryFrom P.codec c = .ok msg ∧
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
              true ∧
          decT msg.senderRatchetKey = some T ∧
          ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
          g.session.senderChain = some sc ∧
          Dh.dh (st_R.2.coins g.party) T ≠ 0
      · rcases hdh with ⟨msg, T, sc, htry, hfind, hdec_T, hT, hsc, hQ0_R⟩
        exact evalDist_runHop2_phase1_of_lazy_pk1 rc_L hrel c rc msg T sc
          hidx_R htry hfind hdec_T hT hsc hQ0_R post (hpost.withGoodRc hgood_rc) k_oa d_ih ih'
      · have hdh_L : ¬ (∃ msg T sc,
            SignalMessage.tryFrom P.codec c = .ok msg ∧
            (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone
                = true ∧
            decT msg.senderRatchetKey = some T ∧
            ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
            g.session.senderChain = some sc ∧
            Dh.dh (st_L.2.coins g.party) T ≠ 0) := by
          rw [hrel.coins_eq]; exact hdh
        have hrun_L := hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrf k rc_L)
          (k + 1) g c rc st_L hidx_L hdh_L
        have hrun_R := fun u_chall =>
          hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
            (k + 1) g c rc st_R hidx_R hdh
        exact evalDist_runHop2_phase1_of_pure_recv rc_L hrel Q1 c rc _ post (hpost.withGoodRc
            hgood_rc)
          hrun_L hrun_R (fun x hx => Or.inl (hop2NonDhOut_snd_none P g c rc x hx)) k_oa d_ih ih'

theorem evalDist_runHop2_phase1_deliver_le {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
    (hph2 : Hop2Phase2Bound P Dh encPt decT encT ℓ qep s k rc_L)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (Q : Party) (c : Bytes)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem_next : ℕ) (hq_k : ∀ r, SM.MakesAtMostQueries (k_oa r) rem_next)
    (d_ih ε : ℝ≥0∞)
    (hd_ih : d_ih + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hd_ph2 : ((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
      ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤ ε)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa r) sR []] {true} + d_ih) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrf k rc_L) (Q, c)).run st_L)).run tbl
      runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa z.1.1) z.1.2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrg P encPt (k + 1) u_chall) (Q,
            c)).run st_R)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
          1) u_chall) (k_oa z.1.1) z.1.2 z.2)] {true} + ε := by
  have hwin_eq : st_L.1.win = st_R.1.win := by rw [hrel.st1_eq]
  have hin_eq : st_L.1.inTransit Q.other c = st_R.1.inTransit Q.other c := by rw [hrel.st1_eq]
  have hd_le : d_ih ≤ ε := le_self_add.trans hd_ih
  by_cases hwin : st_R.1.win = true
  · have hwin_L : st_L.1.win = true := hwin_eq.trans hwin
    unfold hop2Deliver
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin_L, hwin, ↓reduceIte,
      StateT.run_pure, simulateQ_pure]
    exact (ih' none st_L tbl st_R hrel (Nat.le_succ _)).trans (add_le_add le_rfl hd_le)
  · have hwin_R : st_R.1.win = false := Bool.eq_false_iff.mpr hwin
    have hwin_L : st_L.1.win = false := hwin_eq.trans hwin_R
    cases hin_R : st_R.1.inTransit Q.other c with
    | none =>
      have hin_L : st_L.1.inTransit Q.other c = none := hin_eq.trans hin_R
      unfold hop2Deliver
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin_L, hwin_R, Bool.false_eq_true,
        ↓reduceIte, hin_L, hin_R, StateT.run_pure, simulateQ_pure]
      exact (ih' none st_L tbl st_R hrel (Nat.le_succ _)).trans (add_le_add le_rfl hd_le)
    | some r =>
      have hin_L : st_L.1.inTransit Q.other c = some r := hin_eq.trans hin_R
      rw [hop2Deliver_run_eq_post P Dh encT decT s (hop2HybPrf k rc_L) Q c st_L r hwin_L hin_L]
      simp only [hop2Deliver_run_eq_post P Dh encT decT s _ Q c st_R r hwin_R hin_R]
      have hpost_eq : hop2DeliverPost (Pt := Pt) (ℓ := ℓ) P s Q c (st_L.1.st Q) r =
          hop2DeliverPost (Pt := Pt) (ℓ := ℓ) P s Q c (st_R.1.st Q) r := by
        rw [hrel.st1_eq]
      rw [hpost_eq]
      exact evalDist_runHop2_phase1_recvWithPost_le (qep := qep) hX hdec rc_L hph2 hrel Q c
        _ (Or.inl ⟨r, hin_R, rfl⟩) k_oa rem_next hq_k d_ih ε hd_ih hd_ph2 ih'

theorem evalDist_runHop2_phase1_inject_le {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
    (hph2 : Hop2Phase2Bound P Dh encPt decT encT ℓ qep s k rc_L)
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R)
    (Q : Party) (c : Bytes)
    (k_oa : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem_next : ℕ) (hq_k : ∀ r, SM.MakesAtMostQueries (k_oa r) rem_next)
    (d_ih ε : ℝ≥0∞)
    (hd_ih : d_ih + (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤ ε)
    (hd_ph2 : ((5 * rem_next : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
      ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤ ε)
    (ih' : ∀ r sL tL sR, Hop2Phase1Rel P decT encT k sL tL sR →
      tL.length ≤ tbl.length + 1 →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tL] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa r) sR []] {true} + d_ih) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrf k rc_L) (Q, c)).run st_L)).run tbl
      runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa z.1.1) z.1.2 z.2)] {true} ≤
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall => (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (Q,
            c)).run st_R)).run []
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
          1) u_chall) (k_oa z.1.1) z.1.2 z.2)] {true} + ε := by
  have hg_eq : (st_L.1.win || (st_L.1.inTransit Q.other c).isSome || !(st_L.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
      (st_R.1.win || (st_R.1.inTransit Q.other c).isSome || !(st_R.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := by
    rw [hrel.st1_eq]
  have hd_le : d_ih ≤ ε := le_self_add.trans hd_ih
  by_cases hg : (st_R.1.win || (st_R.1.inTransit Q.other c).isSome || !(st_R.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · have hg_L : (st_L.1.win || (st_L.1.inTransit Q.other c).isSome || !(st_L.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hg_eq.trans hg
    unfold hop2Inject
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hg_L, hg, ↓reduceIte,
      StateT.run_pure, simulateQ_pure]
    exact (ih' none st_L tbl st_R hrel (Nat.le_succ _)).trans (add_le_add le_rfl hd_le)
  · have hg_R : (st_R.1.win || (st_R.1.inTransit Q.other c).isSome || !(st_R.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
    have hg_L : (st_L.1.win || (st_L.1.inTransit Q.other c).isSome || !(st_L.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := hg_eq.trans hg_R
    rw [hop2Inject_run_eq_post P Dh encT decT qep s (hop2HybPrf k rc_L) Q c st_L hg_L]
    simp only [hop2Inject_run_eq_post P Dh encT decT qep s _ Q c st_R hg_R]
    have hpost_eq : hop2InjectPost (Pt := Pt) (ℓ := ℓ) P qep s Q c (st_L.1.st Q) =
        hop2InjectPost (Pt := Pt) (ℓ := ℓ) P qep s Q c (st_R.1.st Q) := by
      rw [hrel.st1_eq]
    rw [hpost_eq]
    exact evalDist_runHop2_phase1_recvWithPost_le hX hdec rc_L hph2 hrel Q c
      _ (Or.inr rfl) k_oa rem_next hq_k d_ih ε hd_ih hd_ph2 ih'

theorem evalDist_unif_bind_const {α : Type} [SampleableType α] (mx : ProbComp Bool) :
    𝒟[($ᵗ α : ProbComp α) >>= fun _ => mx] {true} = 𝒟[mx] {true} := by
  simp

theorem evalDist_runHop2_phase1_le {ℓ : ℕ} {P : Params Bytes PQC}
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (s : BitVec 256) (k : ℕ) (rc_L : Ratchet.RootKey × BitVec 256)
    (hph2 : Hop2Phase2Bound P Dh encPt decT encT ℓ qep s k rc_L)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem : ℕ) (hq : SM.MakesAtMostQueries oa rem)
    (st_L : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) (st_R : Hop2State Pt ℓ)
    (hrel : Hop2Phase1Rel P decT encT k st_L tbl st_R) :
    𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) oa st_L tbl] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u_chall =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) oa st_R []] {true} +
      ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem st_L tbl st_R with
  | pure a =>
    simp only [runHop2_pure, evalDist_unif_bind_const, hrel.bad_eq]
    exact le_self_add
  | query_bind t k_oa ih =>
    rw [SM.MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
    rw [runHop2_bind_query]
    simp only [runHop2_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2_unif]
      simp only [runHop2_unif]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      exact bind_evalDist_true_le_of_support _ _ _ _ fun a _ =>
        ih a rem (by simpa [SM.MakesAtMostQueries] using hq.2 a) st_L tbl st_R hrel
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      rw [runHop2_hop2Lift', hrel.st1_eq]
      simp only [runHop2_hop2Lift']
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
      have hinv' :=
          transmitR_support_hop2FullInv P hcodec hL Dh encPt decT encT hX hdec qep y_tr st_R
          hrel.inv_R r hr
      have hle : (((6 * (rem - 1) + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
        (r.2, st_L.2) tbl (r.2, st_R.2) (hrel.of_st1_step r.2 hinv')).trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      rw [runHop2_hop2Lift', hrel.st1_eq]
      simp only [runHop2_hop2Lift']
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
      have hinv' :=
          challR_support_hop2FullInv P hcodec hL Dh encPt decT encT hX hdec qep y_ch st_R hrel.inv_R
          r hr
      have hle : (((6 * (rem - 1) + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
        (r.2, st_L.2) tbl (r.2, st_R.2) (hrel.of_st1_step r.2 hinv')).trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      have hd_ih : ((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 6 * (rem - 1) +
            (tbl.length + 1) + 5 ≤ 6 * rem + tbl.length)) zero_le
      have hd_ph2 : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul, ← add_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 5 * (rem - 1) + (5 +
            tbl.length) ≤ 6 * rem + tbl.length)) zero_le
      refine evalDist_runHop2_phase1_deliver_le (qep := qep) hX hdec rc_L hph2 hrel Q c k_oa
        (rem - 1) (fun r => by simpa [SM.MakesAtMostQueries] using hq.2 r)
        (((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) hd_ih hd_ph2
        (fun r sL tL sR hrel' hlen => ?_)
      have hle : (((6 * (rem - 1) + tL.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r)
        sL tL sR hrel').trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      have hd_ih : ((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          (5 : ℝ≥0∞) * hop2CreateCollUnit Dh ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 6 * (rem - 1) +
            (tbl.length + 1) + 5 ≤ 6 * rem + tbl.length)) zero_le
      have hd_ph2 : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh +
          ((5 : ℝ≥0∞) * hop2CreateCollUnit Dh + (tbl.length : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
        rw [← add_mul, ← add_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 5 * (rem - 1) + (5 +
            tbl.length) ≤ 6 * rem + tbl.length)) zero_le
      refine evalDist_runHop2_phase1_inject_le hX hdec rc_L hph2 hrel Q c k_oa
        (rem - 1) (fun r => by simpa [SM.MakesAtMostQueries] using hq.2 r)
        (((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh)
        (((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) hd_ih hd_ph2
        (fun r sL tL sR hrel' hlen => ?_)
      have hle : (((6 * (rem - 1) + tL.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * (rem - 1) + (tbl.length + 1) : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r)
        sL tL sR hrel').trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [hop2Impl]
      rw [runHop2_hop2Lift', hrel.st1_eq]
      simp only [runHop2_hop2Lift']
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
      have hinv' := corrR_support_hop2FullInv P decT encT y_corr st_R hrel.inv_R r hr
      have hle : (((6 * (rem - 1) + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) ≤
          ((6 * rem + tbl.length : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      exact (ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
        (r.2, st_L.2) tbl (r.2, st_R.2) (hrel.of_st1_step r.2 hinv')).trans (add_le_add le_rfl hle)

end Phase1

end CryptoVerification.E2E.SpkHop1
