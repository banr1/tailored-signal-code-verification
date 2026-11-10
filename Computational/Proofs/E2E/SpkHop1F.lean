/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1E
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.GameHop.Fel
import Computational.Proofs.SignalWireRoundTrip

/-!
# Hop 2 Phase 2 Relation and Receiver-Chain Collision Bounds

Defines the Phase 2 coupling relation `Hop2Phase2Rel` and bounds receiver-chain key collisions
across window steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq

section Hop2Coupling

open CryptoGames.CKA CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF MACScheme

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

structure Hop2Phase2Rel {ℓ : ℕ} (P : Params Bytes PQC) (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (k : ℕ) (u_chall : BitVec 256) (Q_create : Pt)
    (st_L : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) (st_R : Hop2State Pt ℓ) : Prop where
  inv_R : Hop2GameInv P decT encT st_R
  st1_eq : st_L.1 = patchGamePartyIdx (k + 2) (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).1
    st_R.2.idx st_R.1
  bad_eq : st_L.2.bad = st_R.2.bad
  idx_pk_L : st_L.2.idx (partyOfParity k) = none
  idx_pk_R : st_R.2.idx (partyOfParity k) = none ∨ st_R.2.idx (partyOfParity k) = some (k + 2)
  idx_pk1_eq : st_L.2.idx (partyOfParity (k + 1)) = st_R.2.idx (partyOfParity (k + 1))
  idx_pk1_R : st_R.2.idx (partyOfParity (k + 1)) = none ∨
    st_R.2.idx (partyOfParity (k + 1)) = some (k + 1)
  made_create : st_R.2.made.lookup (k + 1, Q_create) =
    some (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2
  made_other : ∀ Q ≠ Q_create, st_R.2.made.lookup (k + 1, Q) = none
  tbl_create : tbl.lookup Q_create = some u_chall
  tbl_other : ∀ Q ≠ Q_create, tbl.lookup Q = st_R.2.lazy.lookup (k + 1, Q)
  coins_pk1 : st_R.2.idx (partyOfParity (k + 1)) = some (k + 1) →
    st_L.2.coins (partyOfParity (k + 1)) = st_R.2.coins (partyOfParity (k + 1))

omit [Zero Pt] [SampleableType Pt] in
theorem Hop2Phase2Rel.of_st1_step {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {k : ℕ} {u_chall : BitVec 256} {Q_create : Pt}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    (s_R' : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hinv' : Hop2GameInv P decT encT (s_R', st_R.2)) :
    Hop2Phase2Rel P decT encT k u_chall Q_create
      (patchGamePartyIdx (k + 2) (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).1
        st_R.2.idx s_R', st_L.2)
      tbl (s_R', st_R.2) :=
  ⟨hinv', rfl, hrel.bad_eq, hrel.idx_pk_L, hrel.idx_pk_R, hrel.idx_pk1_eq,
   hrel.idx_pk1_R, hrel.made_create, hrel.made_other, hrel.tbl_create,
   hrel.tbl_other, hrel.coins_pk1⟩

omit [Zero Pt] [SampleableType Pt] in
theorem hop2Phase2Rel_of_post_pk1 {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {qep : ℕ} {s : BitVec 256} {k : ℕ} {u_chall : BitVec 256} {Q_create : Pt}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    {c : Bytes} {post : Hop2Out Pt ℓ → Hop2State Pt ℓ →
        Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverOrInjectPost (Pt := Pt) P qep s (partyOfParity (k + 1)) c
      (st_R.1.st (partyOfParity (k + 1))) post)
    (o : Hop2Out Pt ℓ) (st2_L st2_R : Hop2State Pt ℓ) (tbl' : List (Pt × BitVec 256))
    (hinv' : Hop2GameInv P decT encT (post o st2_R).2)
    (hL : st2_L.1 = st_L.1 ∧ st2_L.2.bad = st_L.2.bad ∧ st2_L.2.idx = st_L.2.idx ∧
      st2_L.2.coins = st_L.2.coins ∧ st2_L.2.made = st_L.2.made)
    (hR : st2_R.1 = st_R.1 ∧ st2_R.2.bad = st_R.2.bad ∧ st2_R.2.idx = st_R.2.idx ∧
      st2_R.2.coins = st_R.2.coins ∧ st2_R.2.made = st_R.2.made)
    (htbl_create : tbl'.lookup Q_create = some u_chall)
    (htbl_other : ∀ Q' ≠ Q_create, tbl'.lookup Q' = st2_R.2.lazy.lookup (k + 1, Q'))
    (ho_upd : ∀ x ∈ o, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩) :
    (post o st2_L).1 = (post o st2_R).1 ∧
    Hop2Phase2Rel P decT encT k u_chall Q_create (post o st2_L).2 tbl' (post o st2_R).2 := by
  set Q := partyOfParity (k + 1)
  set rk_chall := (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).1
  have hQ_ne : partyOfParity k ≠ Q := (partyOfParity_succ_ne k).symm
  have hst1_2 : st2_L.1 = patchGamePartyIdx (k + 2) rk_chall st2_R.2.idx st2_R.1 := by
    rw [hL.1, hR.1, hR.2.2.1, hrel.st1_eq]
  have hbad_2 : st2_L.2.bad = st2_R.2.bad := by
    rw [hL.2.1, hR.2.1, hrel.bad_eq]
  have hidx_ne_k2 : ∀ x ∈ o, (hop2Commit st2_R.2 Q x.2).idx Q ≠ some (k + 2) := by
    intro x hx
    rcases ho_upd x hx with hnone | ⟨rc', hsome⟩
    · rw [hnone]; dsimp only [hop2Commit]; rw [hR.2.2.1]
      rcases hrel.idx_pk1_R with h0 | h1
      · simp [h0, Q]
      · simp [h1, Q]
    · rw [hsome]; simp [hop2Commit]
  have ho_map : o.map (·.1) = o.map (fun x =>
      (patchPartyIdx (k + 2) rk_chall ((hop2Commit st2_R.2 Q x.2).idx Q) x.1.1, x.1.2)) := by
    cases h_o : o with
    | none => rfl
    | some x =>
      dsimp only [Option.map]
      rw [patchPartyIdx_of_ne _ _ _ _ (hidx_ne_k2 x (by simp [h_o]))]
  have hother : ∀ x ∈ o, ∀ R ≠ Q, (hop2Commit st2_R.2 Q x.2).idx R = st2_R.2.idx R := by
    intro x _ R hR
    cases x.2 <;> simp [hop2Commit, Function.update_of_ne hR]
  have hstep := hpost.patchGamePartyIdx_step (k +
      2) rk_chall st2_L st2_R hst1_2 hbad_2 o o ho_map hother
  refine ⟨hstep.1, ⟨hinv', hstep.2.1, hstep.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, htbl_create, ?_, ?_⟩⟩
  · rcases hstep.2.2.2.2.2 with ⟨_, _, hL_eq, _⟩ | ⟨_, _, _, _, _, u_L, u_R, hoL, hoR, hcases⟩
    · rw [hL_eq, hL.2.2.1, hrel.idx_pk_L]
    · rcases hcases with ⟨hidxL, _⟩ | ⟨hidxL, _⟩
      · rw [hidxL, hL.2.2.1, hrel.idx_pk_L]
      · rw [hidxL]
        cases u_L <;> simp [hop2Commit, Function.update_of_ne hQ_ne, hL.2.2.1, hrel.idx_pk_L]
  · rcases hstep.2.2.2.2.2 with ⟨_, _, _, hR_eq⟩ | ⟨_, _, _, _, _, u_L, u_R, hoL, hoR, hcases⟩
    · rw [hR_eq, hR.2.2.1]; exact hrel.idx_pk_R
    · rcases hcases with ⟨_, _, _, hidxR, _⟩ | ⟨_, _, _, hidxR, _⟩
      · rw [hidxR, hR.2.2.1]; exact hrel.idx_pk_R
      · rw [hidxR]
        cases u_R <;> simp [hop2Commit, Function.update_of_ne hQ_ne, hR.2.2.1, hrel.idx_pk_R]
  · rcases hstep.2.2.2.2.2 with ⟨_, _, hL_eq, hR_eq⟩ | ⟨_, _, _, _, _, u_L, u_R, hoL, hoR, hcases⟩
    · rw [hL_eq, hR_eq, hL.2.2.1, hR.2.2.1, hrel.idx_pk1_eq]
    · have hu_eq : u_L = u_R := by
        rw [hoL] at hoR; injection hoR with hp; exact (Prod.mk.inj hp).2
      subst hu_eq
      rcases hcases with ⟨hidxL, _, _, hidxR, _⟩ | ⟨hidxL, _, _, hidxR, _⟩
      · rw [hidxL, hidxR, hL.2.2.1, hR.2.2.1, hrel.idx_pk1_eq]
      · rw [hidxL, hidxR]
        cases u_L <;> simp [hop2Commit, Function.update_self, Q, hL.2.2.1, hR.2.2.1,
            hrel.idx_pk1_eq]
  · rcases hstep.2.2.2.2.2 with ⟨_, _, _, hR_eq⟩ | ⟨_, st_R', t', i', m', u_L, u_R, hoL, hoR,
      hcases⟩
    · rw [hR_eq, hR.2.2.1]; exact hrel.idx_pk1_R
    · rcases hcases with ⟨_, _, _, hidxR, _⟩ | ⟨_, _, _, hidxR, _⟩
      · rw [hidxR, hR.2.2.1]; exact hrel.idx_pk1_R
      · rw [hidxR]
        rcases ho_upd ((st_R', t', i', m'), u_R) (by simp [hoR]) with hnone | ⟨rc', hsome⟩
        · dsimp only [] at hnone; subst hnone
          dsimp only [hop2Commit]; rw [hR.2.2.1]; exact hrel.idx_pk1_R
        · dsimp only [] at hsome; subst hsome
          simp [hop2Commit, Q]
  · have hmade_eq : (post o st2_R).2.2.made = st_R.2.made := by
      rcases hstep.2.2.2.2.2 with ⟨_, _, _, hR_eq⟩ | ⟨_, st_R', t', i', m', u_L, u_R, hoL, hoR,
          hcases⟩
      · rw [hR_eq, hR.2.2.2.2]
      · rcases hcases with ⟨_, _, _, _, _, hmadeR⟩ | ⟨_, _, _, _, _, hmadeR⟩
        · rw [hmadeR, hR.2.2.2.2]
        · rw [hmadeR]
          rcases ho_upd ((st_R', t', i', m'), u_R) (by simp [hoR]) with hnone | ⟨rc', hsome⟩
          · dsimp only [] at hnone; subst hnone; exact hR.2.2.2.2
          · dsimp only [] at hsome; subst hsome; exact hR.2.2.2.2
    rw [hmade_eq]; exact hrel.made_create
  · intro Q' hQ'
    have hmade_eq : (post o st2_R).2.2.made = st_R.2.made := by
      rcases hstep.2.2.2.2.2 with ⟨_, _, _, hR_eq⟩ | ⟨_, st_R', t', i', m', u_L, u_R, hoL, hoR,
          hcases⟩
      · rw [hR_eq, hR.2.2.2.2]
      · rcases hcases with ⟨_, _, _, _, _, hmadeR⟩ | ⟨_, _, _, _, _, hmadeR⟩
        · rw [hmadeR, hR.2.2.2.2]
        · rw [hmadeR]
          rcases ho_upd ((st_R', t', i', m'), u_R) (by simp [hoR]) with hnone | ⟨rc', hsome⟩
          · dsimp only [] at hnone; subst hnone; exact hR.2.2.2.2
          · dsimp only [] at hsome; subst hsome; exact hR.2.2.2.2
    rw [hmade_eq]; exact hrel.made_other Q' hQ'
  · intro Q' hQ'
    rw [hstep.2.2.2.2.1]
    exact htbl_other Q' hQ'
  · intro hidx_post
    rcases hstep.2.2.2.2.2 with ⟨_, _, hL_eq, hR_eq⟩ | ⟨_, st_R', t', i', m', u_L, u_R, hoL, hoR,
        hcases⟩
    · rw [hR_eq, hR.2.2.1] at hidx_post
      rw [hL_eq, hR_eq, hL.2.2.2.1, hR.2.2.2.1]
      exact hrel.coins_pk1 hidx_post
    · have hu_eq : u_L = u_R := by
        rw [hoL] at hoR; injection hoR with hp; exact (Prod.mk.inj hp).2
      subst hu_eq
      rcases hcases with ⟨_, hcoinsL, _, hidxR, hcoinsR, _⟩ | ⟨_, hcoinsL, _, hidxR, hcoinsR, _⟩
      · rw [hidxR, hR.2.2.1] at hidx_post
        rw [hcoinsL, hcoinsR, hL.2.2.2.1, hR.2.2.2.1]
        exact hrel.coins_pk1 hidx_post
      · rcases ho_upd ((st_R', t', i', m'), u_L) (by simp [hoR]) with hnone | ⟨rc', hsome⟩
        · dsimp only [] at hnone; subst hnone
          rw [hidxR] at hidx_post
          dsimp only [hop2Commit] at hidx_post
          rw [hR.2.2.1] at hidx_post
          rw [hcoinsL, hcoinsR]
          dsimp only [hop2Commit]
          rw [hL.2.2.2.1, hR.2.2.2.1]
          exact hrel.coins_pk1 hidx_post
        · dsimp only [] at hsome; subst hsome
          rw [hidxR] at hidx_post
          simp [hop2Commit, Q] at hidx_post


theorem hop2Phase2Rel_of_post_pk {ℓ : ℕ} {P : Params Bytes PQC} (hcodec : P.codec =
    protoSignalCodec)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz : ∀ x, Dh.dh x 0 = 0)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} {rc_L : Ratchet.RootKey × BitVec 256}
    {u_chall : BitVec 256} {Q_create : Pt}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    {c : Bytes} (rc : BitVec 256)
    (horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true)
    {post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ}
    (hpost : IsDeliverOrInjectPost (Pt := Pt) P qep s (partyOfParity k) c
      (st_R.1.st (partyOfParity k)) post) :
    ∃ o_L o_R : Hop2Out Pt ℓ,
      (hop2Recv (ℓ :=
          ℓ) P Dh encT decT (hop2HybPrf k rc_L) (st_L.1.st (partyOfParity k)) c rc).run st_L =
        pure (o_L, st_L) ∧
      (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
        (st_R.1.st (partyOfParity k)) c rc).run st_R =
        pure (o_R, st_R) ∧
      (post o_L st_L).1 = (post o_R st_R).1 ∧
      Hop2Phase2Rel P decT encT k u_chall Q_create (post o_L st_L).2 tbl (post o_R st_R).2 := by
  set Q := partyOfParity k
  set rk_chall := (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).1
  have hQ1_ne : partyOfParity (k + 1) ≠ Q := partyOfParity_succ_ne k
  have hp_R : (st_R.1.st Q).party = Q := hrel.inv_R.party_eq Q
  have hg_L_eq : st_L.1.st Q = patchPartyIdx (k + 2) rk_chall (st_R.2.idx Q) (st_R.1.st Q) := by
    rw [hrel.st1_eq]; rfl
  have hp_L : (st_L.1.st Q).party = Q := by
    rw [hg_L_eq, patchPartyIdx_party, hp_R]
  have hidx_L : st_L.2.idx (st_L.1.st Q).party = none := by
    rw [hp_L]; exact hrel.idx_pk_L
  have hrun_L := hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrf k rc_L)
    (st_L.1.st Q) c rc st_L hidx_L
  have hidx_cases_R : st_R.2.idx (st_R.1.st Q).party = none ∨
      (st_R.2.idx (st_R.1.st Q).party = some (k + 2) ∧
        ∃ ckS0, (st_R.1.st Q).session.senderChain =
          some ⟨KeyPair.generate P.C (st_R.2.coins (st_R.1.st Q).party), ckS0⟩) := by
    rw [hp_R]
    rcases hrel.idx_pk_R with hnone | hsome
    · exact Or.inl hnone
    · exact Or.inr ⟨hsome, hrel.inv_R.coins_sc Q (by simp [hsome, Q])⟩
  obtain ⟨o_R, hrun_R, ho_map_R, hprops_R⟩ :=
    hop2Recv_patchPartyIdx_eq (ℓ := ℓ) P hcodec Dh encPt encT decT hX hz
      (k + 1) (k + 2) (by omega) rk_chall (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2
      (st_R.1.st Q) c rc st_R horc hidx_cases_R
  set o_L : Hop2Out Pt ℓ := ((sessionSchemeU P ℓ).receive (st_L.1.st Q) c rc).map (fun r => (r,
      none))
  have ho_map : o_L.map (·.1) = o_R.map (fun x =>
      (patchPartyIdx (k + 2) rk_chall ((hop2Commit st_R.2 Q x.2).idx Q) x.1.1, x.1.2)) := by
    have hmap_L : o_L.map (·.1) = (sessionSchemeU P ℓ).receive (st_L.1.st Q) c rc := by
      dsimp only [o_L]; rw [Option.map_map]; exact Option.map_id'
    have ho_map_R' := ho_map_R
    rw [hp_R] at ho_map_R'
    rw [hmap_L, hg_L_eq, ← ho_map_R']
  have hother : ∀ x ∈ o_R, ∀ R ≠ Q, (hop2Commit st_R.2 Q x.2).idx R = st_R.2.idx R := by
    intro x _ R hR
    cases x.2 <;> simp [hop2Commit, Function.update_of_ne hR]
  have hsupp_R : ((o_R, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
          1) u_chall) (st_R.1.st Q) c rc).run st_R)).run []) := by
    have hrun_R' : (hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
        1) u_chall) (st_R.1.st Q) c rc).run st_R =
        pure (o_R, st_R) := hrun_R
    rw [hrun_R']
    simp [simulateQ_pure, StateT.run_pure]
  have hinv' : Hop2GameInv P decT encT (post o_R st_R).2 :=
    hpost.preserves_hop2GameInv hrel.inv_R ((o_R, st_R), []) hsupp_R
  have hstep := hpost.patchGamePartyIdx_step (k +
      2) rk_chall st_L st_R hrel.st1_eq hrel.bad_eq o_L o_R ho_map hother
  refine ⟨o_L, o_R, hrun_L, hrun_R, hstep.1,
    ⟨hinv', hstep.2.1, hstep.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, hrel.tbl_create, ?_, ?_⟩⟩
  · rcases hstep.2.2.2.2.2 with ⟨_, _, hL_eq, _⟩ | ⟨st_L', _, t', i', m', u_L, _, hoL, _, hcases⟩
    · rw [hL_eq, hrel.idx_pk_L]
    · have hu_L : u_L = none := by
        dsimp only [o_L] at hoL
        simp only [Option.map_eq_some_iff] at hoL
        rcases hoL with ⟨_, _, hp⟩
        exact (Prod.mk.inj hp).2.symm
      subst hu_L
      rcases hcases with ⟨hidxL, _⟩ | ⟨hidxL, _⟩
      · rw [hidxL, hrel.idx_pk_L]
      · rw [hidxL]; exact hrel.idx_pk_L
  · rcases hstep.2.2.2.2.2 with ⟨_, _, _, hR_eq⟩ | ⟨_, st_R', t', i', m', _, u_R, _, hoR, hcases⟩
    · rw [hR_eq]; exact hrel.idx_pk_R
    · rcases hcases with ⟨_, _, _, hidxR, _⟩ | ⟨_, _, _, hidxR, _⟩
      · rw [hidxR]; exact hrel.idx_pk_R
      · rw [hidxR]
        have hpR := (hprops_R ((st_R', t', i', m'), u_R) (by simp [hoR])).1
        rw [hp_R] at hpR
        rcases hpR with hnone | ⟨hsome, _⟩
        · exact Or.inl hnone
        · exact Or.inr hsome
  · rcases hstep.2.2.2.2.2 with ⟨_, _, hL_eq, hR_eq⟩ | ⟨st_L', st_R', t', i', m', u_L, u_R, hoL,
      hoR, hcases⟩
    · rw [hL_eq, hR_eq, hrel.idx_pk1_eq]
    · have hu_L : u_L = none := by
        dsimp only [o_L] at hoL
        simp only [Option.map_eq_some_iff] at hoL
        rcases hoL with ⟨_, _, hp⟩
        exact (Prod.mk.inj hp).2.symm
      subst hu_L
      rcases hcases with ⟨hidxL, _, _, hidxR, _⟩ | ⟨hidxL, _, _, hidxR, _⟩
      · rw [hidxL, hidxR, hrel.idx_pk1_eq]
      · rw [hidxL, hidxR]
        cases u_R <;> simp [hop2Commit, Function.update_of_ne hQ1_ne, hrel.idx_pk1_eq]
  · rcases hstep.2.2.2.2.2 with ⟨_, _, _, hR_eq⟩ | ⟨_, st_R', t', i', m', _, u_R, _, hoR, hcases⟩
    · rw [hR_eq]; exact hrel.idx_pk1_R
    · rcases hcases with ⟨_, _, _, hidxR, _⟩ | ⟨_, _, _, hidxR, _⟩
      · rw [hidxR]; exact hrel.idx_pk1_R
      · rw [hidxR]
        cases u_R <;> simp [hop2Commit, Function.update_of_ne hQ1_ne, hrel.idx_pk1_R]
  · have hmade_eq : (post o_R st_R).2.2.made = st_R.2.made := by
      rcases hstep.2.2.2.2.2 with ⟨_, _, _, hR_eq⟩ | ⟨_, st_R', t', i', m', _, u_R, _, hoR, hcases⟩
      · rw [hR_eq]
      · rcases hcases with ⟨_, _, _, _, _, hmadeR⟩ | ⟨_, _, _, _, _, hmadeR⟩
        · exact hmadeR
        · rw [hmadeR]
          have hm := (hprops_R ((st_R', t', i', m'), u_R) (by simp [hoR])).2.2.1
          rw [hp_R] at hm; exact hm
    rw [hmade_eq]; exact hrel.made_create
  · intro Q' hQ'
    have hmade_eq : (post o_R st_R).2.2.made = st_R.2.made := by
      rcases hstep.2.2.2.2.2 with ⟨_, _, _, hR_eq⟩ | ⟨_, st_R', t', i', m', _, u_R, _, hoR, hcases⟩
      · rw [hR_eq]
      · rcases hcases with ⟨_, _, _, _, _, hmadeR⟩ | ⟨_, _, _, _, _, hmadeR⟩
        · exact hmadeR
        · rw [hmadeR]
          have hm := (hprops_R ((st_R', t', i', m'), u_R) (by simp [hoR])).2.2.1
          rw [hp_R] at hm; exact hm
    rw [hmade_eq]; exact hrel.made_other Q' hQ'
  · intro Q' hQ'
    rw [hstep.2.2.2.2.1]
    exact hrel.tbl_other Q' hQ'
  · intro hidx_post
    rcases hstep.2.2.2.2.2 with ⟨_, _, hL_eq, hR_eq⟩ | ⟨st_L', st_R', t', i', m', u_L, u_R, hoL,
        hoR, hcases⟩
    · rw [hR_eq] at hidx_post
      rw [hL_eq, hR_eq]
      exact hrel.coins_pk1 hidx_post
    · have hu_L : u_L = none := by
        dsimp only [o_L] at hoL
        simp only [Option.map_eq_some_iff] at hoL
        rcases hoL with ⟨_, _, hp⟩
        exact (Prod.mk.inj hp).2.symm
      subst hu_L
      rcases hcases with ⟨_, hcoinsL, _, hidxR, hcoinsR, _⟩ | ⟨_, hcoinsL, _, hidxR, hcoinsR, _⟩
      · rw [hidxR] at hidx_post
        rw [hcoinsL, hcoinsR]
        exact hrel.coins_pk1 hidx_post
      · have hidx_eq : (hop2Commit st_R.2 Q u_R).idx (partyOfParity (k + 1)) =
            st_R.2.idx (partyOfParity (k + 1)) := by
          cases u_R <;> simp [hop2Commit, Function.update_of_ne hQ1_ne]
        have hcoins_eq : (hop2Commit st_R.2 Q u_R).coins (partyOfParity (k + 1)) =
            st_R.2.coins (partyOfParity (k + 1)) := by
          cases u_R <;> simp [hop2Commit, Function.update_of_ne hQ1_ne]
        rw [hidxR, hidx_eq] at hidx_post
        rw [hcoinsL, hcoinsR, hcoins_eq]
        exact hrel.coins_pk1 hidx_post

theorem bind_evalDist_true_eq {α : Type} (mx : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ a, 𝒟[f a] {true} = 𝒟[g a] {true}) :
    𝒟[mx >>= f] {true} = 𝒟[mx >>= g] {true} := by
  let : MeasurableSpace α := ⊤
  have h1 : ∀ (k : α → ProbComp Bool),
      𝒟[mx >>= k] {true} = ∫⁻ c, 𝒟[k c] {true} ∂𝒟[mx] := fun k => by
    rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable]
  rw [h1 f, h1 g]
  exact congrArg (fun k => ∫⁻ c, k c ∂𝒟[mx]) (funext h)

theorem party_eq_partyOfParity_or_succ (k : ℕ) (Q : Party) :
    Q = partyOfParity k ∨ Q = partyOfParity (k + 1) := by
  rw [partyOfParity_succ]
  cases partyOfParity k <;> cases Q <;> decide

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_lazyImpl_map_evalQuery {α : Type} (f : BitVec 256 → α) (I : Pt)
    (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt)) (f <$> evalQuery (Input := Pt) (Tag :=
        BitVec 256) I)).run tbl =
      match tbl.lookup I with
      | some u => pure (f u, tbl)
      | none => (fun u => (f u, (I, u) :: tbl)) <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
  simp only [map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind,
    simulateQ_lazyImpl_evalQuery, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    lazyStep, StateT.run_get, pure_bind]
  cases tbl.lookup I <;>
    simp [StateT.run_bind, StateT.run_set, StateT.run_pure,
      map_eq_bind_pure_comp, bind_assoc, pure_bind]

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_lazyImpl_map_hop2Lazy {ℓ : ℕ} {α : Type} (f : BitVec 256 × Hop2State Pt ℓ → α)
    (t : ℕ) (I : Pt) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt)) (f <$> (hop2Lazy t I).run st)).run tbl =
      match st.2.lazy.lookup (t, I) with
      | some u => pure (f (u, st), tbl)
      | none => (fun u => (f (u, (st.1, { st.2 with lazy := ((t, I), u) :: st.2.lazy })), tbl)) <$>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
  simp only [map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure,
    hop2Lazy, StateT.run_get, pure_bind]
  cases st.2.lazy.lookup (t, I) <;>
    simp [StateT.run_bind, StateT.run_set, StateT.run_pure,
      simulateQ_bind, simulateQ_lazyImpl_hop2Unif, simulateQ_pure,
      map_eq_bind_pure_comp, bind_assoc, pure_bind]

/-! ## Receiver-chain collision bounds -/

theorem bind_evalDist_true_le_of_support_window {α : Type} (mx : ProbComp α) (f g : α →
    ProbComp Bool)
    (h : ∀ a ∈ support mx, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} :=
  Computational.Proofs.GameHop.Advantage.evalDist_bind_mono_prob_of_support mx f g
    (measurableSet_singleton true) h

theorem bind_evalDist_true_le_add_of_support_window {α : Type} (mx : ProbComp α) (f g : α →
    ProbComp Bool)
    (d : ℝ≥0∞)
    (h : ∀ a ∈ support mx, 𝒟[f a] {true} ≤ 𝒟[g a] {true} + d) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} + d :=
  Computational.Proofs.GameHop.Advantage.evalDist_bind_le_add_prob_of_support mx f g
    (measurableSet_singleton true) h

theorem bind_apply_le_add_of_evalDist_le_on_good_window {α : Type} (mx : ProbComp α)
    (f g : α → ProbComp Bool) (bad : α → Bool) (d : ℝ≥0∞)
    (hle : ∀ c, bad c = false → 𝒟[f c] {true} ≤ 𝒟[g c] {true} + d) :
    𝒟[mx >>= f] {true} ≤
      𝒟[mx >>= g] {true} + d + 𝒟[mx >>= fun c => pure (bad c)] {true} := by
  let : MeasurableSpace α := ⊤
  have h1 : ∀ (k : α → ProbComp Bool),
      𝒟[mx >>= k] {true} = ∫⁻ c, 𝒟[k c] {true} ∂𝒟[mx] := fun k => by
    rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable]
  rw [h1 f, h1 g, h1 (fun c => pure (bad c))]
  have hd : d = ∫⁻ _c, d ∂𝒟[mx] := by
    rw [MeasureTheory.lintegral_const, evalDist_apply_univ_eq_one, mul_one]
  rw [hd, ← MeasureTheory.lintegral_add_right _ Measurable.of_discrete,
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete.add_const d)]
  refine MeasureTheory.lintegral_mono fun c => ?_
  rcases hbc : bad c
  · calc 𝒟[f c] {true} ≤ 𝒟[g c] {true} + d := hle c hbc
      _ ≤ (𝒟[g c] {true} + d) + 𝒟[(pure false : ProbComp Bool)] {true} := le_self_add
  · have htrue : 𝒟[(pure true : ProbComp Bool)] {true} = 1 := by simp
    rw [htrue]
    calc 𝒟[f c] {true} ≤ 𝒟[f c] Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := evalDist_apply_univ_eq_one _
      _ ≤ (𝒟[g c] {true} + d) + 1 := le_add_self

def hasKeyInChainsBool (k : PublicKey) (cs : List ReceiverChain) : Bool :=
  cs.any (·.senderRatchetKey == k)

theorem noKeyInChains_of_hasKeyInChainsBool_false (k : PublicKey) (cs : List ReceiverChain)
    (h : hasKeyInChainsBool k cs = false) :
    NoKeyInChains k cs := by
  intro c hc hck
  unfold hasKeyInChainsBool at h
  rw [List.any_eq_false] at h
  have := h c hc
  rw [hck, beq_self_eq_true] at this
  exact this rfl

theorem generate_publicKey_eq_prob_le_hop2GuessUnit (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (pk : PublicKey) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
      fun rc => pure ((KeyPair.generate P.C rc).publicKey == pk)] {true} ≤
      hop2GuessUnit Dh := by
  cases hdec_pk : decT pk with
  | none =>
    have hfalse : ∀ rc : BitVec 256, ((KeyPair.generate P.C rc).publicKey == pk) = false := by
      intro rc
      rw [beq_eq_false_iff_ne]
      intro heq
      rw [CryptoGames.LibsignalSM.Proofs.Refinement.keyPair_generate_publicKey hX rc] at heq
      have h1 := congrArg decT heq
      rw [hdec (Dh.dh rc Dh.base), hdec_pk] at h1
      cases h1
    simp [hfalse]
  | some T =>
    have hle : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
        fun rc => pure ((KeyPair.generate P.C rc).publicKey == pk)] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
          fun rc => pure (decide (Dh.dh rc Dh.base = T))] {true} := by
      refine bind_evalDist_true_le_of_support_window _ _ _ fun rc _ => ?_
      by_cases hbeq : ((KeyPair.generate P.C rc).publicKey == pk) = true
      · have heq : (KeyPair.generate P.C rc).publicKey = pk := eq_of_beq hbeq
        rw [CryptoGames.LibsignalSM.Proofs.Refinement.keyPair_generate_publicKey hX rc] at heq
        have h1 := congrArg decT heq
        rw [hdec (Dh.dh rc Dh.base), hdec_pk, Option.some.injEq] at h1
        simp [hbeq, h1]
      · have hbf : ((KeyPair.generate P.C rc).publicKey == pk) = false :=
          Bool.eq_false_iff.mpr hbeq
        simp [hbf]
    exact hle.trans (dh_base_eq_prob_le_hop2GuessUnit Dh T)

theorem hasKeyInChainsBool_prob_le_hop2GuessUnit (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (cs : List ReceiverChain) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
      fun rc => pure (hasKeyInChainsBool (KeyPair.generate P.C rc).publicKey cs)] {true} ≤
      (cs.length : ℝ≥0∞) * hop2GuessUnit Dh := by
  have hev : ∀ (f : BitVec 256 → Bool),
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (f rc)] {true} =
        Pr{let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))}[f rc = true] := fun f => by
    rw [prEvent_eq_evalDist_of_discrete]
    have hmap : (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (f rc)) =
        f <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
      simp [map_eq_bind_pure_comp]
    rw [hmap, evalDist_map_of_discrete,
      MeasureTheory.Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
    rfl
  unfold hasKeyInChainsBool
  rw [hev]
  refine (Computational.Proofs.GameHop.Fel.prEvent_any_list_le_sum
    ($ᵗ BitVec 256 : ProbComp (BitVec 256)) cs
    (fun rc c => c.senderRatchetKey == (KeyPair.generate P.C rc).publicKey)).trans ?_
  refine (List.sum_le_length_nsmul _ (hop2GuessUnit Dh) fun x hx => ?_).trans ?_
  · rcases List.mem_map.mp hx with ⟨c, _, rfl⟩
    rw [← hev]
    simp_rw [BEq.comm (a := c.senderRatchetKey)]
    exact generate_publicKey_eq_prob_le_hop2GuessUnit P Dh encPt decT encT hX hdec c.senderRatchetKey
  · simp only [List.length_map, nsmul_eq_mul, le_rfl]

theorem send_tryFrom_senderRatchetKey {ℓ : ℕ} (P : Params Bytes PQC)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (g : GhostState Bytes)
    (hver : g.session.sessionVersion = BitVec.ofNat 32 currentVersion.toNat)
    (m : CBC.Plain ℓ) (r : PQC) (msg : SignalMessage)
    (htry : SignalMessage.tryFrom P.codec ((sessionSchemeU P ℓ).send g m r).2 = .ok msg) :
    ∃ sc, g.session.senderChain = some sc ∧ msg.senderRatchetKey = sc.ratchetKey.publicKey := by
  have hrt : CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp P ℓ :=
      ⟨hcodec ▸ signalRoundTripShort_proto, hL, hcodec ▸ signalEncodeFits32_proto⟩
  obtain ⟨hlen_try, hparse_try⟩ := SpkHop2.parse_tryFrom_senderRatchetKey_eq P.codec
    ((sessionSchemeU P ℓ).send g m r).2 msg htry
  unfold sessionSchemeU Params.send SessionState.messageEncrypt at hlen_try hparse_try
  dsimp only [] at hlen_try hparse_try
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState g.session with ⟨r_from, taken⟩
  rw [hfrom] at hlen_try hparse_try
  cases r_from with
  | error _ => simp at hlen_try
  | ok session =>
    dsimp only [] at hlen_try hparse_try
    rcases henc : Mut.exec (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr m.toList
      (g.session.encryptAddresses (P.sendAddrs g.party)) r) session with ⟨r_enc, session'⟩
    rw [henc] at hlen_try hparse_try
    cases r_enc with
    | error _ => simp at hlen_try
    | ok msg_enc =>
      dsimp only [] at hparse_try
      obtain ⟨sc, rem, hsc_some, _, rfl, _, _⟩ :=
        SpkHop2.Mut_exec_outgoingFromSessionState g.session session taken hfrom
      obtain ⟨newPqr, pqrKey, pqrMsg, hspqr, hmsg⟩ :=
        SpkHop2.Mut_exec_outgoingEncrypt P.C P.codec P.spqr m.toList
          (g.session.encryptAddresses (P.sendAddrs g.party)) r _ msg_enc session' henc
      have hv : BitVec.ofNat 8 g.session.version.toNat = currentVersion :=
        SpkHop2.version_of_sessionVersion_current hver
      dsimp only [] at hmsg
      rw [hv] at hmsg
      subst hmsg
      set messageKeys := (sc.chainKey.messageKeys P.C.F).generateKeys P.C.F pqrKey
      set ctext := aesCbcEncrypt P.C.E messageKeys.cipherKey messageKeys.iv m.toList
      set addrs := g.session.encryptAddresses (P.sendAddrs g.party)
      set hdr : SignalHeader := ⟨currentVersion, sc.ratchetKey.publicKey,
        sc.chainKey.index, g.session.previousCounter, pqrMsg, addrs⟩
      set ser := (signalWireCodec P.codec).encode hdr ctext
      set mac := computeMac P.C.F g.session.localIdentity rem messageKeys.macKey ser
      have hser_eq : (SignalMessage.new P.C.F P.codec currentVersion messageKeys.macKey addrs
          sc.ratchetKey.publicKey sc.chainKey.index g.session.previousCounter ctext
          g.session.localIdentity rem pqrMsg).serialized = ser ++ mac := rfl
      have hmac_len : mac.length = 8 :=
        CryptoGames.LibsignalSM.Proofs.Refinement.length_computeMac _ _ _ _ _
      have htake : (ser ++ mac).take ((ser ++ mac).length - 8) = ser := by
        rw [List.length_append, hmac_len, Nat.add_sub_cancel,
          List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      have hparse : (signalWireCodec P.codec).parse ser = some (hdr, ctext) :=
        CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp.parse hrt hdr ctext rfl (Or.inr ⟨_, _, _, _,
            hspqr⟩)
          (CryptoGames.LibsignalSM.Proofs.RoundTrip.sentAddrs_send P g.session.pendingPreKey
              g.party)
          (by rw [CryptoGames.LibsignalSM.Proofs.RoundTrip.length_aesCbcEncrypt, m.toList_length])
      rw [hser_eq, htake, hparse] at hparse_try
      simp only [Option.map_some, Option.some.injEq] at hparse_try
      exact ⟨sc, hsc_some, hparse_try.symm⟩

theorem tryDecryptFromRecord_none_props (P : Params Bytes PQC)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (m : Bytes) (s_out : SessionState Bytes)
    (hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none)
    (hok : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc g.session = (.ok m, s_out)) :
    (∃ ckR, s_out.receiverChains.length =
      (RatchetState.evictReceiverChains
        (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ckR, []⟩])).length) ∧
    (∀ pk, NoKeyInChains pk g.session.receiverChains → msg.senderRatchetKey ≠ pk →
      NoKeyInChains pk s_out.receiverChains) ∧
    (∃ sck, s_out.senderChain = some ⟨KeyPair.generate P.C rc, sck⟩) := by
  rw [tryDecryptFromRecord_eq] at hok
  split_ifs at hok with hv
  · cases hok
  · cases hrem : g.session.remoteIdentity with
    | none => rw [hrem] at hok; cases hok
    | some rem =>
      rw [hrem] at hok
      dsimp only [] at hok
      set r_in : RatchetState :=
        ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
         g.session.previousCounter, maxForwardJumps⟩
      rcases hrat : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        r_in with ⟨r_rat, r'⟩
      rw [hrat] at hok
      cases r_rat with
      | error _ => cases hok
      | ok gen =>
        dsimp only [] at hok
        have hpost := ((postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper g.session rem gen r' g.session.receiverChains r'.receiverChains).2 m s_out
              hok).2
        have hsc_out : s_out.senderChain = r'.senderChain := by
          dsimp only [postRatchetDecrypt] at hok
          split_ifs at hok with hpan
          · cases hok
          cases hspqr : P.spqr.recv g.session.pqRatchetState msg.pqRatchet with
          | error b => rw [hspqr] at hok; cases b <;> cases hok
          | ok ps =>
            rw [hspqr] at hok
            dsimp only [] at hok
            split_ifs at hok with hmac
            · cases hok
            · cases haes : aesCbcDecrypt P.C.D ((gen.generateKeys P.C.F ps.2).cipherKey)
                  ((gen.generateKeys P.C.F ps.2).iv) msg.ciphertext with
              | none => rw [haes] at hok; cases hok
              | some ptext =>
                rw [haes] at hok
                injection hok with _ hs_out
                subst hs_out
                rfl
        unfold ratchetDecryptStep at hrat
        rw [Mut_exec_bind] at hrat
        rcases hens : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
          r_in with ⟨r_ens, s_ens⟩
        rw [hens] at hrat
        cases r_ens with
        | error _ => cases hrat
        | ok ck =>
          dsimp only [] at hrat
          unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey at hens
          simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_liftE] at hens
          change _ at hnone
          rw [show r_in.findReceiverChainIndex msg.senderRatchetKey = none from hnone] at hens
          dsimp only [] at hens
          unfold RatchetState.dhRatchetStep at hens
          simp only [Mut_exec_bind, Mut_exec_get] at hens
          cases hsc : r_in.senderChain with
          | none => rw [hsc] at hens; simp [Mut_exec_throw] at hens
          | some sc0 =>
            rw [hsc] at hens
            simp only [Mut_exec_bind, Mut_exec_takeRootKey, Mut_exec_liftE,
              Mut_exec_modify, Mut_exec_pure] at hens
            cases hrc1 :
                rootCreateChain P.C r_in.rootKey msg.senderRatchetKey sc0.ratchetKey.privateKey with
            | error _ => rw [hrc1] at hens; simp [] at hens
            | ok p1 =>
              rw [hrc1] at hens
              dsimp only [] at hens
              cases hrc2 :
                  rootCreateChain P.C p1.1 msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey
                  with
              | error _ => rw [hrc2] at hens; simp [] at hens
              | ok p2 =>
                rw [hrc2] at hens
                dsimp only [] at hens
                injection hens with hck hs_ens
                injection hck with hck'
                subst hck'
                have hs_ens_rc : s_ens.receiverChains = RatchetState.evictReceiverChains
                    (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some p1.2, []⟩]) := by
                  rw [← hs_ens]
                have hs_ens_sc : s_ens.senderChain =
                    some ⟨KeyPair.generate P.C rc, p2.2⟩ := by
                  rw [← hs_ens]
                have hcmk_len := consumeMessageKey_length P.C.F msg.senderRatchetKey p1.2
                  msg.counter .whisper s_ens
                have hcmk_sc := SpkHop2.consumeMessageKey_senderChain P.C.F msg.senderRatchetKey
                  p1.2 msg.counter .whisper s_ens
                rw [hrat, hs_ens_rc] at hcmk_len
                rw [hrat, hs_ens_sc] at hcmk_sc
                refine ⟨⟨p1.2, (congrArg List.length hpost.2.2).trans hcmk_len⟩, ?_,
                  ⟨p2.2, hsc_out.trans hcmk_sc⟩⟩
                intro pk hno hne
                rw [hpost.2.2]
                have hno_stepped : NoKeyInChains pk s_ens.receiverChains := by
                  rw [hs_ens_rc]
                  exact noKeyInChains_evict_append pk msg.senderRatchetKey g.session.receiverChains
                    (some p1.2) [] hno hne
                have hcmk_no := consumeMessageKey_noKeyInChains P.C.F pk msg.senderRatchetKey p1.2
                  msg.counter .whisper s_ens hno_stepped
                rw [hrat] at hcmk_no
                exact hcmk_no

theorem sessionSchemeU_receive_window_props {ℓ : ℕ} (P : Params Bytes PQC)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (hrec : (sessionSchemeU P ℓ).receive g c rc = some (st', t', i', m')) :
    ∃ msg, SignalMessage.tryFrom P.codec c = .ok msg ∧
      ((∃ idx, g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
          some idx ∧
        st'.epoch = g.epoch ∧
        st'.chainEpochs =
            g.chainEpochs.drop (g.chainEpochs.length - st'.session.receiverChains.length) ∧
        st'.session.senderChain = g.session.senderChain ∧
        st'.session.receiverChains.length = g.session.receiverChains.length ∧
        (∀ pk, NoKeyInChains pk g.session.receiverChains →
            NoKeyInChains pk st'.session.receiverChains)) ∨
       (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none ∧
        st'.epoch = g.epoch + 1 ∧
        st'.chainEpochs = (g.chainEpochs ++ [g.epoch + 1]).drop
          ((g.chainEpochs.length + 1) - st'.session.receiverChains.length) ∧
        (∃ ckR, st'.session.receiverChains.length =
          (RatchetState.evictReceiverChains
            (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ckR, []⟩])).length) ∧
        (∀ pk, NoKeyInChains pk g.session.receiverChains → msg.senderRatchetKey ≠ pk →
          NoKeyInChains pk st'.session.receiverChains) ∧
        (∃ sck, st'.session.senderChain = some ⟨KeyPair.generate P.C rc, sck⟩))) := by
  unfold sessionSchemeU at hrec
  simp only [Option.map_eq_some_iff] at hrec
  rcases hrec with ⟨⟨g0, t0, i0, m0⟩, hrec0, htuple⟩
  rcases Prod.mk.inj htuple with ⟨rfl, _⟩
  unfold Params.receive at hrec0
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rw [htry] at hrec0; cases hrec0
  | ok msg =>
    rw [htry] at hrec0
    dsimp only [] at hrec0
    rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc g.session with ⟨r_tr, s_out⟩
    rw [htr] at hrec0
    cases r_tr with
    | error _ => cases hrec0
    | ok m_plain =>
      dsimp only [] at hrec0
      refine ⟨msg, rfl, ?_⟩
      cases hfind :
          g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
      | some idx =>
        have hsc_eq := ((receive_setRootKey_of_findIdx_some P g.session.rootKey g c rc msg idx
          htry hfind).2 g0 t0 i0 m0 (by
            unfold Params.receive
            rw [htry]
            dsimp only []
            rw [htr]
            exact hrec0)).1
        rw [hfind] at hrec0
        dsimp only [] at hrec0
        injection hrec0 with htuple0
        rcases Prod.mk.inj htuple0 with ⟨rfl, _⟩
        have hex := tryDecryptFromRecord_existing_props P g msg rc idx m_plain s_out hfind htr
        exact Or.inl ⟨idx, rfl, rfl, rfl, hsc_eq, hex.2.2.1, hex.2.2.2⟩
      | none =>
        rw [hfind] at hrec0
        dsimp only [] at hrec0
        injection hrec0 with htuple0
        rcases Prod.mk.inj htuple0 with ⟨rfl, _⟩
        have hnp := tryDecryptFromRecord_none_props P g msg rc m_plain s_out hfind htr
        refine Or.inr ⟨rfl, rfl, ?_, hnp.1, hnp.2.1, hnp.2.2⟩
        simp [List.length_append]

omit [SampleableType Pt] in
theorem hop2DH_support_window_props {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (idx : Option ℕ) (coins : BitVec 256)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hfind : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none)
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2DH P Dh encT decT h idx coins g msg rc).run st)).run tbl))
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ) (u : Option (Hop2Upd Pt))
    (hsome : z.1.1 = some ((st', t', i', m'), u)) :
    st'.epoch = g.epoch + 1 ∧
    st'.chainEpochs = (g.chainEpochs ++ [g.epoch + 1]).drop
      ((g.chainEpochs.length + 1) - st'.session.receiverChains.length) ∧
    (∃ ckR, st'.session.receiverChains.length =
      (RatchetState.evictReceiverChains
        (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ckR, []⟩])).length) ∧
    (∀ pk, NoKeyInChains pk g.session.receiverChains → msg.senderRatchetKey ≠ pk →
      NoKeyInChains pk st'.session.receiverChains) ∧
    (∃ sck, st'.session.senderChain = some ⟨KeyPair.generate P.C rc, sck⟩) := by
  unfold hop2DH at hz
  cases hdec : decT msg.senderRatchetKey with
  | none =>
    rw [hdec] at hz
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; cases hsome
  | some T =>
    rw [hdec] at hz
    dsimp only [] at hz
    split_ifs at hz with hT
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; cases hsome
    · cases hsc : g.session.senderChain with
      | none =>
        rw [hsc] at hz
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; cases hsome
      | some sc =>
        rw [hsc] at hz
        simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨⟨⟨r1, st1⟩, tbl1⟩, _, hz2⟩
        cases r1 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz2
          subst hz2; cases hsome
        | some p1 =>
          rcases p1 with ⟨idx1, rkM, ckR⟩
          simp only [stateT_lift_run_hop2, StateT.run_bind, bind_assoc, pure_bind,
            simulateQ_bind, MonadAttach.mem_support_bind] at hz2
          rcases hz2 with ⟨⟨r2, tbl2⟩, _, hz3⟩
          cases r2 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz3
            subst hz3; cases hsome
          | some p2 =>
            rcases p2 with ⟨idx2, rk2, ckS, pend⟩
            dsimp only [] at hz3
            set prev := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
            have hstep := tryDecryptFromRecord_steppedSess P g msg rc prev
              rk2 ckR (some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩) hfind
            dsimp only [] at hstep
            rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper rc
              { steppedSessBase g msg prev ckR with
                rootKey := rk2
                senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ } with ⟨r_tr, s_out⟩
            have htr' : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper rc
              { g.session with
                previousCounter := prev
                rootKey := rk2
                receiverChains := RatchetState.evictReceiverChains
                  (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ } = (r_tr, s_out) := htr
            rw [htr'] at hz3
            cases r_tr with
            | error _ =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hz3
              subst hz3; cases hsome
            | ok m_plain =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hz3
              subst hz3
              injection hsome with hpair
              rcases Prod.mk.inj hpair with ⟨h4, rfl⟩
              rcases Prod.mk.inj h4 with ⟨rfl, _⟩
              have hsp := tryDecryptFromRecord_stepped_props P g msg rc prev rk2 ckR
                (some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩) m_plain s_out hfind htr'
              have hs_out_sc : s_out.senderChain = some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ := by
                rw [htr] at hstep
                injection hstep with _ hs_eq
                rw [hs_eq]
              exact ⟨rfl, rfl, ⟨⟨ckR, 0⟩, hsp.2.2.1⟩, hsp.2.2.2, ⟨⟨ckS, 0⟩, hs_out_sc⟩⟩

omit [SampleableType Pt] in
theorem hop2Recv_support_window_props {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT h g c rc).run st)).run tbl))
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ) (u : Option (Hop2Upd Pt))
    (hsome : z.1.1 = some ((st', t', i', m'), u)) :
    ∃ msg, SignalMessage.tryFrom P.codec c = .ok msg ∧
      ((∃ idx, g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
          some idx ∧
        st'.epoch = g.epoch ∧
        st'.chainEpochs =
            g.chainEpochs.drop (g.chainEpochs.length - st'.session.receiverChains.length) ∧
        st'.session.senderChain = g.session.senderChain ∧
        st'.session.receiverChains.length = g.session.receiverChains.length ∧
        (∀ pk, NoKeyInChains pk g.session.receiverChains →
            NoKeyInChains pk st'.session.receiverChains)) ∨
       (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none ∧
        st'.epoch = g.epoch + 1 ∧
        st'.chainEpochs = (g.chainEpochs ++ [g.epoch + 1]).drop
          ((g.chainEpochs.length + 1) - st'.session.receiverChains.length) ∧
        (∃ ckR, st'.session.receiverChains.length =
          (RatchetState.evictReceiverChains
            (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ckR, []⟩])).length) ∧
        (∀ pk, NoKeyInChains pk g.session.receiverChains → msg.senderRatchetKey ≠ pk →
          NoKeyInChains pk st'.session.receiverChains) ∧
        (∃ sck, st'.session.senderChain = some ⟨KeyPair.generate P.C rc, sck⟩))) := by
  unfold hop2Recv at hz
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ =>
    rw [htry] at hz
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; cases hsome
  | ok msg =>
    rw [htry] at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hidx : st.2.idx g.party with
    | none =>
      rw [hidx] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp only [Option.map_eq_some_iff] at hsome
      rcases hsome with ⟨⟨st1, t1, i1, m1⟩, hrec, hpair⟩
      rcases Prod.mk.inj hpair with ⟨h4, rfl⟩
      rcases Prod.mk.inj h4 with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨rfl, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨rfl, rfl⟩
      rw [← htry]
      exact sessionSchemeU_receive_window_props P g c rc st1 t1 i1 m1 hrec
    | some t =>
      rw [hidx] at hz
      dsimp only [] at hz
      cases hfind :
          g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
      | none =>
        rw [hfind] at hz
        simp only [Option.isNone_none, ↓reduceIte] at hz
        have hdh := hop2DH_support_window_props P Dh encT decT h (some t) (st.2.coins g.party)
          g msg rc st tbl hfind z hz st' t' i' m' u hsome
        exact ⟨msg, rfl, Or.inr ⟨hfind, hdh⟩⟩
      | some i =>
        rw [hfind] at hz
        simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        simp only [Option.map_eq_some_iff] at hsome
        rcases hsome with ⟨⟨st1, t1, i1, m1⟩, hrec, hpair⟩
        rcases Prod.mk.inj hpair with ⟨h4, rfl⟩
        rcases Prod.mk.inj h4 with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨rfl, rfl⟩
        rw [← htry]
        exact sessionSchemeU_receive_window_props P g c rc st1 t1 i1 m1 hrec



omit [SampleableType Pt] in
theorem hop2GuessUnit_le_hop2CreateCollUnit (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) :
    hop2GuessUnit Dh ≤ hop2CreateCollUnit Dh := by
  unfold hop2GuessUnit
  refine iSup_le fun T => ?_
  by_cases hT0 : T = 0
  · subst hT0
    have hemp : {x : BitVec 256 | Dh.dh x Dh.base = 0} = ∅ := by
      ext x
      simp [hX.1.dh_ne_zero x Dh.base hX.1.base_ne_zero]
    simp [hemp]
  · exact dh_createColl_single_le_hop2CreateCollUnit Dh Dh.base T hT0

end Hop2Coupling
end CryptoVerification.E2E.SpkHop1
