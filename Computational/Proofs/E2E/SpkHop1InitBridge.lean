/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1Phases01B
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.SignalWireRoundTrip

/-!
# Initial Hop 2 Bridge

Bounds the `boolDist` of `spkLeakRed` under a random function by the `k = 0` hybrid
`hop2PrgRedK` plus epoch-0 forgery and collision error terms
(`evalDist_spkLeakRed_boolDist_le_hop2PrgRedK_zero`).
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
  CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoGames.CKA (DHFun)
section HInitBridge
variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]
abbrev SpkBadSt (Pt : Type) (ℓ : ℕ) := SpkRefSt Pt ℓ
omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrSpkRef_run_of_badSpkCorrA_false {ℓ : ℕ} (decT : PublicKey → Option Pt) (encT : Pt →
    PublicKey) (Q : Party) (st : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (b : Bool)
    (hbad : badSpkCorrA decT encT st Q = false) : (corrSpkRef (Pt := Pt) ℓ decT encT Q).run (st, L,
        b) =
    (liftSpkRef (Pt := Pt) (SM.corrR (configRefuseEarlyBobCorr decT encT) Q)).run (st, L, b) := by
  simp [corrSpkRef, liftSpkRef, hbad]
def spkDeliverPostL {ℓ : ℕ} (P : Params Bytes PQC) (s : BitVec 256) (Q : Party) (c : Bytes) (g₀ :
    GhostState Bytes) (r : SM.Record (CBC.Plain ℓ) Bytes)
    (res : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ)) (stL : SpkBadSt Pt ℓ) :
        Option (SM.RecvResult (CBC.Plain ℓ)) × SpkBadSt Pt ℓ :=
  match res with
  | none => (some .rejected, stL)
  | some (st', t', i', m') =>
    (some (.accepted t' i' (if stL.1.chall.contains r.pos then none else some m')),
      (stL.1.accept Q st' r.pos, stL.2.1, stL.2.2 || hop2BadAt P s g₀ c))
def spkInjectPostL {ℓ : ℕ} (P : Params Bytes PQC) (qep : ℕ) (s : BitVec 256) (Q : Party) (c :
    Bytes) (g₀ : GhostState Bytes)
    (res : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ)) (stL : SpkBadSt Pt ℓ) :
        Option (SM.RecvResult (CBC.Plain ℓ)) × SpkBadSt Pt ℓ :=
  match res with
  | none => (some .rejected, stL)
  | some (st', t', i', m') =>
    let bad' := stL.2.2 || hop2BadAt P s g₀ c
    if qep + 1 < t' then
      (some .rejected, (stL.1, stL.2.1, bad'))
    else
      let pos : SM.Pos := ⟨Q.other, t', i'⟩
      if stL.1.trivial 3 pos then
        (some (.accepted t' i' (some m')), (stL.1.accept Q st' pos, stL.2.1, bad'))
      else
        (some .rejected, ({ stL.1 with win := true }, stL.2.1, bad'))
structure Hop2Init3Rel {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (s x prk : BitVec 256) (A0 : Pt)
    (stL : SpkBadSt Pt ℓ) (stR : Hop2State Pt ℓ) : Prop where
  inv_R : Hop2GameInv P decT encT stR
  st1_eq : stL.1 =
      patchGamePartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx stR.1
  bad_eq : stL.2.2 = stR.2.bad
  idx_A : stR.2.idx .A = none ∨ (stR.2.idx .A = some 1 ∧ (stR.1.st .A).chainEpochs = [0])
  idx_B : (stR.2.idx .B = none ∧ (stR.1.st .B).epoch ≠ 0) ∨
    (stR.2.idx .B = some 0 ∧ (stR.1.st .B).epoch = 0 ∧ stR.1.epoch .B = 0 ∧
      stR.2.coins .B = x ∧ (stR.1.st .B).chainEpochs = [] ∧
      (stR.1.st .B).session.receiverChains = [] ∧
      ∃ ck0, (stR.1.st .B).session.senderChain =
        some ⟨KeyPair.generate P.C x, ⟨ck0, 0⟩⟩)
  tbl_rel : ∀ T : Pt,
    (Dh.dh s T = Dh.dh s A0 →
      (tableFor Dh s stL.2.1).lookup (Dh.dh s T) = some prk ∧
      stR.2.made.lookup (0, Dh.dh x T) = some (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).2) ∧
    (Dh.dh s T ≠ Dh.dh s A0 →
      stR.2.made.lookup (0, Dh.dh x T) = none ∧
      (tableFor Dh s stL.2.1).lookup (Dh.dh s T) = stR.2.lazy.lookup (0, Dh.dh x T))
omit [Zero Pt] [SampleableType Pt] in
theorem hop2Init3Rel_init {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (decT :
    PublicKey → Option Pt) (encT : Pt → PublicKey)
    (s x prk ck0 alice pqr : BitVec 256) (b : Bool) (hker : ∀ (z : BitVec 256) (P_pt P' : Pt),
        Dh.dh z P_pt = Dh.dh z P' ↔ Dh.dh s P_pt = Dh.dh s P') :
    let A0 := Dh.dh alice Dh.base
    let I0 := Dh.dh x A0
    let ck1 := (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).2
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
    let sRef := initGameSpkRef P ℓ b s prk alice pqr
    Hop2Init3Rel P Dh decT encT s x prk A0
      (patchGameSpk P.C x ck0 sRef, [(A0, prk)], false)
      (initSt, aux0) := by
  intro A0 I0 ck1 spk sessA stA stB initSt aux0 sRef
  refine ⟨hop2GameInv_init P decT encT b ck0 x alice pqr ck1 I0, ?_, rfl, Or.inr ⟨rfl, rfl⟩,
    Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨ck0, rfl⟩⟩, ?_⟩
  · dsimp only [sRef, initSt,
      aux0]; rw [← initGameSpk_eq_patchGameSpk]; unfold patchGamePartyIdx; dsimp only []; congr 1
    funext Q
    cases Q <;> rfl
  · intro T
    have hiff : (Dh.dh x T = I0) ↔ (Dh.dh s T = Dh.dh s A0) := hker x T A0
    constructor
    · intro hs
      have hx : Dh.dh x T = I0 := hiff.mpr hs
      dsimp only [aux0, tableFor, List.map, List.lookup]; simp [hs, hx, ck1]
    · intro hns
      have hnx : Dh.dh x T ≠ I0 := fun hx => hns (hiff.mp hx)
      have hbeq_s : (Dh.dh s T == Dh.dh s A0) = false := beq_eq_false_iff_ne.mpr hns
      have hne_pair : (((0 : ℕ), Dh.dh x T) == ((0 : ℕ), I0)) = false := by simp [hnx]
      dsimp only [aux0, tableFor, List.map, List.lookup]; rw [hbeq_s, hne_pair]; exact ⟨rfl, rfl⟩
omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitR_support_epoch_B_zero {ℓ : ℕ} (P : Params Bytes PQC) (decT : PublicKey →
    Option Pt) (encT : Pt → PublicKey) (qep : ℕ) (x : Party × CBC.Plain ℓ × Option PQC)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (he0 : st.epoch .B = 0) :
        ∀ z ∈ support ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st),
    z.2.st .B = st.st .B ∧ z.2.epoch .B = 0 := by
  rcases x with ⟨Q, m, r⟩
  intro z hz
  unfold SM.transmitR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz; simp only [StateT.run_bind,
      StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, SM.transmitImpl,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, he0⟩
    · rw [StateT.run_bind] at hz; simp only [StateT.run_monadLift, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : st.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨rfl, he0⟩
      | some st1 =>
        simp only [hep, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hz
        subst hz
        have hst := (CryptoVerification.E2E.Relabel.GameEq.epMgmt_st_trans hep).1
        have heB := (SpkHop2.epMgmt_epoch_pos_of_noBobEpoch0 hok hep).2.mpr he0
        have hQ : Q = .A := by
          cases Q with
          | A => rfl
          | B =>
            unfold noBobSendInEpoch0 at hok; simp [he0] at hok
        subst hQ
        unfold SM.GameState.record; dsimp only []
        rw [Function.update_of_ne (by decide), hst]
        exact ⟨rfl, heB⟩
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, he0⟩
omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challR_support_epoch_B_zero {ℓ : ℕ} (P : Params Bytes PQC) (decT : PublicKey →
    Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC) (st :
        SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (he0 : st.epoch .B = 0) :
    ∀ z ∈ support ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st),
        z.2.st .B = st.st .B ∧ z.2.epoch .B = 0 := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  intro z hz
  unfold SM.challR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz; simp only [StateT.run_bind,
      StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, SM.challImpl, StateT.run_bind,
      StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, he0⟩
    · rw [StateT.run_bind] at hz; simp only [StateT.run_monadLift, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : st.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨rfl, he0⟩
      | some st1 =>
        simp only [hep] at hz
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨rfl, he0⟩
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          have hst := (CryptoVerification.E2E.Relabel.GameEq.epMgmt_st_trans hep).1
          have heB := (SpkHop2.epMgmt_epoch_pos_of_noBobEpoch0 hok hep).2.mpr he0
          have hQ : Q = .A := by
            cases Q with
            | A => rfl
            | B =>
              unfold noBobSendInEpoch0 at hok; simp [he0] at hok
          subst hQ
          unfold SM.GameState.record; dsimp only []
          rw [Function.update_of_ne (by decide), hst]
          exact ⟨rfl, heB⟩
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, he0⟩
omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrR_support_epoch_B_zero {ℓ : ℕ} (decT : PublicKey → Option Pt) (encT : Pt →
    PublicKey) (Q : Party) (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    ∀ z ∈ support ((SM.corrR (configRefuseEarlyBobCorr decT encT) Q).run st), z.2.st = st.st ∧ z.2.epoch =
        st.epoch := by
  intro z hz
  unfold SM.corrR at hz; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl⟩
omit [Zero Pt] [SampleableType Pt] in
theorem Hop2Init3Rel.of_st1_step {ℓ : ℕ} {P : Params Bytes PQC} {Dh :
    DHFun (BitVec 256) Pt} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {s x prk : BitVec 256} {A0 : Pt} {stL : SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ} (hrel :
        Hop2Init3Rel P Dh decT encT s x prk A0 stL stR)
    (st1' : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (hinv' :
        Hop2GameInv P decT encT (st1', stR.2)) (hstep : StSendStep P stR.1 st1')
    (hb0 : stR.1.epoch .B = 0 → st1'.st .B = stR.1.st .B ∧ st1'.epoch .B = 0) :
        Hop2Init3Rel P Dh decT encT s x prk A0
    (patchGamePartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx st1', stL.2.1,
        stL.2.2)
      (st1', stR.2) where
  inv_R := hinv'
  st1_eq := rfl
  bad_eq := hrel.bad_eq
  idx_A := by
    rcases hrel.idx_A with hnone | ⟨hsome, hce⟩
    · exact Or.inl hnone
    · right
      refine ⟨hsome, ?_⟩
      rcases hstep .A with heq | ⟨m, r, heq⟩
      · rw [heq]; exact hce
      · rw [heq, (sessionSchemeU_send_props P (stR.1.st .A) m r).2.1]; exact hce
  idx_B := by
    rcases hrel.idx_B with ⟨hnone, hne0⟩ | ⟨hsome, he0, hep0, hcoins, hce, hrc, hsc⟩
    · left
      refine ⟨hnone, ?_⟩
      rcases hstep .B with heq | ⟨m, r, heq⟩
      · rw [heq]; exact hne0
      · rw [heq]; obtain ⟨_, _, hep⟩ :=
          SpkHop2.sessionSenderInv_send P (stR.1.st .B) m r (hrel.inv_R.sender_inv .B)
        rcases hep with h1 | h2 <;> omega
    · right
      obtain ⟨hstB, hepB⟩ := hb0 hep0; rw [hstB, hepB]; exact ⟨hsome, he0, rfl, hcoins, hce, hrc,
          hsc⟩
  tbl_rel := hrel.tbl_rel
theorem sessionSchemeU_receive_epoch_ne_zero {ℓ : ℕ} (P : Params Bytes PQC) (g :
    GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ) (hne : g.epoch ≠ 0) (hrec :
        (sessionSchemeU P ℓ).receive g c rc = some (st', t', i', m')) : st'.epoch ≠ 0 := by
  unfold sessionSchemeU Params.receive at hrec; simp only [Option.map_eq_some_iff] at hrec
  rcases hrec with ⟨⟨g1, t1, i1, m1⟩, hy, htuple⟩
  rcases Prod.mk.inj htuple with ⟨rfl, _⟩
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rw [htry] at hy; cases hy
  | ok msg =>
    rw [htry] at hy; dsimp only [] at hy; rcases htr :
        SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc g.session with ⟨r_tr, s_out⟩
    rw [htr] at hy
    cases r_tr with
    | error _ => cases hy
    | ok m_plain =>
      dsimp only [] at hy
      injection hy with hy'
      rcases Prod.mk.inj hy' with ⟨rfl, _⟩
      cases g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) <;>
        dsimp only [] <;> omega
theorem receiveB0Post_epoch_ne_zero {ℓ : ℕ} (P : Params Bytes PQC) (g : GhostState Bytes) (msg :
    SignalMessage) (rc prk : BitVec 256)
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ) (h : receiveB0Post P ℓ g msg rc prk =
        some (st', t', i', m')) : st'.epoch ≠ 0 := by
  unfold receiveB0Post at h; dsimp only [] at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h'
      rcases Prod.mk.inj h' with ⟨rfl, _⟩
      dsimp only []; omega
structure Hop2Init3RecvOutRel {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (s x prk : BitVec 256) (A0 : Pt) (Q : Party) (c : Bytes) (rc : BitVec 256)
    (stR : Hop2State Pt ℓ)
    (outL : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × List (Pt × BitVec 256))
    (outR : Hop2Out Pt ℓ × Hop2State Pt ℓ) : Prop where
  mem_supp : (outR, ([] : List (Pt × BitVec 256))) ∈ support
    ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR)).run [])
  st1_eq : outR.2.1 = stR.1
  idx_eq : outR.2.2.idx = stR.2.idx
  coins_eq : outR.2.2.coins = stR.2.coins
  made_eq : outR.2.2.made = stR.2.made
  bad_eq : outR.2.2.bad = stR.2.bad
  res_eq : outL.1 = outR.1.map (fun r =>
    (patchPartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1
      ((hop2Commit stR.2 Q r.2).idx Q) r.1.1, r.1.2))
  on_some : ∀ r ∈ outR.1,
    (∀ R ≠ Q, (hop2Commit stR.2 Q r.2).idx R = stR.2.idx R ∧
      (hop2Commit stR.2 Q r.2).coins R = stR.2.coins R) ∧
    (hop2Commit stR.2 Q r.2).made = stR.2.made ∧
    (Q = .A → (hop2Commit stR.2 .A r.2).idx .A = none ∨
      ((hop2Commit stR.2 .A r.2).idx .A = some 1 ∧ r.1.1.chainEpochs = [0])) ∧
    (Q = .B → (hop2Commit stR.2 .B r.2).idx .B = none ∧ r.1.1.epoch ≠ 0)
  tbl_rel : ∀ T : Pt,
    (Dh.dh s T = Dh.dh s A0 →
      (tableFor Dh s outL.2).lookup (Dh.dh s T) = some prk ∧
      outR.2.2.made.lookup (0, Dh.dh x T) = some (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).2) ∧
    (Dh.dh s T ≠ Dh.dh s A0 →
      outR.2.2.made.lookup (0, Dh.dh x T) = none ∧
      (tableFor Dh s outL.2).lookup (Dh.dh s T) = outR.2.2.lazy.lookup (0, Dh.dh x T))
omit [SampleableType Pt] in
theorem Hop2Init3RecvOutRel.deliverPost {ℓ : ℕ} {P : Params Bytes PQC} {Dh :
    DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {decT : PublicKey → Option Pt} {encT : Pt →
    PublicKey}
    {s x prk : BitVec 256} {A0 : Pt} {Q : Party} {c : Bytes} {rc : BitVec 256} {stL :
        SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ}
    {outL : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × List (Pt × BitVec 256)} {outR :
        Hop2Out Pt ℓ × Hop2State Pt ℓ} (r : SM.Record (CBC.Plain ℓ) Bytes)
    (hrel : Hop2Init3Rel P Dh decT encT s x prk A0 stL stR) (hout :
        Hop2Init3RecvOutRel P Dh encPt decT encT s x prk A0 Q c rc stR outL outR) :
    (spkDeliverPostL P s Q c (stL.1.st Q) r outL.1 (stL.1, outL.2, stL.2.2)).1 =
        (hop2DeliverPost P s Q c (stR.1.st Q) r outR.1 outR.2).1 ∧
        Hop2Init3Rel P Dh decT encT s x prk A0
    (spkDeliverPostL P s Q c (stL.1.st Q) r outL.1 (stL.1, outL.2,
        stL.2.2)).2 (hop2DeliverPost P s Q c (stR.1.st Q) r outR.1 outR.2).2 := by
  have hinv_post :
      Hop2GameInv P decT encT (hop2DeliverPost P s Q c (stR.1.st Q) r outR.1 outR.2).2 :=
    IsDeliverOrInjectPost.preserves_hop2GameInv (qep := 0) (Or.inl ⟨r, rfl⟩) hrel.inv_R
      (outR, []) hout.mem_supp
  rcases outR with ⟨o, stR'⟩
  rcases outL with ⟨res, L'⟩
  dsimp only [] at hout hinv_post ⊢
  cases o with
  | none =>
    have hres : res = none := by simpa using hout.res_eq
    subst hres
    dsimp only [spkDeliverPostL, hop2DeliverPost]
    refine ⟨rfl, hinv_post, ?_, hrel.bad_eq.trans hout.bad_eq.symm, ?_, ?_, hout.tbl_rel⟩
    · rw [hrel.st1_eq, hout.st1_eq, hout.idx_eq]
    · rw [hout.idx_eq, hout.st1_eq]; exact hrel.idx_A
    · rw [hout.idx_eq, hout.coins_eq, hout.st1_eq]; exact hrel.idx_B
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    have hst1_eq : stR'.1 = stR.1 := hout.st1_eq
    have hidx_eq : stR'.2.idx = stR.2.idx := hout.idx_eq
    have hcoins_eq : stR'.2.coins = stR.2.coins := hout.coins_eq
    have hmade_eq : stR'.2.made = stR.2.made := hout.made_eq
    have hbad_eq : stR'.2.bad = stR.2.bad := hout.bad_eq
    have htbl : ∀ T : Pt, (Dh.dh s T = Dh.dh s A0 → (tableFor Dh s L').lookup (Dh.dh s T) =
        some prk ∧
          stR'.2.made.lookup (0, Dh.dh x T) =
              some (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).2) ∧
        (Dh.dh s T ≠ Dh.dh s A0 →
          stR'.2.made.lookup (0, Dh.dh x T) = none ∧
          (tableFor Dh s L').lookup (Dh.dh s T) = stR'.2.lazy.lookup (0, Dh.dh x T)) := hout.tbl_rel
    obtain ⟨hoth, hmade, hA, hB⟩ := hout.on_some ((st', t', i', m'), u) (by simp)
    have hres : res =
        some (patchPartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1 ((hop2Commit stR.2 Q
        u).idx Q) st', t', i', m') := by simpa using hout.res_eq
    subst hres
    have hbad_at : hop2BadAt P s (stL.1.st Q) c = hop2BadAt P s (stR.1.st Q) c :=
        by rw [hrel.st1_eq]; exact hop2BadAt_patchPartyIdx P s 1 _ (stR.2.idx Q) (stR.1.st Q) c
    have hcomm_eq : (hop2Commit stR'.2 Q u).idx = (hop2Commit stR.2 Q u).idx ∧
        (hop2Commit stR'.2 Q u).coins = (hop2Commit stR.2 Q u).coins ∧
        (hop2Commit stR'.2 Q u).made = (hop2Commit stR.2 Q u).made ∧
        (hop2Commit stR'.2 Q u).lazy = stR'.2.lazy := by
      cases u <;> simp [hop2Commit, hidx_eq, hcoins_eq, hmade_eq]
    dsimp only [spkDeliverPostL, hop2DeliverPost]
    have hchall : stL.1.chall = stR'.1.chall := by rw [hrel.st1_eq, hst1_eq]; rfl
    refine ⟨by rw [hchall], hinv_post, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only []; rw [hrel.st1_eq, hst1_eq,
        hcomm_eq.1]; exact patchGamePartyIdx_accept 1 _ stR.2.idx (hop2Commit stR.2 Q u).idx stR.1 Q
        st' r.pos
        (fun R hR => (hoth R hR).1)
    · dsimp only []; rw [hrel.bad_eq, hbad_eq, hbad_at]
    · dsimp only [SM.GameState.accept]; rw [hcomm_eq.1, hst1_eq]
      cases Q with
      | A =>
        rw [Function.update_self]; exact hA rfl
      | B =>
        rw [(hoth .A (by decide)).1, Function.update_of_ne (by decide)]
        exact hrel.idx_A
    · dsimp only [SM.GameState.accept]; rw [hcomm_eq.1, hcomm_eq.2.1, hst1_eq]
      cases Q with
      | A =>
        rw [(hoth .B (by decide)).1, (hoth .B (by decide)).2, Function.update_of_ne (by decide)]
        exact hrel.idx_B
      | B =>
        left
        rw [Function.update_self]; exact hB rfl
    · dsimp only []; rw [hcomm_eq.2.2.1, hcomm_eq.2.2.2, hmade, ← hmade_eq]; exact htbl
omit [SampleableType Pt] in
theorem Hop2Init3RecvOutRel.injectPost {ℓ : ℕ} {P : Params Bytes PQC} {Dh :
    DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {decT : PublicKey → Option Pt} {encT : Pt →
    PublicKey}
    {qep : ℕ} {s x prk : BitVec 256} {A0 : Pt} {Q : Party} {c : Bytes} {rc : BitVec 256} {stL :
        SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ}
    {outL : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × List (Pt × BitVec 256)} {outR :
        Hop2Out Pt ℓ × Hop2State Pt ℓ} (hrel : Hop2Init3Rel P Dh decT encT s x prk A0 stL stR)
    (hout : Hop2Init3RecvOutRel P Dh encPt decT encT s x prk A0 Q c rc stR outL outR) :
        (spkInjectPostL P qep s Q c (stL.1.st Q) outL.1 (stL.1, outL.2, stL.2.2)).1 =
    (hop2InjectPost P qep s Q c (stR.1.st Q) outR.1 outR.2).1 ∧
        Hop2Init3Rel P Dh decT encT s x prk A0 (spkInjectPostL P qep s Q c (stL.1.st Q) outL.1
        (stL.1, outL.2, stL.2.2)).2
    (hop2InjectPost P qep s Q c (stR.1.st Q) outR.1 outR.2).2 := by
  have hinv_post :
      Hop2GameInv P decT encT (hop2InjectPost P qep s Q c (stR.1.st Q) outR.1 outR.2).2 :=
    IsDeliverOrInjectPost.preserves_hop2GameInv (qep := qep) (Or.inr rfl) hrel.inv_R
      (outR, []) hout.mem_supp
  rcases outR with ⟨o, stR'⟩
  rcases outL with ⟨res, L'⟩
  dsimp only [] at hout hinv_post ⊢
  cases o with
  | none =>
    have hres : res = none := by simpa using hout.res_eq
    subst hres
    dsimp only [spkInjectPostL, hop2InjectPost]
    refine ⟨rfl, hinv_post, ?_, hrel.bad_eq.trans hout.bad_eq.symm, ?_, ?_, hout.tbl_rel⟩
    · rw [hrel.st1_eq, hout.st1_eq, hout.idx_eq]
    · rw [hout.idx_eq, hout.st1_eq]; exact hrel.idx_A
    · rw [hout.idx_eq, hout.coins_eq, hout.st1_eq]; exact hrel.idx_B
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    have hst1_eq : stR'.1 = stR.1 := hout.st1_eq
    have hidx_eq : stR'.2.idx = stR.2.idx := hout.idx_eq
    have hcoins_eq : stR'.2.coins = stR.2.coins := hout.coins_eq
    have hmade_eq : stR'.2.made = stR.2.made := hout.made_eq
    have hbad_eq : stR'.2.bad = stR.2.bad := hout.bad_eq
    have htbl : ∀ T : Pt, (Dh.dh s T = Dh.dh s A0 → (tableFor Dh s L').lookup (Dh.dh s T) =
        some prk ∧
          stR'.2.made.lookup (0, Dh.dh x T) =
              some (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).2) ∧
        (Dh.dh s T ≠ Dh.dh s A0 →
          stR'.2.made.lookup (0, Dh.dh x T) = none ∧
          (tableFor Dh s L').lookup (Dh.dh s T) = stR'.2.lazy.lookup (0, Dh.dh x T)) := hout.tbl_rel
    obtain ⟨hoth, hmade, hA, hB⟩ := hout.on_some ((st', t', i', m'), u) (by simp)
    have hres : res =
        some (patchPartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1 ((hop2Commit stR.2 Q
        u).idx Q) st', t', i', m') := by simpa using hout.res_eq
    subst hres
    have hbad_at : hop2BadAt P s (stL.1.st Q) c = hop2BadAt P s (stR.1.st Q) c :=
        by rw [hrel.st1_eq]; exact hop2BadAt_patchPartyIdx P s 1 _ (stR.2.idx Q) (stR.1.st Q) c
    have htriv : stL.1.trivial 3 ⟨Q.other, t', i'⟩ = stR'.1.trivial 3 ⟨Q.other, t', i'⟩ :=
        by rw [hrel.st1_eq, hst1_eq]; rfl
    dsimp only [spkInjectPostL, hop2InjectPost]; rw [htriv]
    split_ifs with hqep htr
    · refine ⟨rfl, by simpa [hop2InjectPost, hqep] using hinv_post, ?_, ?_, ?_, ?_, htbl⟩
      · dsimp only []; rw [hrel.st1_eq, hst1_eq, hidx_eq]
      · dsimp only []; rw [hrel.bad_eq, hbad_eq, hbad_at]
      · dsimp only []; rw [hidx_eq, hst1_eq]; exact hrel.idx_A
      · dsimp only []; rw [hidx_eq, hcoins_eq, hst1_eq]; exact hrel.idx_B
    · set b_new := stR'.2.bad || hop2BadAt P s (stR.1.st Q) c
      have hcomm_eq : (hop2Commit { stR'.2 with
                                    bad := b_new } Q u).idx = (hop2Commit stR.2 Q u).idx ∧
          (hop2Commit { stR'.2 with bad := b_new } Q u).coins = (hop2Commit stR.2 Q u).coins ∧
          (hop2Commit { stR'.2 with bad := b_new } Q u).made = (hop2Commit stR.2 Q u).made ∧
          (hop2Commit { stR'.2 with bad := b_new } Q u).lazy = stR'.2.lazy ∧
          (hop2Commit { stR'.2 with bad := b_new } Q u).bad = b_new := by
        cases u <;> simp [hop2Commit, hidx_eq, hcoins_eq, hmade_eq]
      refine ⟨rfl, by simpa [hop2InjectPost, hqep, htr] using hinv_post, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []; rw [hrel.st1_eq, hst1_eq,
          hcomm_eq.1]; exact patchGamePartyIdx_accept 1 _ stR.2.idx (hop2Commit stR.2 Q u).idx stR.1
          Q st' ⟨Q.other, t', i'⟩
          (fun R hR => (hoth R hR).1)
      · rw [hcomm_eq.2.2.2.2]; dsimp only [b_new]; rw [hrel.bad_eq, hbad_eq, hbad_at]
      · dsimp only [SM.GameState.accept]; rw [hcomm_eq.1, hst1_eq]
        cases Q with
        | A =>
          rw [Function.update_self]; exact hA rfl
        | B =>
          rw [(hoth .A (by decide)).1, Function.update_of_ne (by decide)]
          exact hrel.idx_A
      · dsimp only [SM.GameState.accept]; rw [hcomm_eq.1, hcomm_eq.2.1, hst1_eq]
        cases Q with
        | A =>
          rw [(hoth .B (by decide)).1, (hoth .B (by decide)).2, Function.update_of_ne (by decide)]
          exact hrel.idx_B
        | B =>
          left
          rw [Function.update_self]; exact hB rfl
      · dsimp only []; rw [hcomm_eq.2.2.1, hcomm_eq.2.2.2.1, hmade, ← hmade_eq]; exact htbl
    · refine ⟨rfl, by simpa [hop2InjectPost, hqep, htr] using hinv_post, ?_, ?_, ?_, ?_, htbl⟩
      · dsimp only [patchGamePartyIdx]; rw [hrel.st1_eq, hst1_eq, hidx_eq]; rfl
      · dsimp only []; rw [hrel.bad_eq, hbad_eq, hbad_at]
      · dsimp only []; rw [hidx_eq, hst1_eq]; exact hrel.idx_A
      · dsimp only []; rw [hidx_eq, hcoins_eq, hst1_eq]; exact hrel.idx_B
omit [SampleableType Pt] in
theorem hop2Init3RecvOutRel_of_none {ℓ : ℕ} {P : Params Bytes PQC} {Dh :
    DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {decT : PublicKey → Option Pt} {encT : Pt →
    PublicKey}
    {s x prk : BitVec 256} {A0 : Pt} {Q : Party} {c : Bytes} {rc : BitVec 256} {stL :
        SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ} (hrel :
        Hop2Init3Rel P Dh decT encT s x prk A0 stL stR)
    (hmem : ((none, stR), ([] : List (Pt × BitVec 256))) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
    ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR)).run [])) :
    Hop2Init3RecvOutRel P Dh encPt decT encT s x prk A0 Q c rc stR (none, stL.2.1) (none, stR) where
  mem_supp := hmem
  st1_eq := rfl
  idx_eq := rfl
  coins_eq := rfl
  made_eq := rfl
  bad_eq := rfl
  res_eq := rfl
  on_some := by simp
  tbl_rel := hrel.tbl_rel
omit [SampleableType Pt] in
theorem hop2Init3RecvOutRel_of_B0_out {ℓ : ℕ} {P : Params Bytes PQC} {Dh :
    DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {decT : PublicKey → Option Pt} {encT : Pt →
    PublicKey}
    {s x prk : BitVec 256} {A0 : Pt} {c : Bytes} {rc u : BitVec 256} {msg : SignalMessage} {stR :
        Hop2State Pt ℓ}
    {L' : List (Pt × BitVec 256)} {lazy' : List ((ℕ × Pt) × BitVec 256)} (hmem :
        (((receiveB0Post P ℓ (stR.1.st .B) msg rc u).map (fun r => (r, some ⟨none, rc, none⟩)),
        (stR.1, { stR.2 with lazy := lazy' })), ([] : List (Pt × BitVec 256))) ∈ support
      ((simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st .B) c rc).run stR)).run []))
    (htbl : ∀ T : Pt,
      (Dh.dh s T = Dh.dh s A0 →
        (tableFor Dh s L').lookup (Dh.dh s T) = some prk ∧
        stR.2.made.lookup (0, Dh.dh x T) = some (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).2) ∧
      (Dh.dh s T ≠ Dh.dh s A0 →
        stR.2.made.lookup (0, Dh.dh x T) = none ∧
        (tableFor Dh s L').lookup (Dh.dh s T) = lazy'.lookup (0, Dh.dh x T))) :
    Hop2Init3RecvOutRel P Dh encPt decT encT s x prk A0 .B c rc stR
      (receiveB0Post P ℓ (stR.1.st .B) msg rc u, L')
      ((receiveB0Post P ℓ (stR.1.st .B) msg rc u).map (fun r => (r, some ⟨none, rc, none⟩)),
        (stR.1, { stR.2 with lazy := lazy' })) where
  mem_supp := hmem
  st1_eq := rfl
  idx_eq := rfl
  coins_eq := rfl
  made_eq := rfl
  bad_eq := rfl
  res_eq := by
    cases receiveB0Post P ℓ (stR.1.st .B) msg rc u with
    | none => rfl
    | some val =>
      rcases val with ⟨st', t', i', m'⟩
      simp [hop2Commit, patchPartyIdx]
  on_some := by
    intro r hr
    simp only [Option.mem_def, Option.map_eq_some_iff] at hr
    rcases hr with ⟨⟨st', t', i', m'⟩, hrec, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro R hR; simp [hop2Commit, Function.update_of_ne hR]
    · simp [hop2Commit]
    · intro hA; cases hA
    · intro _; exact ⟨by simp [hop2Commit],
        receiveB0Post_epoch_ne_zero P (stR.1.st .B) msg rc u st' t' i' m' hrec⟩
  tbl_rel := htbl
theorem stepReceiveSpk_bind_hop2Recv_zero_nonB0 {ℓ : ℕ} {P : Params Bytes PQC} (hcodec :
    P.codec = protoSignalCodec) {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (hX :
        X25519RealizesDh P.C Dh encPt encT) (hz : ∀ z, Dh.dh z 0 = 0)
    {s x prk : BitVec 256} {A0 : Pt} {Q : Party} {c : Bytes} {rc : BitVec 256} {stL :
        SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ} (hrel :
        Hop2Init3Rel P Dh decT encT s x prk A0 stL stR)
    (horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true) (hnonB0 : Q = .A ∨ (Q = .B ∧
        (stR.1.st .B).epoch ≠ 0))
    (FL : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × List (Pt × BitVec 256) →
        ProbComp Bool) (FR : Hop2Out Pt ℓ × Hop2State Pt ℓ → ProbComp Bool) (d : ℝ≥0∞)
    (hF : ∀ outL outR, Hop2Init3RecvOutRel P Dh encPt decT encT s x prk A0 Q c rc stR outL outR →
        𝒟[FL outL] {true} ≤ 𝒟[FR outR] {true} + d) :
    𝒟[stepReceiveSpk P ℓ Dh encT decT s (stL.1.st Q) c rc stL.2.1 >>= FL] {true} ≤
    𝒟[simulateQ (pureStepImpl ((extractPRF P.C.F encPt).tag (Ratchet.rootExpand P.C.F (keyToBytes32
        prk)).1))
    ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR) >>= FR] {true}
        + d := by
  have hpQ : (stR.1.st Q).party = Q := hrel.inv_R.party_eq Q
  have hstL_Q : stL.1.st Q =
      patchPartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1 (stR.2.idx Q) (stR.1.st Q) :=
      by rw [hrel.st1_eq]; rfl
  have hcondF : ((stL.1.st Q).party == .B && (stL.1.st Q).epoch == 0) = false := by
    rw [hstL_Q, patchPartyIdx_party, patchPartyIdx_epoch, hpQ]
    rcases hnonB0 with rfl | ⟨rfl, hne0⟩
    · rfl
    · simp [hne0]
  have hidx_cases : stR.2.idx (stR.1.st Q).party = none ∨ (stR.2.idx (stR.1.st Q).party = some 1 ∧
      ∃ ckS0, (stR.1.st Q).session.senderChain =
          some ⟨KeyPair.generate P.C (stR.2.coins (stR.1.st Q).party), ckS0⟩) := by
    rw [hpQ]
    rcases hnonB0 with rfl | ⟨rfl, hne0⟩
    · rcases hrel.idx_A with hnone | ⟨hsome, _⟩
      · exact Or.inl hnone
      · exact Or.inr ⟨hsome, hrel.inv_R.coins_sc .A (by simp [hsome])⟩
    · rcases hrel.idx_B with ⟨hnone, _⟩ | ⟨_, he0, _⟩
      · exact Or.inl hnone
      · exact absurd he0 hne0
  obtain ⟨opt, hrun, hmap, hprops⟩ :=
    hop2Recv_patchPartyIdx_eq (ℓ := ℓ) P hcodec Dh encPt encT decT hX hz 0 1 (by omega)
      (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1
      (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).2
      (stR.1.st Q) c rc stR horc hidx_cases
  have hrun' : (hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR =
      pure (opt, stR) := hrun
  unfold stepReceiveSpk; rw [hcondF]; simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, hrun',
      simulateQ_pure]
  apply hF
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, hrel.tbl_rel⟩
  · rw [hrun']; simp [StateT.run_pure]
  · rw [hpQ] at hmap; dsimp only []; rw [hstL_Q, ← hmap]
  · intro r hr
    obtain ⟨hidx_out, hoth, hmade, _, _⟩ := hprops r hr; rw [hpQ] at hidx_out hoth hmade
    refine ⟨hoth, hmade, fun hQA => ?_, fun hQB => ?_⟩
    · subst hQA
      rcases hidx_out with hnone | ⟨hsome, _⟩
      · exact Or.inl hnone
      · right
        refine ⟨hsome, ?_⟩
        rcases hrel.idx_A with hnone_A | ⟨hsome_A, hce_A⟩
        · exfalso
          have hrun_none :
              (hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st .A) c rc).run stR =
              pure (((sessionSchemeU P ℓ).receive (stR.1.st .A) c rc).map (fun x => (x, none)),
                  stR) := by
            unfold hop2Recv
            cases htry : SignalMessage.tryFrom P.codec c with
            | error _ => simp [StateT.run_pure, sessionSchemeU, Params.receive, htry]
            | ok msg => simp [StateT.run_bind, StateT.run_get, hpQ, hnone_A, StateT.run_pure]
          rw [hrun'] at hrun_none
          injection hrun_none with hpair
          rcases Prod.mk.inj hpair with ⟨hopt_eq, _⟩
          subst hopt_eq
          simp only [Option.mem_def, Option.map_eq_some_iff] at hr
          rcases hr with ⟨_, _, rfl⟩
          simp [hop2Commit, hnone_A] at hsome
        · rcases r with ⟨⟨st', t', i', m'⟩, u⟩
          have hsupp_R : ((opt, stR), ([] :
              List (Pt × BitVec 256))) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
                ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st .A) c rc).run
                    stR)).run []) := by
            rw [hrun']; simp [StateT.run_pure]
          obtain ⟨msg, htry, ⟨idx, hfind, _, hce_eq, _, hlen_eq, _⟩ | ⟨hfind_none, _⟩⟩ :=
            hop2Recv_support_window_props P Dh encT decT (hop2HybPrg P encPt 0 prk)
              (stR.1.st .A) c rc stR [] ((opt, stR), []) hsupp_R st' t' i' m' u hr
          · have hne_nil : (stR.1.st .A).session.receiverChains ≠ [] :=
              by intro hnil; simp [hnil] at hfind
            have hpos_len : 0 < st'.session.receiverChains.length :=
                by rw [hlen_eq]; exact List.length_pos_iff.mpr hne_nil
            rw [hce_eq, hce_A]
            simp [Nat.sub_eq_zero_of_le (by omega : 1 ≤ st'.session.receiverChains.length)]
          · exfalso
            have hrun2 := hrun'
            unfold hop2Recv at hrun2; rw [htry] at hrun2; dsimp only [] at hrun2
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hpQ, hsome_A, hfind_none,
                Option.isNone_none, ↓reduceIte] at hrun2; unfold hop2DH at hrun2
            cases hdec : decT msg.senderRatchetKey with
            | none =>
              rw [hdec] at hrun2; simp only [Pure.pure] at hrun2
              injection hrun2 with hpair
              rcases Prod.mk.inj hpair with ⟨hopt_none, _⟩
              subst hopt_none; cases hr
            | some T =>
              rw [hdec] at hrun2; dsimp only [] at hrun2
              split at hrun2
              · simp only [Pure.pure] at hrun2
                injection hrun2 with hpair
                rcases Prod.mk.inj hpair with ⟨hopt_none, _⟩
                subst hopt_none; cases hr
              · cases hsc : (stR.1.st .A).session.senderChain with
                | none =>
                  rw [hsc] at hrun2; simp only [Pure.pure] at hrun2
                  injection hrun2 with hpair
                  rcases Prod.mk.inj hpair with ⟨hopt_none, _⟩
                  subst hopt_none; cases hr
                | some sc =>
                  rw [hsc] at hrun2; unfold hop2RecvHalf at hrun2; dsimp only [] at hrun2
                  split at hrun2
                  · simp only [Pure.pure] at hrun2
                    injection hrun2 with hpair
                    rcases Prod.mk.inj hpair with ⟨hopt_none, _⟩
                    subst hopt_none; cases hr
                  · have hnot_le : ¬ ((1 : ℕ) ≤ (hop2HybPrg P encPt 0 prk).k) :=
                      Nat.not_succ_le_zero 0
                    have hstep_pure : ∀ x, (hop2HybPrg P encPt 0 prk).step x =
                        pure ((extractPRF P.C.F encPt).tag (Ratchet.rootExpand P.C.F (keyToBytes32
                        prk)).1 x) :=
                      fun _ => rfl
                    simp only [hnot_le, ↓reduceIte, StateT.run_bind, stateT_lift_run_hop2,
                        hstep_pure, StateT.run_pure,
                        pure_bind] at hrun2; unfold hop2SendHalf at hrun2
                    simp only [] at hrun2
                    split at hrun2
                    · simp only [Pure.pure] at hrun2
                      injection hrun2 with hpair
                      rcases Prod.mk.inj hpair with ⟨hopt_none, _⟩
                      subst hopt_none; cases hr
                    · simp only [pure_bind] at hrun2
                      split at hrun2
                      · simp only [Pure.pure] at hrun2
                        injection hrun2 with hpair
                        rcases Prod.mk.inj hpair with ⟨hopt_none, _⟩
                        subst hopt_none; cases hr
                      · simp only [Pure.pure] at hrun2
                        injection hrun2 with hpair
                        rcases Prod.mk.inj hpair with ⟨hopt_eq, _⟩
                        rw [← hopt_eq] at hr
                        injection hr with hr_eq
                        rcases Prod.mk.inj hr_eq with ⟨_, hu_eq⟩
                        subst hu_eq
                        simp [hop2Commit] at hsome
    · subst hQB
      rcases hnonB0 with hA | ⟨_, hne0⟩
      · cases hA
      · rcases hrel.idx_B with ⟨hnone, _⟩ | ⟨_, he0, _⟩
        · have hrun_none :
            (hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st .B) c rc).run stR =
              pure (((sessionSchemeU P ℓ).receive (stR.1.st .B) c rc).map (fun x => (x, none)),
                  stR) := by
            unfold hop2Recv
            cases htry : SignalMessage.tryFrom P.codec c with
            | error _ => simp [StateT.run_pure, sessionSchemeU, Params.receive, htry]
            | ok msg => simp [StateT.run_bind, StateT.run_get, hpQ, hnone, StateT.run_pure]
          rw [hrun'] at hrun_none
          injection hrun_none with hpair
          rcases Prod.mk.inj hpair with ⟨hopt_eq, _⟩
          subst hopt_eq
          simp only [Option.mem_def, Option.map_eq_some_iff] at hr
          rcases hr with ⟨⟨st', t', i', m'⟩, hrec, rfl⟩
          exact ⟨by simp [hop2Commit, hnone],
            sessionSchemeU_receive_epoch_ne_zero P (stR.1.st .B) c rc st' t' i' m' hne0 hrec⟩
        · exact absurd he0 hne0
theorem hop2DH_tail_eq_receiveB0Post {ℓ : ℕ} (P : Params Bytes PQC) {Dh :
    DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {encT : Pt → PublicKey} (hX :
    X25519RealizesDh P.C Dh encPt encT)
    (g : GhostState Bytes) (msg : SignalMessage) (rc u : BitVec 256) (T : Pt) (st' :
        Hop2State Pt ℓ) (hpB : g.party = .B) (he0 : g.epoch = 0) (hce : g.chainEpochs = [])
    (hrc : g.session.receiverChains = []) (hT0 : T ≠ 0) (hencT : encT T = msg.senderRatchetKey) :
        rootCreateChain P.C (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
    msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey =
        .ok ((Ratchet.rootExpand P.C.F (keyToBytes32 ((extractPRF P.C.F encPt).tag
    (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1 (Dh.dh rc T)))).1,
        ⟨(Ratchet.rootExpand P.C.F (keyToBytes32 ((extractPRF P.C.F encPt).tag
    (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1 (Dh.dh rc T)))).2, 0⟩) ∧
    (match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
        { g.session with
          previousCounter := 0
          rootKey := (Ratchet.rootExpand P.C.F
            (keyToBytes32 ((extractPRF P.C.F encPt).tag
              (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1 (Dh.dh rc T)))).1
          receiverChains := RatchetState.evictReceiverChains
            (g.session.receiverChains ++ [(⟨msg.senderRatchetKey,
              some ⟨(Ratchet.rootExpand P.C.F (keyToBytes32 u)).2, 0⟩, []⟩ : ReceiverChain)])
          senderChain := some ⟨KeyPair.generate P.C rc,
            ⟨(Ratchet.rootExpand P.C.F
              (keyToBytes32 ((extractPRF P.C.F encPt).tag
                (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1 (Dh.dh rc T)))).2, 0⟩⟩ } with
      | (.error _, _) => (pure none : Hop2M Pt ℓ (Hop2Out Pt ℓ))
      | (.ok m, s_out) =>
        let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
          ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
        pure (some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m),
          some (⟨none, rc, none⟩ : Hop2Upd Pt)))).run st' =
      pure ((receiveB0Post P ℓ g msg rc u).map (fun r => (r, some (⟨none, rc, none⟩ :
          Hop2Upd Pt))), st') := by
  have hM := libX25519Rel_model hX
  have hpub : msg.senderRatchetKey.bytes.toList = encPt T :=
      by rw [← hencT]; exact encT_bytes_toList hX T
  have hcc := rootCreateChain_generate_honest P.C hM
    (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1 rc hT0 hpub
  have hup :
      Ratchet.rootExpand P.C.F (keyToBytes32 ((extractPRF P.C.F encPt).tag (Ratchet.rootExpand P.C.F
      (keyToBytes32 u)).1 (Dh.dh rc T))) =
      (rootPRNG P.C.F encPt).up (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1 (Dh.dh rc T) :=
    SpkHop2.expand_extract_eq_rootPRNG P.C.F encPt _ _
  rw [hup]
  refine ⟨hcc, ?_⟩
  unfold receiveB0Post expandPRG; dsimp only []; rw [hcc, hpB, he0, hce,
      hrc]; dsimp only [List.nil_append, List.length_nil, Nat.zero_add]
  have hevict : RatchetState.evictReceiverChains ([⟨msg.senderRatchetKey,
      some ⟨(Ratchet.rootExpand P.C.F (keyToBytes32 u)).2, 0⟩, []⟩] : List ReceiverChain) =
      [⟨msg.senderRatchetKey, some ⟨(Ratchet.rootExpand P.C.F (keyToBytes32 u)).2, 0⟩, []⟩] := rfl
  rw [hevict]
  rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B) msg .whisper rc _ with
      ⟨r_tr, s_out⟩
  cases r_tr <;> rfl
omit [SampleableType Pt] in
theorem mem_support_lazyImpl_hop2Recv_of_pureStep {ℓ : ℕ} {P : Params Bytes PQC} {Dh :
    DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {prk : BitVec 256} {Q : Party} {c :
        Bytes} {rc : BitVec 256}
    {stR : Hop2State Pt ℓ} {outR : Hop2Out Pt ℓ × Hop2State Pt ℓ} (h : outR ∈ support
    (simulateQ (pureStepImpl ((extractPRF P.C.F encPt).tag (Ratchet.rootExpand P.C.F (keyToBytes32
        prk)).1))
    ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR))) : (outR,
        ([] : List (Pt × BitVec 256))) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
    ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR)).run []) := by
  rw [hop2HybPrg, simulateQ_lazyImpl_hop2Recv_pureStep]; simp only [support_map,
      Set.mem_image]; exact ⟨outR, h, rfl⟩
theorem hop2Recv_B0_pureStep_eq {ℓ : ℕ} {P : Params Bytes PQC} {Dh :
    DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {decT : PublicKey → Option Pt} {encT : Pt →
    PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) {s x prk ck0 : BitVec 256} {A0 : Pt} {c : Bytes} {rc :
        BitVec 256} {stL : SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ}
    (hrel : Hop2Init3Rel P Dh decT encT s x prk A0 stL stR) (hsome : stR.2.idx .B = some 0) (he0 :
        (stR.1.st .B).epoch = 0) (hcoins : stR.2.coins .B = x)
    (hce : (stR.1.st .B).chainEpochs = []) (hrc : (stR.1.st .B).session.receiverChains =
        []) (hsc : (stR.1.st .B).session.senderChain = some ⟨KeyPair.generate P.C x, ⟨ck0, 0⟩⟩) :
    simulateQ (pureStepImpl ((extractPRF P.C.F encPt).tag (Ratchet.rootExpand P.C.F (keyToBytes32
        prk)).1))
    ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st .B) c rc).run stR) =
      match SignalMessage.tryFrom P.codec c with
      | .error _ => pure (none, stR)
      | .ok msg =>
        match decT msg.senderRatchetKey with
        | none => pure (none, stR)
        | some T =>
          if T = 0 ∨ encT T ≠ msg.senderRatchetKey then
            pure (none, stR)
          else if Dh.dh s T = Dh.dh s A0 then
            pure ((receiveB0Post P ℓ (stR.1.st .B) msg rc prk).map
              (fun r => (r, some (⟨none, rc, none⟩ : Hop2Upd Pt))),
              (stR.1, { stR.2 with lazy := stR.2.lazy }))
          else
            match stR.2.lazy.lookup (0, Dh.dh x T) with
            | some u =>
              pure ((receiveB0Post P ℓ (stR.1.st .B) msg rc u).map
                (fun r => (r, some (⟨none, rc, none⟩ : Hop2Upd Pt))),
                (stR.1, { stR.2 with lazy := stR.2.lazy }))
            | none => do
              let u ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
              return ((receiveB0Post P ℓ (stR.1.st .B) msg rc u).map
                (fun r => (r, some (⟨none, rc, none⟩ : Hop2Upd Pt))),
                (stR.1, { stR.2 with lazy := ((0, Dh.dh x T), u) :: stR.2.lazy })) := by
  set g := stR.1.st .B
  have hpB : g.party = .B := hrel.inv_R.party_eq .B
  have hM := libX25519Rel_model hX
  unfold hop2Recv
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => simp [StateT.run_pure]
  | ok msg =>
    dsimp only []
    have hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true := by simp [hrc]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hpB, hsome, hfind, ↓reduceIte,
        hcoins]; unfold hop2DH
    cases hdec : decT msg.senderRatchetKey with
    | none => simp [StateT.run_pure]
    | some T =>
      dsimp only []
      by_cases hT : T = 0 ∨ encT T ≠ msg.senderRatchetKey
      · simp [hT, StateT.run_pure]
      · simp only [hT, ↓reduceIte, hsc]
        have hT0 : T ≠ 0 := fun h0 => hT (Or.inl h0)
        have hencT : encT T = msg.senderRatchetKey :=
            Classical.not_not.mp fun hne => hT (Or.inr hne)
        have hxT0 : Dh.dh x T ≠ 0 := hM.dh_ne_zero x T hT0
        have hrcT0 : Dh.dh rc T ≠ 0 := hM.dh_ne_zero rc T hT0
        dsimp only [hop2HybPrg, pureStepHyb]
        by_cases hs : Dh.dh s T = Dh.dh s A0
        · obtain ⟨_, hlR⟩ := (hrel.tbl_rel T).1 hs
          have htail := (hop2DH_tail_eq_receiveB0Post (ℓ :=
              ℓ) P hX g msg rc prk T stR hpB he0 hce hrc hT0 hencT).2
          unfold hop2RecvHalf hop2SendHalf
          simp only [hs, hxT0, hrcT0, le_refl, Nat.not_lt_zero, Nat.add_one_ne_zero, ↓reduceIte,
              StateT.run_bind, StateT.run_get, StateT.run_pure, stateT_lift_run_hop2, bind_assoc,
              pure_bind, hlR]
          exact (congrArg (simulateQ _) htail).trans rfl
        · obtain ⟨hmR, _⟩ := (hrel.tbl_rel T).2 hs; unfold hop2RecvHalf hop2SendHalf hop2Lazy
          simp only [hs, hxT0, le_refl, ↓reduceIte, StateT.run_bind, StateT.run_get,
              StateT.run_pure, stateT_lift_run_hop2, bind_assoc, pure_bind, hmR]
          cases hlazy : stR.2.lazy.lookup (0, Dh.dh x T) with
          | some u =>
            obtain ⟨hcc, htail⟩ := hop2DH_tail_eq_receiveB0Post (ℓ :=
                ℓ) P hX g msg rc u T stR hpB he0 hce hrc hT0 hencT; simp only [StateT.run_pure,
                pure_bind, hcc]
            exact (congrArg (simulateQ _) htail).trans rfl
          | none =>
            simp only [stateT_lift_run_hop2, StateT.run_bind, StateT.run_set, StateT.run_pure,
                bind_assoc, pure_bind, simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
            refine bind_congr fun u => ?_
            obtain ⟨hcc, htail⟩ := hop2DH_tail_eq_receiveB0Post (ℓ := ℓ) P hX g msg rc u T
              (stR.1, { stR.2 with
                        lazy := ((0, Dh.dh x T), u) :: stR.2.lazy }) hpB he0 hce hrc hT0 hencT
            simp only [hcc, simulateQ_pure,
                pure_bind]; exact (congrArg (simulateQ _) htail).trans rfl
theorem stepReceiveSpk_bind_hop2Recv_zero_B0 {ℓ : ℕ} {P : Params Bytes PQC} {Dh :
    DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {s x prk ck0 : BitVec 256} (hX :
        X25519RealizesDh P.C Dh encPt encT)
    (hker : ∀ (z : BitVec 256) (P_pt P' : Pt), Dh.dh z P_pt = Dh.dh z P' ↔ Dh.dh s P_pt =
        Dh.dh s P') {A0 : Pt} {c : Bytes} {rc : BitVec 256}
    {stL : SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ} (hrel :
        Hop2Init3Rel P Dh decT encT s x prk A0 stL stR) (hsome : stR.2.idx .B = some 0) (he0 :
        (stR.1.st .B).epoch = 0)
    (hcoins : stR.2.coins .B = x) (hce : (stR.1.st .B).chainEpochs = []) (hrc :
        (stR.1.st .B).session.receiverChains = [] )
    (hsc : (stR.1.st .B).session.senderChain = some ⟨KeyPair.generate P.C x, ⟨ck0, 0⟩⟩)
    (FL : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × List (Pt × BitVec 256) →
        ProbComp Bool) (FR : Hop2Out Pt ℓ × Hop2State Pt ℓ → ProbComp Bool) (d : ℝ≥0∞)
    (hF : ∀ outL outR, Hop2Init3RecvOutRel P Dh encPt decT encT s x prk A0 .B c rc stR outL outR →
        𝒟[FL outL] {true} ≤ 𝒟[FR outR] {true} + d) :
    𝒟[stepReceiveSpk P ℓ Dh encT decT s (stL.1.st .B) c rc stL.2.1 >>= FL] {true} ≤
    𝒟[simulateQ (pureStepImpl ((extractPRF P.C.F encPt).tag (Ratchet.rootExpand P.C.F (keyToBytes32
        prk)).1))
    ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st .B) c rc).run stR) >>= FR] {true}
        + d := by
  have hpB : (stR.1.st .B).party = .B := hrel.inv_R.party_eq .B
  have hstL_B : stL.1.st .B = stR.1.st .B :=
      by rw [hrel.st1_eq]; dsimp only [patchGamePartyIdx]; rw [hsome]; rfl
  have hcondT : ((stR.1.st .B).party == .B && (stR.1.st .B).epoch == 0) = true := by simp [hpB, he0]
  have hpure := hop2Recv_B0_pureStep_eq hX hrel hsome he0 hcoins hce hrc hsc (c := c) (rc := rc)
  unfold stepReceiveSpk; rw [hstL_B, hcondT, hpure]; simp only [↓reduceIte]; unfold stepReceiveB0
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ =>
    simp only [pure_bind]
    apply hF
    apply hop2Init3RecvOutRel_of_none hrel
    apply mem_support_lazyImpl_hop2Recv_of_pureStep
    rw [hpure, htry]; simp
  | ok msg =>
    dsimp only []
    cases hdec : decT msg.senderRatchetKey with
    | none =>
      simp only [pure_bind]
      apply hF
      apply hop2Init3RecvOutRel_of_none hrel
      apply mem_support_lazyImpl_hop2Recv_of_pureStep
      rw [hpure]; simp [htry, hdec]
    | some T =>
      dsimp only []
      by_cases hT : T = 0 ∨ encT T ≠ msg.senderRatchetKey
      · simp only [hT, ↓reduceIte, pure_bind]
        apply hF
        apply hop2Init3RecvOutRel_of_none hrel
        apply mem_support_lazyImpl_hop2Recv_of_pureStep
        rw [hpure]; simp [htry, hdec, hT]
      · simp only [hT, ↓reduceIte]
        by_cases hs : Dh.dh s T = Dh.dh s A0
        · obtain ⟨hlL, _⟩ := (hrel.tbl_rel T).1 hs; unfold stepTableFor; rw [hlL]; simp only [hs,
            ↓reduceIte, pure_bind]
          apply hF
          apply hop2Init3RecvOutRel_of_B0_out ?_ hrel.tbl_rel
          apply mem_support_lazyImpl_hop2Recv_of_pureStep
          rw [hpure]; simp [htry, hdec, hT, hs]
        · obtain ⟨_, hlEq⟩ := (hrel.tbl_rel T).2 hs; unfold stepTableFor; simp only [hs, ↓reduceIte]
          cases hlazy : stR.2.lazy.lookup (0, Dh.dh x T) with
          | some u =>
            have hlL : (tableFor Dh s stL.2.1).lookup (Dh.dh s T) = some u := hlEq.trans hlazy
            rw [hlL]; simp only [pure_bind]
            apply hF
            apply hop2Init3RecvOutRel_of_B0_out ?_ hrel.tbl_rel
            apply mem_support_lazyImpl_hop2Recv_of_pureStep
            rw [hpure]; simp [htry, hdec, hT, hs, hlazy]
          | none =>
            have hlL : (tableFor Dh s stL.2.1).lookup (Dh.dh s T) = none := hlEq.trans hlazy
            rw [hlL]; simp only [bind_assoc, pure_bind]
            refine bind_evalDist_true_le_add_of_support_window ($ᵗ BitVec 256) _ _ d fun u _ => ?_
            apply hF
            apply hop2Init3RecvOutRel_of_B0_out
            · apply mem_support_lazyImpl_hop2Recv_of_pureStep
              rw [hpure]; simp [htry, hdec, hT, hs, hlazy]
            · intro T'
              constructor
              · intro hs'
                have hne_s : (Dh.dh s T' == Dh.dh s T) = false :=
                  beq_eq_false_iff_ne.mpr fun heq => hs (heq ▸ hs')
                dsimp only [tableFor, List.map,
                    List.lookup]; rw [hne_s]; exact (hrel.tbl_rel T').1 hs'
              · intro hns'
                obtain ⟨hmR', hlEq'⟩ := (hrel.tbl_rel T').2 hns'
                refine ⟨hmR', ?_⟩
                dsimp only [tableFor, List.map, List.lookup]
                by_cases heq_s : Dh.dh s T' = Dh.dh s T
                · have heq_x : Dh.dh x T' = Dh.dh x T := (hker x T' T).mpr heq_s
                  simp [heq_s, heq_x]
                · have hne_x : Dh.dh x T' ≠ Dh.dh x T := fun hx => heq_s ((hker x T' T).mp hx)
                  have hbeq_s : (Dh.dh s T' == Dh.dh s T) = false := beq_eq_false_iff_ne.mpr heq_s
                  have hbeq_x : (((0 : ℕ), Dh.dh x T') == ((0 : ℕ), Dh.dh x T)) = false :=
                      by simp [hne_x]
                  rw [hbeq_s, hbeq_x]; exact hlEq'
theorem stepReceiveSpk_bind_hop2Recv_zero {ℓ : ℕ} {P : Params Bytes PQC} (hcodec : P.codec =
    protoSignalCodec) {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {s x prk : BitVec 256} (hX :
        X25519RealizesDh P.C Dh encPt encT) (hz : ∀ z, Dh.dh z 0 = 0)
    (hker : ∀ (z : BitVec 256) (P_pt P' : Pt), Dh.dh z P_pt = Dh.dh z P' ↔ Dh.dh s P_pt =
        Dh.dh s P') {A0 : Pt} {Q : Party} {c : Bytes} {rc : BitVec 256}
    {stL : SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ} (hrel :
        Hop2Init3Rel P Dh decT encT s x prk A0 stL stR) (horc :
        ratchetKeyAdmissible protoSignalCodec decT encT c = true)
    (FL : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × List (Pt × BitVec 256) →
        ProbComp Bool) (FR : Hop2Out Pt ℓ × Hop2State Pt ℓ → ProbComp Bool) (d : ℝ≥0∞)
    (hF : ∀ outL outR, Hop2Init3RecvOutRel P Dh encPt decT encT s x prk A0 Q c rc stR outL outR →
        𝒟[FL outL] {true} ≤ 𝒟[FR outR] {true} + d) :
    𝒟[stepReceiveSpk P ℓ Dh encT decT s (stL.1.st Q) c rc stL.2.1 >>= FL] {true} ≤ 𝒟[(simulateQ
        (lazyImpl (Pt := Pt))
    ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR)).run [] >>= fun
        z => FR z.1] {true} + d := by
  have heq : ((simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR)).run [] >>=
        fun z => FR z.1) =
      (simulateQ (pureStepImpl ((extractPRF P.C.F encPt).tag (Ratchet.rootExpand P.C.F (keyToBytes32
          prk)).1))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR) >>= FR) :=
            by
    rw [hop2HybPrg, simulateQ_lazyImpl_hop2Recv_pureStep]; simp [map_eq_bind_pure_comp, bind_assoc]
  rw [heq]
  cases Q with
  | A =>
    exact stepReceiveSpk_bind_hop2Recv_zero_nonB0 hcodec hX hz hrel horc (Or.inl rfl) FL FR d hF
  | B =>
    rcases hrel.idx_B with ⟨_, hne0⟩ | ⟨hsome, he0, _, hcoins, hce, hrc, ck0, hsc⟩
    · exact stepReceiveSpk_bind_hop2Recv_zero_nonB0 hcodec hX hz hrel horc (Or.inr ⟨rfl,
        hne0⟩) FL FR d hF
    · exact stepReceiveSpk_bind_hop2Recv_zero_B0 hX hker hrel hsome he0 hcoins hce hrc hsc FL FR d
        hF
omit [SampleableType Pt] in
theorem hop2DeliverPost_preserves_pos_chainEpochs {ℓ : ℕ} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (h : Hop2Hyb Pt) (Q : Party) (c : Bytes) (r_rec :
        SM.Record (CBC.Plain ℓ) Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ) (tbl :
        List (Pt × BitVec 256))
    (hpos : ∀ e ∈ (st.1.st .A).chainEpochs, 0 < e) (z :
        (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256)) (hz :
        z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
    ((hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st)).run tbl)) :
        Hop2WindowInv P (hop2DeliverPost P s Q c (st.1.st Q) r_rec z.1.1 z.1.2).2.1 := by
  have hdone := hop2Recv_support_done P Dh encT decT h (st.1.st Q) c rc st tbl z hz
  cases ho : z.1.1 with
  | none =>
    dsimp only [hop2DeliverPost]; rw [hdone.1]; exact Or.inl hpos
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    dsimp only [hop2DeliverPost]; rw [hdone.1]
    left
    dsimp only [SM.GameState.accept, SM.GameState.delete]
    cases Q with
    | A =>
      rw [Function.update_self]; exact (hdone.2.2 st' t' i' m' u ho).2 hpos
    | B =>
      rw [Function.update_of_ne (by decide)]
      exact hpos
theorem evalDist_runSpkBad_deliver_le {ℓ : ℕ} {P : Params Bytes PQC} (hcodec : P.codec =
    protoSignalCodec) {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (hX :
        X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T) (hz : ∀ z,
        Dh.dh z 0 = 0)
    {s x prk : BitVec 256} (hker : ∀ (z : BitVec 256) (P_pt P' : Pt), Dh.dh z P_pt = Dh.dh z P' ↔
        Dh.dh s P_pt = Dh.dh s P') {A0 : Pt} {stL : SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ}
    (hrel : Hop2Init3Rel P Dh decT encT s x prk A0 stL stR) (hwin_inv :
        Hop2WindowInv P stR.1) (Q : Party) (c : Bytes)
    (cont_L : Option (SM.RecvResult (CBC.Plain ℓ)) → SpkBadSt Pt ℓ → ProbComp Bool)
    (cont_R : Option (SM.RecvResult (CBC.Plain ℓ)) → Hop2State Pt ℓ → List (Pt × BitVec 256) →
        ProbComp Bool) (d : ℝ≥0∞)
    (hcont : ∀ r sL sR, Hop2Init3Rel P Dh decT encT s x prk A0 sL sR → Hop2WindowInv P sR.1 →
        𝒟[cont_L r sL] {true} ≤ 𝒟[cont_R r sR []] {true} + d) :
    𝒟[(deliverSpkBad P ℓ Dh encT decT s (Q,
        c)).run stL >>= fun r => cont_L r.1 r.2] {true} ≤ 𝒟[(simulateQ (lazyImpl (Pt := Pt))
    ((hop2Deliver P Dh encT decT s (hop2HybPrg P encPt 0 prk) (Q,
        c)).run stR)).run [] >>= fun z => cont_R z.1.1 z.1.2 z.2] {true} + d + (5 :
        ℝ≥0∞) * hop2GuessUnit Dh := by
  have hwin_eq : stL.1.win = stR.1.win := by rw [hrel.st1_eq]; rfl
  have hin_eq : stL.1.inTransit Q.other c = stR.1.inTransit Q.other c := by rw [hrel.st1_eq]; rfl
  by_cases hwin : stR.1.win = true
  · have hwin_L : stL.1.win = true := hwin_eq.trans hwin
    unfold deliverSpkBad hop2Deliver; simp only [StateT.run_bind, StateT.run_get, StateT.run_mk,
        pure_bind, hwin_L, hwin, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact (hcont none stL stR hrel hwin_inv).trans le_self_add
  · have hwin_R : stR.1.win = false := Bool.eq_false_iff.mpr hwin
    have hwin_L : stL.1.win = false := hwin_eq.trans hwin_R
    cases hin_R : stR.1.inTransit Q.other c with
    | none =>
      have hin_L : stL.1.inTransit Q.other c = none := hin_eq.trans hin_R
      unfold deliverSpkBad hop2Deliver
      simp only [StateT.run_bind, StateT.run_get, StateT.run_mk, pure_bind, hwin_L, hwin_R,
          Bool.false_eq_true, ↓reduceIte, hin_L, hin_R, StateT.run_pure, simulateQ_pure]
      exact (hcont none stL stR hrel hwin_inv).trans le_self_add
    | some r =>
      have hin_L : stL.1.inTransit Q.other c = some r := hin_eq.trans hin_R
      have hrun_L : (deliverSpkBad P ℓ Dh encT decT s (Q, c)).run stL = (($ᵗ BitVec 256 :
          ProbComp (BitVec 256)) >>= fun rc =>
            stepReceiveSpk P ℓ Dh encT decT s (stL.1.st Q) c rc stL.2.1 >>= fun outL =>
              pure (spkDeliverPostL P s Q c (stL.1.st Q) r outL.1 (stL.1, outL.2, stL.2.2))) := by
        unfold deliverSpkBad; simp only [StateT.run_mk, hwin_L, Bool.false_eq_true, ↓reduceIte,
            hin_L]
        refine bind_congr fun rc => bind_congr fun outL => ?_
        cases outL.1 <;> rfl
      rw [hrun_L,
          hop2Deliver_run_eq_post P Dh encT decT s (hop2HybPrg P encPt 0 prk) Q c stR r hwin_R
          hin_R]
      have horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true :=
        inTransit_hop2GameInv hrel.inv_R hin_R
      have hpost_rhs :
          ((simulateQ (lazyImpl (Pt := Pt)) (do
            let rc ← hop2Unif (Pt := Pt)
            let res ← (hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR
            return hop2DeliverPost P s Q c (stR.1.st Q) r res.1 res.2)).run [] >>=
            fun z => cont_R z.1.1 z.1.2 z.2) =
          (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
            (simulateQ (lazyImpl (Pt := Pt))
              ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR)).run
                  [] >>=
              fun z =>
                let p := hop2DeliverPost P s Q c (stR.1.st Q) r z.1.1 z.1.2
                cont_R p.1 p.2 []) := by
        simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
            stateT_lift_probComp_run, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
        refine bind_congr fun rc => ?_
        rw [hop2HybPrg, simulateQ_lazyImpl_hop2Recv_pureStep]; simp [map_eq_bind_pure_comp,
            bind_assoc]
      rw [hpost_rhs]; simp only [bind_assoc, pure_bind]
      rcases hwin_inv with hpos | hcore
      · refine (bind_evalDist_true_le_add_of_support_window ($ᵗ BitVec 256) _ _ d fun rc _ =>
          ?_).trans
          le_self_add
        exact stepReceiveSpk_bind_hop2Recv_zero (Q := Q) (rc := rc) hcodec hX hz hker hrel horc
          (fun outL =>
            let p := spkDeliverPostL P s Q c (stL.1.st Q) r outL.1 (stL.1, outL.2, stL.2.2)
            cont_L p.1 p.2)
          (fun outR =>
            let p := hop2DeliverPost P s Q c (stR.1.st Q) r outR.1 outR.2
            cont_R p.1 p.2 [])
          d fun outL outR hout => by
            obtain ⟨hres_eq, hrel'⟩ := hout.deliverPost r hrel
            have hwin' := hop2DeliverPost_preserves_pos_chainEpochs P Dh encT decT s
              (hop2HybPrg P encPt 0 prk) Q c r rc stR [] hpos (outR, []) hout.mem_supp
            dsimp only []; rw [hres_eq]; exact hcont _ _ _ hrel' hwin'
      · have hcs_le : ((stR.1.st Q.other).session.receiverChains.length : ℝ≥0∞) ≤ 5 := by
          cases Q.other with | A => exact_mod_cast hcore.nA_le | B => exact_mod_cast hcore.csB_le
        have hbad_le : 𝒟[($ᵗ BitVec 256 :
            ProbComp (BitVec 256)) >>= fun rc => pure (hasKeyInChainsBool (KeyPair.generate P.C
            rc).publicKey
              (stR.1.st Q.other).session.receiverChains)] {true} ≤
            (5 : ℝ≥0∞) * hop2GuessUnit Dh :=
          (hasKeyInChainsBool_prob_le_hop2GuessUnit P Dh encPt decT encT hX hdec _).trans
            (mul_le_mul_of_nonneg_right hcs_le zero_le)
        refine (bind_apply_le_add_of_evalDist_le_on_good_window ($ᵗ BitVec 256) _ _
          (fun rc => hasKeyInChainsBool (KeyPair.generate P.C rc).publicKey
            (stR.1.st Q.other).session.receiverChains) d (fun rc hgood => ?_)).trans
          (add_le_add_right hbad_le _)
        exact stepReceiveSpk_bind_hop2Recv_zero (Q := Q) (rc := rc) hcodec hX hz hker hrel horc
          (fun outL =>
            let p := spkDeliverPostL P s Q c (stL.1.st Q) r outL.1 (stL.1, outL.2, stL.2.2)
            cont_L p.1 p.2)
          (fun outR =>
            let p := hop2DeliverPost P s Q c (stR.1.st Q) r outR.1 outR.2
            cont_R p.1 p.2 [])
          d fun outL outR hout => by
            obtain ⟨hres_eq, hrel'⟩ := hout.deliverPost r hrel
            have hwin' := hop2DeliverPost_preserves_hop2WindowInv P Dh encT decT s
              (hop2HybPrg P encPt 0 prk) Q c r rc stR [] (Or.inr hcore) hin_R hgood (outR,
                  []) hout.mem_supp
            dsimp only []; rw [hres_eq]; exact hcont _ _ _ hrel' hwin'
theorem evalDist_runSpkBad_inject_le {ℓ : ℕ} {P : Params Bytes PQC} (hcodec : P.codec =
    protoSignalCodec) {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (hX :
        X25519RealizesDh P.C Dh encPt encT) (hz : ∀ z, Dh.dh z 0 = 0) {qep : ℕ} {s x prk : BitVec 256}
    (hker : ∀ (z : BitVec 256) (P_pt P' : Pt), Dh.dh z P_pt = Dh.dh z P' ↔ Dh.dh s P_pt =
        Dh.dh s P') {A0 : Pt} {stL : SpkBadSt Pt ℓ} {stR : Hop2State Pt ℓ}
    (hrel : Hop2Init3Rel P Dh decT encT s x prk A0 stL stR) (hwin_inv :
        Hop2WindowInv P stR.1) (Q : Party) (c : Bytes)
    (cont_L : Option (SM.RecvResult (CBC.Plain ℓ)) → SpkBadSt Pt ℓ → ProbComp Bool)
    (cont_R : Option (SM.RecvResult (CBC.Plain ℓ)) → Hop2State Pt ℓ → List (Pt × BitVec 256) →
        ProbComp Bool) (d : ℝ≥0∞)
    (hcont : ∀ r sL sR, Hop2Init3Rel P Dh decT encT s x prk A0 sL sR → Hop2WindowInv P sR.1 →
        𝒟[cont_L r sL] {true} ≤ 𝒟[cont_R r sR []] {true} + d) :
    𝒟[(injectSpkBad P ℓ Dh encT decT qep s (Q,
        c)).run stL >>= fun r => cont_L r.1 r.2] {true} ≤ 𝒟[(simulateQ (lazyImpl (Pt := Pt))
    ((hop2Inject P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) (Q,
        c)).run stR)).run [] >>= fun z => cont_R z.1.1 z.1.2 z.2] {true} + d := by
  have hguard_eq : (stL.1.win || (stL.1.inTransit Q.other c).isSome || !(stL.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
      (stR.1.win || (stR.1.inTransit Q.other c).isSome || !(stR.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := by rw [hrel.st1_eq]; rfl
  by_cases hg : (stR.1.win || (stR.1.inTransit Q.other c).isSome || !(stR.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · have hg_L : (stL.1.win || (stL.1.inTransit Q.other c).isSome || !(stL.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hguard_eq.trans hg
    unfold injectSpkBad hop2Inject; simp only [StateT.run_bind, StateT.run_get, StateT.run_mk,
        pure_bind, hg_L, hg, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact hcont none stL stR hrel hwin_inv
  · have hg_R : (stR.1.win || (stR.1.inTransit Q.other c).isSome || !(stR.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
    have hg_L : (stL.1.win || (stL.1.inTransit Q.other c).isSome || !(stL.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := hguard_eq.trans hg_R
    have horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true :=
        by revert hg_R; cases ratchetKeyAdmissible protoSignalCodec decT encT c <;> simp
    have hrun_L : (injectSpkBad P ℓ Dh encT decT qep s (Q, c)).run stL = (($ᵗ BitVec 256 :
        ProbComp (BitVec 256)) >>= fun rc =>
          stepReceiveSpk P ℓ Dh encT decT s (stL.1.st Q) c rc stL.2.1 >>= fun outL =>
            pure (spkInjectPostL P qep s Q c (stL.1.st Q) outL.1 (stL.1, outL.2, stL.2.2))) := by
      unfold injectSpkBad; simp only [StateT.run_mk, hg_L, Bool.false_eq_true, ↓reduceIte
          ]
      refine bind_congr fun rc => bind_congr fun outL => ?_
      cases outL.1 with
      | none => rfl
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        dsimp only [spkInjectPostL]; split <;> [rfl; (split <;> rfl)]
    rw [hrun_L, hop2Inject_run_eq_post P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) Q c stR hg_R]
    have hpost_rhs :
        ((simulateQ (lazyImpl (Pt := Pt)) (do
          let rc ← hop2Unif (Pt := Pt)
          let res ← (hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR
          return hop2InjectPost P qep s Q c (stR.1.st Q) res.1 res.2)).run [] >>=
          fun z => cont_R z.1.1 z.1.2 z.2) =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
          (simulateQ (lazyImpl (Pt := Pt))
            ((hop2Recv P Dh encT decT (hop2HybPrg P encPt 0 prk) (stR.1.st Q) c rc).run stR)).run []
                >>=
            fun z =>
              let p := hop2InjectPost P qep s Q c (stR.1.st Q) z.1.1 z.1.2
              cont_R p.1 p.2 []) := by
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
          stateT_lift_probComp_run, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
      refine bind_congr fun rc => ?_
      rw [hop2HybPrg, simulateQ_lazyImpl_hop2Recv_pureStep]; simp [map_eq_bind_pure_comp,
          bind_assoc]
    rw [hpost_rhs]; simp only [bind_assoc, pure_bind]
    refine bind_evalDist_true_le_add_of_support_window ($ᵗ BitVec 256) _ _ d fun rc _ => ?_
    exact stepReceiveSpk_bind_hop2Recv_zero (Q := Q) (rc := rc) hcodec hX hz hker hrel horc
      (fun outL =>
        let p := spkInjectPostL P qep s Q c (stL.1.st Q) outL.1 (stL.1, outL.2, stL.2.2)
        cont_L p.1 p.2)
      (fun outR =>
        let p := hop2InjectPost P qep s Q c (stR.1.st Q) outR.1 outR.2
        cont_R p.1 p.2 [])
      d fun outL outR hout => by
        obtain ⟨hres_eq, hrel'⟩ := hout.injectPost (qep := qep) hrel
        have hwin' := hop2InjectPost_preserves_hop2WindowInv P Dh encT decT qep s
          (hop2HybPrg P encPt 0 prk) Q c rc stR [] hwin_inv (outR, []) hout.mem_supp
        dsimp only []; rw [hres_eq]; exact hcont _ _ _ hrel' hwin'
theorem evalDist_runSpkBad_le_runHop2_zero {ℓ : ℕ} {P : Params Bytes PQC} (hcodec : P.codec =
    protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {decT : PublicKey → Option Pt} {encT : Pt →
        PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T) (hz : ∀ z,
        Dh.dh z 0 = 0) (qep : ℕ) (s x prk : BitVec 256)
    (hker : ∀ (z : BitVec 256) (P_pt P' : Pt), Dh.dh z P_pt = Dh.dh z P' ↔ Dh.dh s P_pt =
        Dh.dh s P') (A0 : Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool) (rem :
        ℕ) (hq : SM.MakesAtMostQueries oa rem)
    (stL : SpkBadSt Pt ℓ) (stR : Hop2State Pt ℓ) (hrel :
        Hop2Init3Rel P Dh decT encT s x prk A0 stL stR) (hwin_inv : Hop2WindowInv P stR.1) :
    𝒟[runSpkBad P Dh encT decT qep s oa stL.1 stL.2.1 stL.2.2] {true} ≤ 𝒟[runHop2 P Dh encT decT qep
        s (hop2HybPrg P encPt 0 prk) oa stR []] {true} +
    ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem stL stR with
  | pure a =>
    rw [runSpkBad_pure, runHop2_pure, hrel.bad_eq]; exact le_self_add
  | query_bind t k_oa ih =>
    rw [SM.MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq; rw [runSpkBad_bind_query,
        runHop2_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2_unif]; dsimp only [spkBadImpl, StateT.lift,
        StateT.run]; simp only [bind_assoc, pure_bind]
      exact bind_evalDist_true_le_add_of_support_window _ _ _ _ fun a _ =>
        ih a rem (by simpa [SM.MakesAtMostQueries] using hq.2 a) stL stR hrel hwin_inv
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      rcases stL with ⟨st1L, LL, badL⟩
      have hst1L : st1L =
          patchGamePartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx stR.1 :=
          hrel.st1_eq
      dsimp only [spkBadImpl, hop2Impl]; rw [liftSpkRef_run, runHop2_hop2Lift', hst1L,
          transmitR_patchGamePartyIdx P decT encT qep 1 _ stR.2.idx stR.1 y_tr]
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, Prod.map]
      have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤ ((5 * rem : ℕ) :
          ℝ≥0∞) * hop2GuessUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
        (add_le_add le_rfl hle)
      have hinv' :=
          transmitR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep y_tr stR
          hrel.inv_R r hr
      have hwin' :=
          transmitR_support_hop2WindowInv P hcodec hL decT encT qep y_tr stR hrel.inv_R hwin_inv r
          hr
      have hstep := transmitR_support_stSendStep P decT encT qep y_tr stR.1 r hr
      have hb0 := fun he0 => transmitR_support_epoch_B_zero P decT encT qep y_tr stR.1 he0 r hr
      exact ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
        _ (r.2, stR.2) (hrel.of_st1_step r.2 hinv' hstep hb0) hwin'
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      rcases stL with ⟨st1L, LL, badL⟩
      have hst1L : st1L =
          patchGamePartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx stR.1 :=
          hrel.st1_eq
      dsimp only [spkBadImpl, hop2Impl]; rw [liftSpkRef_run, runHop2_hop2Lift', hst1L,
          challR_patchGamePartyIdx P decT encT qep 1 _ stR.2.idx stR.1 y_ch]
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, Prod.map]
      have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤ ((5 * rem : ℕ) :
          ℝ≥0∞) * hop2GuessUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
        (add_le_add le_rfl hle)
      have hinv' :=
          challR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep y_ch stR hrel.inv_R
          r hr
      have hwin' :=
          challR_support_hop2WindowInv P hcodec hL decT encT qep y_ch stR hrel.inv_R hwin_inv r hr
      have hstep := challR_support_stSendStep P decT encT qep y_ch stR.1 r hr
      have hb0 := fun he0 => challR_support_epoch_B_zero P decT encT qep y_ch stR.1 he0 r hr
      exact ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
        _ (r.2, stR.2) (hrel.of_st1_step r.2 hinv' hstep hb0) hwin'
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [spkBadImpl, hop2Impl]
      have hadd : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh + (5 :
          ℝ≥0∞) * hop2GuessUnit Dh = ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
        rw [← add_mul]; congr 1; exact_mod_cast (by omega : 5 * (rem - 1) + 5 = 5 * rem)
      refine (evalDist_runSpkBad_deliver_le hcodec hX hdec hz hker hrel hwin_inv Q c
        (fun r sL => runSpkBad P Dh encT decT qep s (k_oa r) sL.1 sL.2.1 sL.2.2)
        (fun r sR tR => runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) (k_oa r) sR tR)
        (((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh)
        (fun r sL sR hrel' hwin' =>
          ih r (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r) sL sR hrel' hwin')).trans
              ?_
      exact le_of_eq (by rw [add_assoc, hadd]; rfl)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      dsimp only [spkBadImpl, hop2Impl]
      have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤ ((5 * rem : ℕ) :
          ℝ≥0∞) * hop2GuessUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      refine (evalDist_runSpkBad_inject_le (qep := qep) hcodec hX hz hker hrel hwin_inv Q c
        (fun r sL => runSpkBad P Dh encT decT qep s (k_oa r) sL.1 sL.2.1 sL.2.2)
        (fun r sR tR => runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) (k_oa r) sR tR)
        (((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh)
        (fun r sL sR hrel' hwin' =>
          ih r (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r) sL sR hrel' hwin')).trans
        (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      rcases stL with ⟨st1L, LL, badL⟩
      dsimp only [spkBadImpl, hop2Impl]
      have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤ ((5 * rem : ℕ) :
          ℝ≥0∞) * hop2GuessUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      rcases hwin_inv with hpos | hcore
      · have hidxA : stR.2.idx .A = none := by
          rcases hrel.idx_A with hnone | ⟨_, hce⟩
          · exact hnone
          · exfalso; have h0 : 0 < 0 := hpos 0 (by simp [hce]); omega
        have hpatch_self : ∀ s_g : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes,
            patchGamePartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx s_g =
                s_g := by
          intro s_g; unfold patchGamePartyIdx; cases s_g; congr 1; funext R
          cases R with
          | A => simp [patchPartyIdx, hidxA]
          | B =>
            rcases hrel.idx_B with ⟨hnoneB, _⟩ | ⟨hsomeB, _⟩ <;> simp [patchPartyIdx, *]
        have hst1_eq : st1L = stR.1 := hrel.st1_eq.trans (hpatch_self stR.1)
        have hno0 : 0 ∉ (st1L.st .A).chainEpochs := fun h0 => by
          have := hpos 0 (hst1_eq ▸ h0); omega
        have hbad_corr : badSpkCorrA decT encT st1L y_corr = false := by simp [badSpkCorrA, hno0]
        rw [corrSpkRef_run_of_badSpkCorrA_false decT encT y_corr st1L LL badL hbad_corr,
            liftSpkRef_run, runHop2_hop2Lift', hst1_eq]; simp only [bind_assoc, pure_bind]
        refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
          (add_le_add le_rfl hle)
        have hinv' := corrR_support_hop2GameInv P decT encT y_corr stR hrel.inv_R r hr
        have hwin' := corrR_support_hop2WindowInv P decT encT y_corr stR.1 (Or.inl hpos) r hr
        have hstep := corrR_support_stSendStep P decT encT y_corr stR.1 r hr
        have hb0 : stR.1.epoch .B = 0 → r.2.st .B = stR.1.st .B ∧ r.2.epoch .B = 0 := fun he0 => by
          obtain ⟨hst, hep⟩ :=
              corrR_support_epoch_B_zero decT encT y_corr stR.1 r hr; exact ⟨congrFun hst .B,
              (congrFun hep .B).trans he0⟩
        have hrel' := hrel.of_st1_step r.2 hinv' hstep hb0
        dsimp only [] at hrel'; rw [hpatch_self r.2] at hrel'
        exact ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
          (r.2, LL, badL) (r.2, stR.2) hrel' hwin'
      · have hnA := hcore.nA_le
        have hepA := hcore.epA_le
        have hok_R : (configRefuseEarlyBobCorr decT encT).corrOK stR.1 y_corr = false :=
          corrOK_eq_false_of_epoch_A_lt_10 decT encT stR.1 y_corr (by omega)
        have hok_RA : (configRefuseEarlyBobCorr decT encT).corrOK stR.1 .A = false :=
          corrOK_eq_false_of_epoch_A_lt_10 decT encT stR.1 .A (by omega)
        have hst1L : st1L =
            patchGamePartyIdx 1 (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx stR.1 :=
            hrel.st1_eq
        have hok_L : (configRefuseEarlyBobCorr decT encT).corrOK st1L y_corr = false := by rw [hst1L]; exact hok_R
        have hok_LA : (configRefuseEarlyBobCorr decT encT).corrOK st1L .A = false := by rw [hst1L]; exact hok_RA
        have hbad_corr : badSpkCorrA decT encT st1L y_corr = false := by simp [badSpkCorrA, hok_LA]
        rw [corrSpkRef_run_of_badSpkCorrA_false decT encT y_corr st1L LL badL hbad_corr,
            liftSpkRef_run, runHop2_hop2Lift']; unfold SM.corrR
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hok_L, hok_R, Bool.not_false,
            Bool.or_true, ↓reduceIte, StateT.run_pure, Prod.mk.eta]
        exact (ih none (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 none)
          (st1L, LL, badL) stR hrel (Or.inr hcore)).trans (add_le_add le_rfl hle)

/-! ## Top-level `spkLeakRed` to `hop2PrgRedK` bridge -/

def hop2InitState0 {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (b :
    Bool) (ck0 x alice pqr prk : BitVec 256) : Hop2State Pt ℓ :=
  let ck1 := (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).2
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
  (initSt, aux0)
theorem sample_prod_bind_bv256 {γ : Type} (f : BitVec 256 × BitVec 256 → ProbComp γ) :
    (($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) >>= f) =
    (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun a => ($ᵗ BitVec 256 :
        ProbComp (BitVec 256)) >>= fun b => f (a, b)) := by
  have hsel : ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) =
      (Prod.mk <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256)) <*> ($ᵗ BitVec 256 :
          ProbComp (BitVec 256))) := rfl
  rw [hsel]; simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
      pure_bind]
omit [SampleableType Pt] in
theorem simulateQ_prfOracleImpl_spkLeakRed_eq {ℓ : ℕ} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔ Dh.dh s P_pt =
        Dh.dh s P') (key z : BitVec 256)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (v : Bool) :
        ((· == v) <$> (simulateQ (prfOracleImpl (extractPRF P.C.F encPt))
    (spkLeakRed P Dh encPt encT decT qep z A)).run' ⟨key, true, tableFor Dh z []⟩) =
    (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      runSpkTab P Dh encT decT qep s A
        (patchGameSpk P.C z ck0 (initGameSpkRef P ℓ b s prk alice pqr))
        [(Dh.dh alice Dh.base, prk)]
        (fun b' fin => (b == b' || fin.win) == v)) := by
  rw [StateT.run'_eq]; unfold spkLeakRed
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  rw [simulateQ_prfOracleImpl_liftM_bind]
  refine bind_congr fun b => ?_
  rw [simulateQ_prfOracleImpl_liftM_bind]
  refine bind_congr fun ck0 => ?_
  rw [simulateQ_prfOracleImpl_liftM_bind, sample_prod_bind_bv256]
  refine bind_congr fun alice => bind_congr fun pqr => ?_
  rw [initAOracle_true_tableFor_bind (extractPRF P.C.F encPt) P Dh s hker key ck0 z alice pqr []]
  have hstep0 : stepTableFor Dh s (Dh.dh alice Dh.base) [] = (($ᵗ BitVec 256 :
      ProbComp (BitVec 256)) >>= fun prk => pure (prk, [(Dh.dh alice Dh.base, prk)])) := rfl
  rw [hstep0]; simp only [bind_assoc, pure_bind]
  refine bind_congr fun prk => ?_
  rw [simulateQ_prfOracleImpl_spkOracleImpl_bind (extractPRF P.C.F encPt) P Dh encT decT qep s hker
      key z A _ [(Dh.dh alice Dh.base, prk)]]
  unfold runSpkTab; rw [← initGameSpk_eq_patchGameSpk P ℓ b s prk ck0 z alice pqr]; rfl
omit [SampleableType Pt] in
theorem evalDist_branch_true_spkLeakRed_eq {ℓ : ℕ} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey →
    Option Pt)
    (qep : ℕ) (s : BitVec 256) (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt =
        Dh.dh x P' ↔ Dh.dh s P_pt = Dh.dh s P')
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (v : Bool) :
    𝒟[(· == v) <$> (extractPRF P.C.F encPt).branch true (spkLeakRed P Dh encPt encT decT qep s A)]
        {true} =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      runSpkTab P Dh encT decT qep s A
        (patchGameSpk P.C s ck0 (initGameSpkRef P ℓ b s prk alice pqr))
        [(Dh.dh alice Dh.base, prk)]
        (fun b' fin => (b == b' || fin.win) == v)] {true} := by
  have h1 :
      ((· == v) <$> (extractPRF P.C.F encPt).branch true (spkLeakRed P Dh encPt encT decT qep s A))
      = (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun key =>
        (· == v) <$> (simulateQ (prfOracleImpl (extractPRF P.C.F encPt))
          (spkLeakRed P Dh encPt encT decT qep s A)).run' ⟨key, true, tableFor Dh s []⟩) := by
    unfold MACScheme.branch; simp only [map_eq_bind_pure_comp, bind_assoc]; rfl
  rw [h1]; simp only [simulateQ_prfOracleImpl_spkLeakRed_eq P Dh encPt encT decT qep s hker _ s A v,
      OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ Bool) _ _ fun b => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun pqr => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
omit [SampleableType Pt] in
theorem evalDist_branch_true_spkLeakRedU_eq {ℓ : ℕ} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey →
    Option Pt)
    (qep : ℕ) (s : BitVec 256) (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt =
        Dh.dh x P' ↔ Dh.dh s P_pt = Dh.dh s P')
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (v : Bool) :
        𝒟[(· == v) <$> (extractPRF P.C.F encPt).branch true
    (spkLeakRedU spkLeakRed P Dh encPt encT decT qep A)] {true} =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      runSpkTab P Dh encT decT qep s A
        (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
        [(Dh.dh alice Dh.base, prk)]
        (fun b' fin => (b == b' || fin.win) == v)] {true} := by
  have h1 :
      ((· == v) <$> (extractPRF P.C.F encPt).branch true (spkLeakRedU spkLeakRed P Dh encPt encT
      decT qep A)) = (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun key =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
          (· == v) <$> (simulateQ (prfOracleImpl (extractPRF P.C.F encPt))
            (spkLeakRed P Dh encPt encT decT qep x A)).run' ⟨key, true, tableFor Dh x []⟩) := by
    change ((· == v) <$> (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun key =>
        (simulateQ (prfOracleImpl (extractPRF P.C.F encPt))
          ((liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun x =>
            spkLeakRed P Dh encPt encT decT qep x A)).run' ⟨key, true, []⟩)) = _
    simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
        Function.comp_apply, bind_assoc, pure_bind]
    refine bind_congr fun key => ?_
    exact simulateQ_prfOracleImpl_liftM_bind (extractPRF P.C.F encPt) ($ᵗ BitVec 256) ⟨key, true,
        []⟩ _
  rw [h1]; simp only [simulateQ_prfOracleImpl_spkLeakRed_eq P Dh encPt encT decT qep s hker _ _ A v,
      OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ Bool)]
  refine bind_evalDist_true_eq ($ᵗ Bool) _ _ fun b => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  have hswap_ck0 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 => ($ᵗ BitVec 256 :
      ProbComp (BitVec 256)) >>= fun x =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun prk =>
        runSpkTab P Dh encT decT qep s A
          (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
          [(Dh.dh alice Dh.base, prk)]
          (fun b' fin => (b == b' || fin.win) == v)] {true} =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun prk =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkTab P Dh encT decT qep s A
          (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
          [(Dh.dh alice Dh.base, prk)]
          (fun b' fin => (b == b' || fin.win) == v)] {true} := by
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun ck0 => ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun pqr => ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  rw [hswap_ck0]; rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun pqr => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
omit [SampleableType Pt] in
theorem evalDist_prgRealExperiment_hop2PrgRedK_zero_eq {ℓ : ℕ} (P : Params Bytes PQC) (Dh :
    DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (A :
        SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    𝒟[(Ratchet.expandPRG P.C.F).prgRealExperiment (hop2PrgRedK P ℓ Dh encPt encT decT qep s 0 A)]
        {true} =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
        (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} := by
  have hunf :
      (Ratchet.expandPRG P.C.F).prgRealExperiment (hop2PrgRedK P ℓ Dh encPt encT decT qep s 0 A) =
      (do
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let _u1 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk) []) := by
    unfold PRGScheme.prgRealExperiment hop2PrgRedK
    refine bind_congr fun prk => ?_
    change simulateQ (pureStepImpl _) (hop2Game P ℓ Dh encT decT qep s (pureStepHyb 0 _ _) A) = _
    unfold hop2Game; rw [simulateQ_bind, simulateQ_pureStepImpl_liftM]
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
    rw [simulateQ_bind]; simp only [simulateQ_pure]; exact simulateQ_prfReal_hop2Impl_eq_runHop2 P
        Dh encT decT qep s 0 _ _ A _
  rw [hunf]
  have hdrop :
      𝒟[do
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let _u1 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} =
      𝒟[do
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} := by
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun prk => ?_
    refine bind_evalDist_true_eq ($ᵗ Bool) _ _ fun b => ?_
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun ck0 => ?_
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun x => ?_
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun pqr => ?_
    rw [OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
  rw [hdrop, OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ Bool)]
  refine bind_evalDist_true_eq ($ᵗ Bool) _ _ fun b => ?_
  have hinner : ∀ prk, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 => ($ᵗ BitVec 256 :
      ProbComp (BitVec 256)) >>= fun x =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} := by
    intro prk
    have h1 : ∀ ck0, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => ($ᵗ BitVec 256 :
        ProbComp (BitVec 256)) >>= fun alice =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
            (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} =
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
            (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} := by
      intro ck0
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
      refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
    refine (bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ h1).trans ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine (bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ hinner).trans ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
theorem evalDist_spkLeakRed_apply_le_hop2PrgRedK_zero {ℓ : ℕ} (P : Params Bytes PQC) (hcodec :
    P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey →
        Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T) (hz : ∀ x,
        Dh.dh x 0 = 0) (qep q : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔ Dh.dh s P_pt =
        Dh.dh s P') (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
    (hq : SM.MakesAtMostQueries A q) (v : Bool) :
        𝒟[(extractPRF P.C.F encPt).branch true (spkLeakRed P Dh encPt encT decT qep s A)] {v} ≤
    𝒟[(extractPRF P.C.F encPt).branch true (spkLeakRedU spkLeakRed P Dh encPt encT decT qep A)] {v}
        + (epoch0ChainForgeryTerm P.C.F q + spkSwapHiddenScalarGuessTerm Dh q +
    𝒟[(Ratchet.expandPRG P.C.F).prgRealExperiment (hop2PrgRedK P ℓ Dh encPt encT decT qep s 0 A)]
        {true}) := by
  rw [evalDist_apply_eq_beq _ v, evalDist_apply_eq_beq _ v,
      evalDist_branch_true_spkLeakRed_eq P Dh encPt encT decT qep s hker A v,
      evalDist_branch_true_spkLeakRedU_eq P Dh encPt encT decT qep s hker A v,
      evalDist_prgRealExperiment_hop2PrgRedK_zero_eq P Dh encPt encT decT qep s A]
  suffices hmain :
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runSpkTab P Dh encT decT qep s A
          (patchGameSpk P.C s ck0 (initGameSpkRef P ℓ b s prk alice pqr))
          [(Dh.dh alice Dh.base, prk)]
          (fun b' fin => (b == b' || fin.win) == v)] {true} ≤
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runSpkTab P Dh encT decT qep s A
          (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
          [(Dh.dh alice Dh.base, prk)]
          (fun b' fin => (b == b' || fin.win) == v)] {true} +
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} +
      (epoch0ChainForgeryTerm P.C.F q + spkSwapHiddenScalarGuessTerm Dh q) by
    exact hmain.trans (le_of_eq (by ac_rfl))
  refine bind_evalDist_true_le_add_two_of_support ($ᵗ Bool) _ _ _ _ fun b _ => ?_
  refine bind_evalDist_true_le_add_two_of_support ($ᵗ BitVec 256) _ _ _ _ fun alice _ => ?_
  refine bind_evalDist_true_le_add_two_of_support ($ᵗ BitVec 256) _ _ _ _ fun pqr _ => ?_
  refine bind_evalDist_true_le_add_two_of_support ($ᵗ BitVec 256) _ _ _ _ fun prk _ => ?_
  have h1 := evalDist_runSpkTab_s_le_runSpkRef P Dh encT decT qep s A q hq
    (initGameSpkRef P ℓ b s prk alice pqr) [(Dh.dh alice Dh.base, prk)] false
    (spkRefInv_initGameSpkRef P ℓ b s prk alice pqr) hcodec
    ⟨hcodec ▸ signalRoundTripShort_proto, hL, hcodec ▸ signalEncodeFits32_proto⟩
    (by intro r hr; simp [initGameSpkRef] at hr)
    (fun b' fin => (b == b' || fin.win) == v)
    (fun _ _ _ => rfl)
  have href_le :
      𝒟[runSpkRef P Dh encT decT qep s A (initGameSpkRef P ℓ b s prk alice pqr) [(Dh.dh alice
      Dh.base, prk)] false (fun b' fin => (b == b' || fin.win) == v)] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkTab P Dh encT decT qep s A
          (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
          [(Dh.dh alice Dh.base, prk)]
          (fun b' fin => (b == b' || fin.win) == v)] {true} +
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} +
      spkSwapHiddenScalarGuessTerm Dh q := by
    rw [← OracleComp.evalDist_bind_const ($ᵗ BitVec 256) (runSpkRef P Dh encT decT qep s A
        (initGameSpkRef P ℓ b s prk alice pqr) [(Dh.dh alice Dh.base,
        prk)] false (fun b' fin => (b == b' || fin.win) == v))]
    refine bind_evalDist_true_le_add_two_of_support ($ᵗ BitVec 256) _ _ _ _ fun ck0 _ => ?_
    have h2 := evalDist_runSpkRef_le_runSpkTab_x_add_bad P Dh encPt encT decT hX hdec qep s ck0
      A q hq (initGameSpkRef P ℓ b s prk alice pqr) [(Dh.dh alice Dh.base, prk)] false
      (spkRefInv_initGameSpkRef P ℓ b s prk alice pqr)
      (fun b' fin => (b == b' || fin.win) == v)
      (fun _ _ _ => rfl)
    have h3 : 𝒟[($ᵗ BitVec 256 :
        ProbComp (BitVec 256)) >>= fun x => runSpkBad P Dh encT decT qep s A (patchGameSpk P.C x ck0
        (initGameSpkRef P ℓ b s prk alice pqr))
            [(Dh.dh alice Dh.base, prk)] false] {true} ≤
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
          runHop2 P Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
            (hop2InitState0 P Dh b ck0 x alice pqr prk) []] {true} +
        ((5 * q : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
      refine bind_evalDist_true_le_add_of_support_window ($ᵗ BitVec 256) _ _ _ fun x _ => ?_
      exact evalDist_runSpkBad_le_runHop2_zero hcodec hL hX hdec hz qep s x prk hker (Dh.dh alice
          Dh.base) A q hq (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr),
          [(Dh.dh alice Dh.base, prk)], false)
        _ (hop2Init3Rel_init P Dh decT encT s x prk ck0 alice pqr b hker)
        (hop2WindowInv_init P b 0 ck0 x alice pqr
          (Ratchet.rootExpand P.C.F (keyToBytes32 prk)).2)
    have hguess : ((5 * q : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh + (q : ℝ≥0∞) * hop2GuessUnit Dh =
        spkSwapHiddenScalarGuessTerm Dh q := by
      rw [hop2GuessTerm_eq_mul_unit, ← add_mul]; congr 1
      exact_mod_cast (by omega : 5 * q + q = 6 * q)
    refine h2.trans ?_
    calc _ ≤ _ + (_ + ((5 * q : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh) + (q : ℝ≥0∞) * hop2GuessUnit Dh :=
        add_le_add (add_le_add le_rfl h3) le_rfl
      _ = _ := by rw [add_assoc, add_assoc, hguess]; ac_rfl
  rw [spkForgeTerm_eq_mul_eps0IdealUnit]
  exact h1.trans (by
    calc _ ≤ (_ + _ + spkSwapHiddenScalarGuessTerm Dh q) + (q : ℝ≥0∞) * eps0IdealUnit P.C.F :=
        add_le_add href_le le_rfl
      _ = _ := by ac_rfl)
end HInitBridge
end CryptoVerification.E2E.SpkHop1
