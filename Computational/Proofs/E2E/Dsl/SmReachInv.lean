/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.SmReachInvParty
public import Computational.Proofs.ReductionDsl.SM.GameCosted
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers

/-!
# Model-Game `SM.GameState` Reachability Invariant

Lifts `PartyReachInv` to `SM.GameState` (`GameReachInv`, `SmReachBounded`) and driver states
(`DrvSmReachInv`), proving initialization and preservation across `SM.oracleImplR` and E2E local
session steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.SmReachInv

open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (Pos Record GameState ConfigR initState transmitImpl
  challImpl transmitR challR deliverR injectR corrR oracleImplR)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState
  maxReceiverChains maxMessageKeys)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (TopStateTight)
open CryptoVerification.E2E (Bytes SampledSessionKey RecordExtras BHE2EDrvState
  paramsIdsWithSpqr sessionSchemeFixedSpk sessionSchemeU bhE2EMirror bhE2EFinishStartSpk
  bhE2EStepLocalSm bhShallowStepStartU compositionLocalStart)
open CryptoVerification.E2E.Costed (e2eRecordExtras)
open Computational.Proofs.E2E.Dsl.ClampsLossless (ReachableSessionRecordBounds)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv partyReachInv_initA
  partyReachInv_initB partyReachInv_fixedSpk_initA partyReachInv_fixedSpk_initB
  partyReachInv_fixedSpk_send partyReachInv_fixedSpk_receive)

/-! ## Deduplicated `comp` list -/

/-- Deduplicates a compromised-position list while keeping the last occurrence of each `Pos`. -/
def dedupComp : List Pos → List Pos
  | [] => []
  | p :: ps =>
    let d := dedupComp ps
    if d.contains p then d else p :: d

@[simp] theorem dedupComp_nil : dedupComp [] = [] := rfl

@[simp] theorem mem_dedupComp (xs : List Pos) (q : Pos) :
    q ∈ dedupComp xs ↔ q ∈ xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons p ps ih =>
    dsimp only [dedupComp]
    simp only [List.contains_eq_mem, ih p, List.mem_cons]
    by_cases hp : p ∈ ps
    · simp only [hp, decide_true, ↓reduceIte, ih q]
      exact ⟨Or.inr, fun h => h.elim (fun hqp => hqp ▸ hp) id⟩
    · simp [hp, ih q]

@[simp] theorem dedupComp_contains (xs : List Pos) (q : Pos) :
    (dedupComp xs).contains q = xs.contains q := by
  simp [List.contains_eq_mem]

theorem dedupComp_filter (xs : List Pos) (q : Pos) :
    dedupComp (xs.filter (· != q)) = (dedupComp xs).filter (· != q) := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.filter_cons]
    by_cases hpq : (p != q) = true
    · simp only [hpq, ↓reduceIte]
      dsimp only [dedupComp]
      rw [ih]
      simp only [List.contains_eq_mem, List.mem_filter, mem_dedupComp]
      by_cases hp : p ∈ ps
      · simp [hp, hpq]
      · simp [hp, hpq]
    · simp only [hpq, Bool.false_eq_true, ↓reduceIte, ih]
      dsimp only [dedupComp]
      simp only [List.contains_eq_mem, mem_dedupComp]
      by_cases hp : p ∈ ps
      · simp [hp]
      · simp [hp, hpq]

theorem dedupComp_append_of_subset (xs ys : List Pos)
    (hsub : ∀ x ∈ xs, ys.contains x = true) :
    dedupComp (xs ++ ys) = dedupComp ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : ys.contains x = true := hsub x List.mem_cons_self
    have hxs : ∀ y ∈ xs, ys.contains y = true :=
      fun y hy => hsub y (List.mem_cons_of_mem x hy)
    simp only [List.cons_append]
    dsimp only [dedupComp]
    rw [ih hxs, dedupComp_contains, hx]
    rfl

theorem dedupComp_length_cons_le (p : Pos) (ps : List Pos) :
    (dedupComp (p :: ps)).length ≤ (dedupComp ps).length + 1 := by
  dsimp only [dedupComp]
  cases h : (dedupComp ps).contains p <;> simp

theorem dedupComp_afterCorr_eq {St Msg C : Type} (s : GameState St Msg C) (P : Party)
    (hallow : s.corrAllowed P = true) :
    dedupComp (s.afterCorr P).comp = dedupComp s.comp := by
  simp only [GameState.afterCorr, GameState.leak]
  refine dedupComp_append_of_subset _ s.comp ?_
  intro x hx
  rcases List.mem_map.mp hx with ⟨r, hrMem, rfl⟩
  rcases List.mem_filter.mp hrMem with ⟨hrTrans, hrSender⟩
  unfold GameState.corrAllowed at hallow
  rcases Bool.and_eq_true_iff.mp hallow with ⟨_, hnoUncomp⟩
  cases hcont : s.comp.contains r.pos
  · exfalso
    have hany : (s.trans.any fun r' => r'.pos.sender == P.other && !s.comp.contains r'.pos) =
        true := by
      refine List.any_eq_true.mpr ⟨r, hrTrans, ?_⟩
      rw [Bool.and_eq_true_iff]
      exact ⟨hrSender, by rw [hcont]; rfl⟩
    rw [hany] at hnoUncomp
    cases hnoUncomp
  · rfl

/-! ## `GameReachInv` and `SmReachBounded` -/

/-- Asserts `PartyReachInv C K` for both parties of `gs`. -/
structure GameReachInv (C : Crypto) (K : MlKem) {ℓ : ℕ}
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) : Prop where
  alice : PartyReachInv C K (gs.st .A)
  bob : PartyReachInv C K (gs.st .B)

theorem GameReachInv.party {C : Crypto} {K : MlKem} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : GameReachInv C K gs) (p : Party) : PartyReachInv C K (gs.st p) := by
  cases p
  · exact h.alice
  · exact h.bob

theorem GameReachInv.topTight {C : Crypto} {K : MlKem} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : GameReachInv C K gs) (p : Party) :
    TopStateTight C.F K (gs.st p).session.pqRatchetState :=
  (h.party p).topTight

theorem GameReachInv.receiverChains_le {C : Crypto} {K : MlKem} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : GameReachInv C K gs) (p : Party) :
    (gs.st p).session.receiverChains.length ≤ maxReceiverChains :=
  (h.party p).receiverChains_le

theorem GameReachInv.messageKeys_le {C : Crypto} {K : MlKem} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : GameReachInv C K gs) (p : Party) :
    ∀ rc ∈ (gs.st p).session.receiverChains, rc.messageKeys.length ≤ maxMessageKeys :=
  (h.party p).messageKeys_le

theorem GameReachInv.messageKeySeed_eq {C : Crypto} {K : MlKem} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : GameReachInv C K gs) (p : Party) :
    ∀ rc ∈ (gs.st p).session.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length = 32 :=
  (h.party p).messageKeySeed_eq

theorem GameReachInv.reachableSessionRecordBounds {C : Crypto} {K : MlKem} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : GameReachInv C K gs) (p : Party) (E : Party → RecordExtras)
    (hab : (E (gs.st p).party).aliceBaseKey.length ≤ 33)
    (hkyb : ∀ k ∈ (E (gs.st p).party).kyber, k.ciphertext.length ≤ 1569) :
    ReachableSessionRecordBounds E (gs.st p) :=
  (h.party p).reachableSessionRecordBounds E hab hkyb

theorem GameReachInv.reachableSessionRecordBounds_e2e {C : Crypto} {K : MlKem} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : GameReachInv C K gs) (p : Party)
    (regIdA regIdB bobRemoteRegId : BitVec 32) (hdr : SignalPqxdh.HandshakeHdr) :
    ReachableSessionRecordBounds (e2eRecordExtras regIdA regIdB bobRemoteRegId hdr) (gs.st p) :=
  (h.party p).reachableSessionRecordBounds_e2e regIdA regIdB bobRemoteRegId hdr

/-- Query-indexed length bounds on the history lists of `SM.GameState`. -/
structure SmListBounded (q : ℕ) {ℓ : ℕ}
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) : Prop where
  trans_le : gs.trans.length ≤ q
  chall_le : gs.chall.length ≤ q
  dedupComp_le : (dedupComp gs.comp).length ≤ q
  comp_le : gs.comp.length ≤ q * q
  leaks_le : gs.leaks.length ≤ q
  corrs_le : gs.corrs.length ≤ q

theorem SmListBounded.mono {q q' : ℕ} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmListBounded q gs) (hle : q ≤ q') : SmListBounded q' gs where
  trans_le := h.trans_le.trans hle
  chall_le := h.chall_le.trans hle
  dedupComp_le := h.dedupComp_le.trans hle
  comp_le := h.comp_le.trans (Nat.mul_le_mul hle hle)
  leaks_le := h.leaks_le.trans hle
  corrs_le := h.corrs_le.trans hle

theorem SmListBounded.setWin {q : ℕ} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmListBounded q gs) (w : Bool) :
    SmListBounded q { gs with win := w } where
  trans_le := h.trans_le
  chall_le := h.chall_le
  dedupComp_le := h.dedupComp_le
  comp_le := h.comp_le
  leaks_le := h.leaks_le
  corrs_le := h.corrs_le

/-- Combined party-state and history-length reachability invariant after at most `q` SM queries. -/
structure SmReachBounded (C : Crypto) (K : MlKem) (q : ℕ) {ℓ : ℕ}
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) : Prop where
  reach : GameReachInv C K gs
  lists : SmListBounded q gs

theorem SmReachBounded.mono {C : Crypto} {K : MlKem} {q q' : ℕ} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K q gs) (hle : q ≤ q') : SmReachBounded C K q' gs :=
  ⟨h.reach, h.lists.mono hle⟩

/-! ## `SM.oracleImplR` preservation -/

private theorem gameReachInv_update {C : Crypto} {K : MlKem}
    {st : Party → GhostState Bytes} (ha : PartyReachInv C K (st .A))
    (hb : PartyReachInv C K (st .B)) (p : Party) {g' : GhostState Bytes}
    (hg' : PartyReachInv C K g') :
    PartyReachInv C K (Function.update st p g' .A) ∧
      PartyReachInv C K (Function.update st p g' .B) := by
  cases p <;> simp [Function.update, ha, hb, hg']

theorem gameReachInv_initState (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ : ℕ) (s : BitVec 256) (k : SampledSessionKey) (b : Bool) :
    GameReachInv C K
      (initState
        (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          ℓ s).sendPart k b) :=
  ⟨partyReachInv_fixedSpk_initA C K idA idB ℓ s k,
   partyReachInv_fixedSpk_initB C K idA idB ℓ s k⟩

theorem gameReachInv_initState_u (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ : ℕ) (kU : CryptoVerification.E2E.KeyU) (b : Bool) :
    GameReachInv C K
      (initState
        (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          ℓ).sendPart kU b) :=
  ⟨partyReachInv_initA C K rfl _, partyReachInv_initB C K rfl _⟩

theorem smReachBounded_initState (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ : ℕ) (s : BitVec 256) (k : SampledSessionKey) (b : Bool) :
    SmReachBounded C K 0
      (initState
        (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          ℓ s).sendPart k b) :=
  ⟨gameReachInv_initState C K idA idB ℓ s k b,
   ⟨Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0⟩⟩

private theorem epMgmt_preserves {C : Crypto} {K : MlKem} {q Δ qep : ℕ} {ℓ : ℕ}
    {gs s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes} {P : Party} {bad : Bool}
    (hreach : GameReachInv C K gs) (hlist : SmListBounded q gs)
    (hep : gs.epMgmt Δ qep P bad = some s1) :
    GameReachInv C K s1 ∧
      s1.trans = gs.trans ∧ s1.chall = gs.chall ∧ s1.comp = gs.comp ∧
      s1.leaks.length ≤ q + 1 ∧ s1.corrs = gs.corrs := by
  unfold GameState.epMgmt at hep
  by_cases hsends : P.sendsIn (gs.epoch P + 1) = true
  · simp only [hsends, ↓reduceIte] at hep
    by_cases hq1 : qep < gs.epoch P + 1
    · simp only [hq1, ↓reduceIte] at hep
      cases hep
    · simp only [hq1, ↓reduceIte] at hep
      by_cases hbad : (bad && !gs.safeCh Δ P) = true
      · simp only [hbad, ↓reduceIte, Option.some.injEq] at hep
        subst hep
        refine ⟨⟨hreach.alice, hreach.bob⟩, rfl, rfl, rfl, ?_, rfl⟩
        simp only [GameState.leak, List.length_cons]
        exact Nat.succ_le_succ hlist.leaks_le
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hep
        subst hep
        exact ⟨⟨hreach.alice, hreach.bob⟩, rfl, rfl, rfl,
          hlist.leaks_le.trans (Nat.le_succ q), rfl⟩
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq2 : qep < gs.epoch P
    · simp only [hq2, ↓reduceIte] at hep
      cases hep
    · simp only [hq2, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨hreach, rfl, rfl, rfl, hlist.leaks_le.trans (Nat.le_succ q), rfl⟩

private theorem record_preserves {C : Crypto} {K : MlKem} {q Δ : ℕ} {ℓ : ℕ}
    {gs s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hlist : SmListBounded q gs)
    (htr1 : s1.trans = gs.trans) (hch1 : s1.chall = gs.chall) (hcp1 : s1.comp = gs.comp)
    (hlk1 : s1.leaks.length ≤ q + 1) (hcr1 : s1.corrs = gs.corrs)
    (P : Party) {st' : GhostState Bytes} (hst' : PartyReachInv C K st')
    (hs1 : GameReachInv C K s1) (rec_ : Record (Plain ℓ) Bytes) (isChall : Bool) :
    SmReachBounded C K (q + 1) (s1.record Δ P st' rec_ isChall) := by
  obtain ⟨ha', hb'⟩ := gameReachInv_update hs1.alice hs1.bob P hst'
  refine ⟨⟨ha', hb'⟩, ⟨?_, ?_, ?_, ?_, hlk1, ?_⟩⟩
  · simp only [GameState.record, List.length_cons, htr1]
    exact Nat.succ_le_succ hlist.trans_le
  · simp only [GameState.record, hch1]
    cases isChall
    · exact hlist.chall_le.trans (Nat.le_succ q)
    · exact Nat.succ_le_succ hlist.chall_le
  · simp only [GameState.record, hcp1]
    split_ifs
    · exact hlist.dedupComp_le.trans (Nat.le_succ q)
    · exact (dedupComp_length_cons_le rec_.pos gs.comp).trans
        (Nat.succ_le_succ hlist.dedupComp_le)
  · simp only [GameState.record, hcp1]
    have hmul : q * q + 1 ≤ (q + 1) * (q + 1) := by
      have : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by ring
      omega
    split_ifs
    · exact hlist.comp_le.trans (Nat.le_trans (Nat.le_succ _) hmul)
    · simp only [List.length_cons]
      exact (Nat.succ_le_succ hlist.comp_le).trans hmul
  · simp only [GameState.record, hcr1]
    exact hlist.corrs_le.trans (Nat.le_succ q)

private theorem accept_preserves {C : Crypto} {K : MlKem} {q : ℕ} {ℓ : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hreach : GameReachInv C K gs) (hlist : SmListBounded q gs)
    (P : Party) {st' : GhostState Bytes} (hst' : PartyReachInv C K st') (pos : Pos) :
    SmReachBounded C K (q + 1) (gs.accept P st' pos) := by
  obtain ⟨ha', hb'⟩ := gameReachInv_update hreach.alice hreach.bob P hst'
  refine ⟨⟨ha', hb'⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [GameState.accept, GameState.delete]
    exact List.length_filter_le _ _ |>.trans (hlist.trans_le.trans (Nat.le_succ q))
  · simp only [GameState.accept, GameState.delete]
    exact List.length_filter_le _ _ |>.trans (hlist.chall_le.trans (Nat.le_succ q))
  · simp only [GameState.accept, GameState.delete, dedupComp_filter]
    exact List.length_filter_le _ _ |>.trans (hlist.dedupComp_le.trans (Nat.le_succ q))
  · simp only [GameState.accept, GameState.delete]
    exact List.length_filter_le _ _ |>.trans
      (hlist.comp_le.trans (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q)))
  · exact hlist.leaks_le.trans (Nat.le_succ q)
  · exact hlist.corrs_le.trans (Nat.le_succ q)

theorem smReachBounded_transmitR (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ Δ qep q : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (arg : Party × Plain ℓ × Option (BitVec 512))
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K q gs)
    {out : Option Bytes × GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support
      ((transmitR
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
            ℓ s) Δ qep cfg arg).run gs)) :
    SmReachBounded C K (q + 1) out.2 := by
  rcases arg with ⟨P, m, optR⟩
  unfold transmitR transmitImpl at hout
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
  by_cases hok : !cfg.sendOK gs P
  · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact h.mono (Nat.le_succ q)
  · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hout
    by_cases hwin : gs.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact h.mono (Nat.le_succ q)
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
      rcases hout with ⟨⟨⟨coins, bad⟩, s0⟩, ⟨_, -, hpair⟩, hout⟩
      have hgs : s0 = gs := (Prod.mk.inj hpair).2
      subst s0
      dsimp only at hout
      cases hep : gs.epMgmt Δ qep P bad with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact h.mono (Nat.le_succ q)
      | some s1 =>
        simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hout
        subst hout
        obtain ⟨hs1, htr1, hch1, hcp1, hlk1, hcr1⟩ := epMgmt_preserves h.reach h.lists hep
        exact record_preserves h.lists htr1 hch1 hcp1 hlk1 hcr1 P
          (partyReachInv_fixedSpk_send C K idA idB ℓ s (hs1.party P) m coins) hs1 _ false

theorem smReachBounded_challR (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ Δ qep q : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (arg : Party × Plain ℓ × Plain ℓ × Option (BitVec 512))
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K q gs)
    {out : Option Bytes × GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support
      ((challR
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
            ℓ s) Δ qep cfg arg).run gs)) :
    SmReachBounded C K (q + 1) out.2 := by
  rcases arg with ⟨P, m0, m1, optR⟩
  unfold challR challImpl at hout
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
  by_cases hok : !cfg.sendOK gs P
  · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact h.mono (Nat.le_succ q)
  · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hout
    by_cases hwin : gs.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact h.mono (Nat.le_succ q)
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
      rcases hout with ⟨⟨⟨coins, bad⟩, s0⟩, ⟨_, -, hpair⟩, hout⟩
      have hgs : s0 = gs := (Prod.mk.inj hpair).2
      subst s0
      dsimp only at hout
      cases hep : gs.epMgmt Δ qep P bad with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact h.mono (Nat.le_succ q)
      | some s1 =>
        rw [hep] at hout
        dsimp only at hout
        by_cases hsafe : !s1.safeCh Δ P || !cfg.base.challAllowedIn (s1.epoch P)
        · simp only [hsafe, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hout
          subst hout
          exact h.mono (Nat.le_succ q)
        · simp only [hsafe, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          obtain ⟨hs1, htr1, hch1, hcp1, hlk1, hcr1⟩ := epMgmt_preserves h.reach h.lists hep
          exact record_preserves h.lists htr1 hch1 hcp1 hlk1 hcr1 P
            (partyReachInv_fixedSpk_send C K idA idB ℓ s (hs1.party P) _ coins) hs1 _ true

theorem smReachBounded_deliverR (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ q : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (arg : Party × Bytes)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K q gs)
    {out : Option (CryptoGames.SM.RecvResult (Plain ℓ)) ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support
      ((deliverR
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
            ℓ s) cfg arg).run gs)) :
    SmReachBounded C K (q + 1) out.2 := by
  rcases arg with ⟨P, c⟩
  unfold deliverR at hout
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
  by_cases hwin : gs.win
  · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact h.mono (Nat.le_succ q)
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hout
    cases htr : gs.inTransit P.other c with
    | none =>
      simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact h.mono (Nat.le_succ q)
    | some rec_ =>
      simp only [htr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
      rcases hout with ⟨⟨rc, s0⟩, ⟨_, -, hpair⟩, hout⟩
      have hgs : s0 = gs := (Prod.mk.inj hpair).2
      subst s0
      dsimp only at hout
      cases hrecv : (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ s).receive
          (gs.st P) c rc with
      | none =>
        rw [hrecv] at hout
        dsimp only at hout
        by_cases hmust : cfg.base.deliverWin && cfg.must gs P rec_
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact ⟨⟨h.reach.alice, h.reach.bob⟩, (h.lists.setWin true).mono (Nat.le_succ q)⟩
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact h.mono (Nat.le_succ q)
      | some quad =>
        rcases quad with ⟨st', t', i', m'⟩
        rw [hrecv] at hout
        dsimp only at hout
        have hst' : PartyReachInv C K st' :=
          partyReachInv_fixedSpk_receive C K idA idB ℓ s (h.reach.party P) hrecv
        have hacc : SmReachBounded C K (q + 1) (gs.accept P st' rec_.pos) :=
          accept_preserves h.reach h.lists P hst' rec_.pos
        by_cases hbad : cfg.base.deliverWin && cfg.must gs P rec_ &&
            !decide ((t', i', m') = (rec_.pos.epoch, rec_.pos.idx, rec_.msg))
        · simp only [hbad, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact ⟨⟨hacc.reach.alice, hacc.reach.bob⟩, hacc.lists.setWin true⟩
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact hacc

theorem smReachBounded_injectR (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ Δ qep q : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (arg : Party × Bytes)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K q gs)
    {out : Option (CryptoGames.SM.RecvResult (Plain ℓ)) ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support
      ((injectR
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
            ℓ s) Δ qep cfg arg).run gs)) :
    SmReachBounded C K (q + 1) out.2 := by
  rcases arg with ⟨P, c⟩
  unfold injectR at hout
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
  by_cases href : gs.win || (gs.inTransit P.other c).isSome || !gs.safeInj Δ || !cfg.injOK c
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact h.mono (Nat.le_succ q)
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨rc, s0⟩, ⟨_, -, hpair⟩, hout⟩
    have hgs : s0 = gs := (Prod.mk.inj hpair).2
    subst s0
    dsimp only at hout
    cases hrecv : (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ s).receive
        (gs.st P) c rc with
    | none =>
      rw [hrecv] at hout
      dsimp only at hout
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact h.mono (Nat.le_succ q)
    | some quad =>
      rcases quad with ⟨st', t', i', m'⟩
      rw [hrecv] at hout
      dsimp only at hout
      have hst' : PartyReachInv C K st' :=
        partyReachInv_fixedSpk_receive C K idA idB ℓ s (h.reach.party P) hrecv
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact h.mono (Nat.le_succ q)
      · simp only [hqep, ↓reduceIte] at hout
        by_cases htriv : gs.trivial Δ ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact accept_preserves h.reach h.lists P hst' ⟨P.other, t', i'⟩
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hout
          by_cases hfull : cfg.base.injectFull t'
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hout
            subst hout
            exact ⟨⟨h.reach.alice, h.reach.bob⟩, (h.lists.setWin true).mono (Nat.le_succ q)⟩
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hout
            subst hout
            exact h.mono (Nat.le_succ q)

theorem smReachBounded_corrR (C : Crypto) (K : MlKem) (ℓ q : ℕ)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (P : Party)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K q gs)
    {out : Option (GhostState Bytes) × GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support ((corrR cfg P).run gs)) :
    SmReachBounded C K (q + 1) out.2 := by
  unfold corrR at hout
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
  by_cases href : gs.win || !gs.corrAllowed P || (cfg.r1 && CryptoGames.SM.inWindow gs P) ||
      !cfg.corrOK gs P
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact h.mono (Nat.le_succ q)
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    have hallow : gs.corrAllowed P = true := by
      cases hc : gs.corrAllowed P
      · simp [hc] at href
      · rfl
    have hdedup : dedupComp (gs.afterCorr P).comp = dedupComp gs.comp :=
      dedupComp_afterCorr_eq gs P hallow
    refine ⟨⟨h.reach.alice, h.reach.bob⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact h.lists.trans_le.trans (Nat.le_succ q)
    · exact h.lists.chall_le.trans (Nat.le_succ q)
    · dsimp only
      rw [hdedup]
      exact h.lists.dedupComp_le.trans (Nat.le_succ q)
    · simp only [GameState.afterCorr, GameState.leak, List.length_append, List.length_map]
      have hflt : (gs.trans.filter fun r => r.pos.sender == P.other).length ≤ q :=
        (List.length_filter_le _ _).trans h.lists.trans_le
      have hcp := h.lists.comp_le
      have hsq : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by ring
      omega
    · simp only [GameState.afterCorr, GameState.leak, List.length_cons]
      exact Nat.succ_le_succ h.lists.leaks_le
    · simp only [GameState.afterCorr, GameState.leak, List.length_cons]
      exact Nat.succ_le_succ h.lists.corrs_le

/-- Every `SM.oracleImplR` query over `sessionSchemeFixedSpk` advances `SmReachBounded C K q` to
`q + 1`. -/
theorem smReachBounded_oracleImplR (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ Δ qep q : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (qry : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K q gs)
    {out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range qry ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support
      ((oracleImplR
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
            ℓ s) Δ qep cfg qry).run gs)) :
    SmReachBounded C K (q + 1) out.2 := by
  rcases qry with (((qTr | qCh) | qDl) | qIj) | qCr
  · exact smReachBounded_transmitR C K idA idB ℓ Δ qep q s cfg qTr h hout
  · exact smReachBounded_challR C K idA idB ℓ Δ qep q s cfg qCh h hout
  · exact smReachBounded_deliverR C K idA idB ℓ q s cfg qDl h hout
  · exact smReachBounded_injectR C K idA idB ℓ Δ qep q s cfg qIj h hout
  · exact smReachBounded_corrR C K ℓ q cfg qCr h hout

theorem gameReachInv_oracleImplR (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ Δ qep : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (qry : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : GameReachInv C K gs)
    {out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range qry ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support
      ((oracleImplR
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
            ℓ s) Δ qep cfg qry).run gs)) :
    GameReachInv C K out.2 := by
  let q0 := max gs.trans.length (max gs.chall.length
    (max gs.comp.length (max gs.leaks.length gs.corrs.length)))
  have hleTr : gs.trans.length ≤ q0 := Nat.le_max_left _ _
  have hleR1 : max gs.chall.length (max gs.comp.length (max gs.leaks.length gs.corrs.length)) ≤
      q0 := Nat.le_max_right _ _
  have hleCh : gs.chall.length ≤ q0 := (Nat.le_max_left _ _).trans hleR1
  have hleR2 : max gs.comp.length (max gs.leaks.length gs.corrs.length) ≤ q0 :=
    (Nat.le_max_right _ _).trans hleR1
  have hleCp : gs.comp.length ≤ q0 := (Nat.le_max_left _ _).trans hleR2
  have hleR3 : max gs.leaks.length gs.corrs.length ≤ q0 := (Nat.le_max_right _ _).trans hleR2
  have hleLk : gs.leaks.length ≤ q0 := (Nat.le_max_left _ _).trans hleR3
  have hleCr : gs.corrs.length ≤ q0 := (Nat.le_max_right _ _).trans hleR3
  have hdedupLe : ∀ xs : List Pos, (dedupComp xs).length ≤ xs.length := by
    intro xs
    induction xs with
    | nil => exact Nat.le_refl 0
    | cons p ps ih =>
      exact (dedupComp_length_cons_le p ps).trans (Nat.succ_le_succ ih)
  have hcpSq : gs.comp.length ≤ (q0 + 1) * (q0 + 1) := by
    have : q0 ≤ (q0 + 1) * (q0 + 1) := by
      have : (q0 + 1) * (q0 + 1) = q0 * q0 + 2 * q0 + 1 := by ring
      omega
    exact hleCp.trans this
  have hb0 : SmReachBounded C K (q0 + 1) gs :=
    ⟨h, ⟨hleTr.trans (Nat.le_succ q0), hleCh.trans (Nat.le_succ q0),
      (hdedupLe gs.comp).trans (hleCp.trans (Nat.le_succ q0)), hcpSq,
      hleLk.trans (Nat.le_succ q0), hleCr.trans (Nat.le_succ q0)⟩⟩
  exact (smReachBounded_oracleImplR C K idA idB ℓ Δ qep (q0 + 1) s cfg qry hb0 hout).reach

/-! ## Driver invariant `DrvSmReachInv` -/

/-- Asserts `GameReachInv C K` for every active local session in `σ`. -/
def DrvSmReachInv {S : SignalPqxdh.Setup} {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (σ : BHE2EDrvState S ℓ) : Prop :=
  ∀ d ∈ σ.insts, ∀ gs ∈ d.gs, GameReachInv C K gs

theorem drvSmReachInv_empty {S : SignalPqxdh.Setup} {ℓ : ℕ} (C : Crypto) (K : MlKem) :
    DrvSmReachInv C K ({} : BHE2EDrvState S ℓ) := by
  intro _ hd
  cases hd

theorem drvSmReachInv_mirror {S : SignalPqxdh.Setup} {ℓ : ℕ} {C : Crypto} {K : MlKem}
    {σ : BHE2EDrvState S ℓ} (h : DrvSmReachInv C K σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    DrvSmReachInv C K (bhE2EMirror σ kq kr) :=
  h

theorem drvSmReachInv_finishStartSpk {S : SignalPqxdh.Setup} {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (bMode? : Option Bool) {σ : BHE2EDrvState S ℓ} (h : DrvSmReachInv C K σ)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (aliceCoins : BitVec 256) :
    DrvSmReachInv C K (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 aliceCoins).2 := by
  unfold bhE2EFinishStartSpk
  split
  · split_ifs
    · intro d hd gs hgs
      rcases List.mem_append.mp hd with hd0 | hd1
      · exact h d hd0 gs hgs
      · simp only [List.mem_singleton] at hd1
        subst hd1
        rcases Option.mem_map.mp hgs with ⟨b, -, rfl⟩
        exact gameReachInv_initState C K _ _ ℓ _ _ b
    · exact h
  · exact h

theorem drvSmReachInv_compositionLocalStart {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {σ : BHE2EDrvState S ℓ} (h : DrvSmReachInv C K σ) (sid : SignalPqxdh.SessionId S)
    {out : Option ℕ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (compositionLocalStart ki C K bMode? σ sid)) :
    DrvSmReachInv C K out.2 := by
  unfold compositionLocalStart at hout
  split at hout
  · simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact h
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr1, st1⟩, -, ⟨kr2, st2⟩, -, ac, -, rfl⟩
    have h' : DrvSmReachInv C K { σ with st := st2 } := h
    exact drvSmReachInv_finishStartSpk C K bMode? h' sid kr1 kr2 ac

theorem drvSmReachInv_stepStartU {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem)
    {σ : BHE2EDrvState S ℓ} (h : DrvSmReachInv C K σ)
    (sid : SignalPqxdh.SessionId S) (kU : CryptoVerification.E2E.KeyU) :
    DrvSmReachInv C K (bhShallowStepStartU C K σ sid kU).2 := by
  dsimp only [bhShallowStepStartU]
  split
  · exact h
  · intro d hd gs hgs
    rcases List.mem_append.mp hd with hd0 | hd1
    · exact h d hd0 gs hgs
    · simp only [List.mem_singleton] at hd1
      subst hd1
      simp only [Option.mem_def, Option.some.injEq] at hgs
      subst hgs
      exact gameReachInv_initState_u C K _ _ ℓ kU σ.b

private theorem mem_set_iff_or {α : Type} :
    ∀ (l : List α) (i : ℕ) (x y : α), y ∈ l.set i x → y = x ∨ y ∈ l
  | [], _, _, _, hy => nomatch hy
  | _ :: as, 0, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ hmem)
  | a :: as, i + 1, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inr List.mem_cons_self
    · rcases mem_set_iff_or as i x y hmem with rfl | hmem'
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a hmem')

theorem drvSmReachInv_bhE2EStepLocalSm {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} (h : DrvSmReachInv C K σ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : CryptoVerification.E2E.BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    DrvSmReachInv C K out.2 := by
  unfold bhE2EStepLocalSm at hout
  by_cases hcl : !CryptoVerification.E2E.bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact h
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none =>
      simp only [hd, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact h
    | some d =>
      cases him : σ.instMeta[i]? with
      | none =>
        simp only [hd, him, support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact h
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted && CryptoVerification.E2E.bhIsBobRecvSMQuery sq &&
            CryptoVerification.E2E.bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact h
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none =>
            simp only [hgs, support_pure, Set.mem_singleton_iff] at hout
            subst hout
            exact h
          | some gs =>
            simp only [hgs] at hout
            have hdMem : d ∈ σ.insts := List.mem_of_getElem? hd
            have hgsInv : GameReachInv C K gs := h d hdMem gs hgs
            have hrunStd :
                ∀ (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ)
                    (BitVec 512) Bytes).Domain),
                out ∈ support (do
                  let (r, gs') ← (oracleImplR
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins) (2 + 1) qep
                    (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT) q').run gs
                  let accepted := CryptoVerification.E2E.bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true,
                                ikACorrAtAccept := CryptoVerification.E2E.bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  pure (CryptoVerification.E2E.bhPackSmResp q' r, σ1)) →
                DrvSmReachInv C K out.2 := by
              intro q' hrun
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrun
              rcases hrun with ⟨⟨r, gs'⟩, hstep, rfl⟩
              have hgs' : GameReachInv C K gs' :=
                gameReachInv_oracleImplR C K d.idA d.idB ℓ (2 + 1) qep d.spkCoins _ q' hgsInv hstep
              intro d' hd' gs0 hgs0
              rcases mem_set_iff_or σ.insts i { d with gs := some gs' } d' hd' with rfl | hmem
              · simp only [Option.mem_def, Option.some.injEq] at hgs0
                subst hgs0
                exact hgs'
              · exact h d' hmem gs0 hgs0
            have hpure : out ∈ support (pure ((none, none, none), σ) :
                ProbComp (CryptoVerification.E2E.BHE2ESmResp ℓ × BHE2EDrvState S ℓ)) →
                DrvSmReachInv C K out.2 := by
              simp only [support_pure, Set.mem_singleton_iff]
              intro heq; subst heq; exact h
            rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
            · dsimp only at hout
              exact hrunStd _ hout
            · dsimp only at hout
              exact hrunStd _ hout
            · cases pDl
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunStd _ hout
              · dsimp only at hout
                split_ifs at hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hpure hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hrunStd _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
            · cases pIj
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunStd _ hout
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cIj
                  · rw [hdec] at hout; dsimp only at hout; exact hrunStd _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
            · dsimp only at hout
              exact hrunStd _ hout

end Computational.Proofs.E2E.Dsl.SmReachInv
