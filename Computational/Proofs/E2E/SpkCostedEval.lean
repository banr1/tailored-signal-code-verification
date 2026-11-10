/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SpkHop2Red
public import Computational.Proofs.ReductionDsl.SpkLeakRedU
public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds

/-!
# Evaluation, Cost, and Query Bridges for E2E Signed-Pre-Key Reductions

Proves the reachable-state `GhostBounded` invariant for `sessionSchemeU`, `spkOracleImpl`, and
`hop2Impl`, and establishes the unconditional evaluation bridges `spkLeakRedProg_eval_of_le`,
`hop2PrfRedKProg_eval_of_le`, and `hop2PrgRedKProg_eval_of_le` together with their `GRedBounded`
bounds.
-/

@[expose] public section

namespace CryptoVerification.E2E.Costed

open ReductionDsl OracleComp OracleSpec CryptoGames CryptoGames.SM
open CryptoGames.PRF.Costed CryptoGames.PRG.Costed
open CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E
open Computational.Proofs.GameHop.CompDedup
  (canonComp canonComp_idem canonComp_safeCh canonComp_inTransit canonComp_safeInj
    canonComp_trivial canonComp_corrAllowed canonComp_inWindow canonComp_epMgmt
    canonComp_record canonComp_accept canonComp_setWin canonComp_afterCorr
    canonComp_afterCorrDedup map_run_simulateQ_eq_of_idem_proj afterCorrDedup corrRDedup)

set_option linter.unusedSectionVars false

/-! ## Reachable `GhostState` epoch bound -/

/-- A `GhostState` has `GhostBounded E` when its current epoch and all stored receiver-chain
epochs are at most `E`. -/
def GhostBounded (E : ℕ) (g : GhostState Bytes) : Prop :=
  g.epoch ≤ E ∧ ∀ e ∈ g.chainEpochs, e ≤ E

def StateGhostBounded {ℓ : ℕ} (E : ℕ)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) : Prop :=
  ∀ Q, GhostBounded E (st.st Q)

theorem GhostBounded.mono {E₁ E₂ : ℕ} {g : GhostState Bytes}
    (h : E₁ ≤ E₂) (hg : GhostBounded E₁ g) : GhostBounded E₂ g :=
  ⟨le_trans hg.1 h, fun e he => le_trans (hg.2 e he) h⟩

theorem StateGhostBounded.mono {ℓ E₁ E₂ : ℕ}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (h : E₁ ≤ E₂) (hst : StateGhostBounded E₁ st) : StateGhostBounded E₂ st :=
  fun Q => (hst Q).mono h

theorem getD_le_of_forall_mem {l : List ℕ} {E : ℕ}
    (hl : ∀ e ∈ l, e ≤ E) (i : ℕ) : l.getD i 0 ≤ E := by
  induction l generalizing i with
  | nil => simp [List.getD]
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
      exact hl hd List.mem_cons_self
    | succ j =>
      simp only [List.getD, List.getElem?_cons_succ]
      exact ih (fun e he => hl e (List.mem_cons_of_mem hd he)) j

theorem mem_drop_le_of_forall_mem {l : List ℕ} {E : ℕ}
    (hl : ∀ e ∈ l, e ≤ E) (n : ℕ) : ∀ e ∈ l.drop n, e ≤ E :=
  fun e he => hl e (List.mem_of_mem_drop he)

theorem bv32_toNat_succ_le (u : BitVec 32) : u.toNat + 1 ≤ 2 ^ 32 := by
  have h : u.toNat < 2 ^ 32 := u.isLt
  omega

theorem ghostBounded_e2eInitA {PQC : Type} (P : Params Bytes PQC)
    (args : BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256) :
    GhostBounded 0 (e2eInitA P args) := by
  refine ⟨le_rfl, ?_⟩
  intro e he
  simp only [e2eInitA, List.mem_singleton] at he
  omega

theorem ghostBounded_initB {PQC : Type} (P : Params Bytes PQC) (k : InitKeys) :
    GhostBounded 0 (P.initB k) := by
  refine ⟨le_rfl, ?_⟩
  intro e he
  simp [Params.initB] at he

theorem ghostBounded_initAOracle {Pt PQC : Type} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (ck0 s alice pqr : BitVec 256) :
    ∀ g ∈ support (initAOracle P Dh ck0 s alice pqr), GhostBounded 0 g := by
  intro g hg
  simp only [initAOracle, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hg
  obtain ⟨prk, -, rfl⟩ := hg
  refine ⟨le_rfl, ?_⟩
  intro e he
  simp only [List.mem_singleton] at he
  omega

theorem ghostBounded_send {PQC : Type} {ℓ E : ℕ} (P : Params Bytes PQC) (g : GhostState Bytes)
    (m : CBC.Plain ℓ) (r : PQC) (hg : GhostBounded E g) :
    GhostBounded (E + 1) ((sessionSchemeU P ℓ).send g m r).1 := by
  dsimp only [sessionSchemeU, Params.send]
  rcases SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m.toList r
      g.session with ⟨_ | msg, s_out⟩
  · exact hg.mono (Nat.le_succ E)
  · refine ⟨?_, fun e he => le_trans (hg.2 e he) (Nat.le_succ E)⟩
    dsimp only
    have h1 := hg.1
    split_ifs <;> omega

theorem ghostBounded_receive_sessionSchemeU {PQC : Type} {ℓ E : ℕ} (P : Params Bytes PQC)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (hg : GhostBounded E g)
    (hrec : (sessionSchemeU P ℓ).receive g c rc = some (st', t', i', m')) :
    GhostBounded (E + 1) st' ∧ t' ≤ E + 1 ∧ i' ≤ 2 ^ 32 := by
  simp only [sessionSchemeU, Option.map_eq_some_iff] at hrec
  obtain ⟨⟨st0, t0, i0, m0⟩, hprec, heq⟩ := hrec
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl, rfl⟩
  unfold Params.receive at hprec
  rcases htry : SignalMessage.tryFrom P.codec c with _ | msg
  · simp [htry] at hprec
  · rw [htry] at hprec
    dsimp only at hprec
    rcases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
        msg .whisper rc g.session with ⟨_ | m_raw, s_out⟩
    · simp [hdec] at hprec
    · rw [hdec] at hprec
      dsimp only at hprec
      have hi : msg.counter.toNat + 1 ≤ 2 ^ 32 := bv32_toNat_succ_le msg.counter
      rcases hidx : g.session.receiverChains.findIdx?
          (·.senderRatchetKey == msg.senderRatchetKey) with _ | idx
      · rw [hidx] at hprec
        simp only [Option.some.injEq, Prod.mk.injEq] at hprec
        rcases hprec with ⟨rfl, rfl, rfl, rfl⟩
        have h1 := hg.1
        have hmem : ∀ e ∈ g.chainEpochs ++ [g.epoch + 1], e ≤ E + 1 := by
          intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact le_trans (hg.2 e he) (Nat.le_succ E)
          · omega
        exact ⟨⟨by dsimp only; omega, mem_drop_le_of_forall_mem hmem _⟩, by omega, hi⟩
      · rw [hidx] at hprec
        simp only [Option.some.injEq, Prod.mk.injEq] at hprec
        rcases hprec with ⟨rfl, rfl, rfl, rfl⟩
        have h1 := hg.1
        have ht : g.chainEpochs.getD idx 0 ≤ E := getD_le_of_forall_mem hg.2 idx
        have hmem : ∀ e ∈ g.chainEpochs, e ≤ E + 1 :=
          fun e he => le_trans (hg.2 e he) (Nat.le_succ E)
        exact ⟨⟨by dsimp only; omega, mem_drop_le_of_forall_mem hmem _⟩, by omega, hi⟩

theorem ghostBounded_finishRecvB0 {PQC : Type} {ℓ E : ℕ} (P : Params Bytes PQC)
    (g : GhostState Bytes) (c : Bytes) (rc prk : BitVec 256)
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (hfin : finishRecvB0 P ℓ g c rc prk = some (st', t', i', m')) :
    GhostBounded (E + 1) st' ∧ t' ≤ 1 ∧ i' ≤ 2 ^ 32 := by
  unfold finishRecvB0 at hfin
  rcases htry : SignalMessage.tryFrom P.codec c with _ | msg
  · simp [htry] at hfin
  · rw [htry] at hfin
    dsimp only at hfin
    rcases hrc : rootCreateChain P.C ((expandPRG P.C.F).gen prk).1 msg.senderRatchetKey
        (KeyPair.generate P.C rc).privateKey with _ | ⟨rk2, ck2⟩
    · simp [hrc] at hfin
    · rw [hrc] at hfin
      dsimp only at hfin
      split at hfin
      · simp at hfin
      · simp only [Option.some.injEq, Prod.mk.injEq] at hfin
        rcases hfin with ⟨rfl, rfl, rfl, rfl⟩
        have hmem : ∀ e ∈ ([1] : List ℕ), e ≤ E + 1 := by
          intro e he; simp only [List.mem_singleton] at he; omega
        exact ⟨⟨by dsimp only; omega, mem_drop_le_of_forall_mem hmem _⟩, le_rfl,
          bv32_toNat_succ_le msg.counter⟩

theorem ghostBounded_finishHop2DH {PQC : Type} {ℓ E : ℕ} (P : Params Bytes PQC)
    (g : GhostState Bytes) (c : Bytes) (rc rk2 ckR ckS : BitVec 256)
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (hg : GhostBounded E g)
    (hfin : finishHop2DH P ℓ g c rc rk2 ckR ckS = some (st', t', i', m')) :
    GhostBounded (E + 1) st' ∧ t' ≤ E + 1 ∧ i' ≤ 2 ^ 32 := by
  unfold finishHop2DH at hfin
  rcases htry : SignalMessage.tryFrom P.codec c with _ | msg
  · simp [htry] at hfin
  · rw [htry] at hfin
    dsimp only at hfin
    rcases hsc : g.session.senderChain with _ | sc
    · simp [hsc] at hfin
    · rw [hsc] at hfin
      dsimp only at hfin
      split at hfin
      · simp at hfin
      · simp only [Option.some.injEq, Prod.mk.injEq] at hfin
        rcases hfin with ⟨rfl, rfl, rfl, rfl⟩
        have h1 := hg.1
        have hmem : ∀ e ∈ g.chainEpochs ++ [g.epoch + 1], e ≤ E + 1 := by
          intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact le_trans (hg.2 e he) (Nat.le_succ E)
          · omega
        exact ⟨⟨by dsimp only; omega, mem_drop_le_of_forall_mem hmem _⟩, by omega,
          bv32_toNat_succ_le msg.counter⟩

/-! ## `StateGhostBounded` preservation -/

theorem epMgmt_st_eq {St Msg C : Type} {Δ qep : ℕ} {P : Party} {bad : Bool}
    {s s₁ : SM.GameState (St := St) (Msg := Msg) (C := C)}
    (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.st = s.st := by
  unfold GameState.epMgmt at h
  by_cases hsends : P.sendsIn (s.epoch P + 1)
  · simp only [hsends, ↓reduceIte] at h
    by_cases hqep : qep < s.epoch P + 1
    · simp [hqep] at h
    · simp only [hqep, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases hbad : (bad && !s.safeCh Δ P) <;> simp [hbad, GameState.leak]
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hqep : qep < s.epoch P
    · simp [hqep] at h
    · simp only [hqep, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl

theorem StateGhostBounded.record {ℓ E₁ E₂ : ℕ} {Δ : ℕ} {P : Party} {isChall : Bool}
    {st' : GhostState Bytes} {r : SM.Record (CBC.Plain ℓ) Bytes}
    {s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hE : E₁ ≤ E₂) (hs : StateGhostBounded E₁ s) (hst' : GhostBounded E₂ st') :
    StateGhostBounded E₂ (s.record Δ P st' r isChall) := by
  intro Q
  simp only [GameState.record, Function.update]
  split_ifs with hQP
  · subst hQP; exact hst'
  · exact (hs Q).mono hE

theorem StateGhostBounded.accept {ℓ E₁ E₂ : ℕ} {P : Party}
    {st' : GhostState Bytes} {pos : SM.Pos}
    {s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hE : E₁ ≤ E₂) (hs : StateGhostBounded E₁ s) (hst' : GhostBounded E₂ st') :
    StateGhostBounded E₂ (s.accept P st' pos) := by
  intro Q
  simp only [GameState.accept, GameState.delete, Function.update]
  split_ifs with hQP
  · subst hQP; exact hst'
  · exact (hs Q).mono hE

theorem StateGhostBounded.transmitR {PQC : Type} [SampleableType PQC]
    {ℓ Δ qep : ℕ} (P : Params Bytes PQC)
    (cfgR : ConfigR (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (y : Party × CBC.Plain ℓ × Option PQC) {E : ℕ}
    {s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : StateGhostBounded E s) :
    ∀ r ∈ support ((SM.transmitR (sessionSchemeU P ℓ) Δ qep cfgR y).run s),
      StateGhostBounded (E + 1) r.2 := by
  rcases y with ⟨Q, msg, optR⟩
  intro r hr
  unfold SM.transmitR SM.transmitImpl at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hok : !(cfgR.sendOK s Q)
  · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hs.mono (Nat.le_succ E)
  · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hr
    by_cases hwin : s.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hs.mono (Nat.le_succ E)
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_run_monadLift_bind,
        mem_support_bind_iff] at hr
      obtain ⟨⟨coins, bad⟩, -, hr⟩ := hr
      rcases hep : s.epMgmt Δ qep Q bad with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hs.mono (Nat.le_succ E)
      · simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr
        have hs₁ : StateGhostBounded E s₁ := by
          intro Q'; rw [epMgmt_st_eq hep]; exact hs Q'
        exact hs₁.record (Nat.le_succ E) (ghostBounded_send P (s₁.st Q) msg coins (hs₁ Q))

theorem StateGhostBounded.challR {PQC : Type} [SampleableType PQC]
    {ℓ Δ qep : ℕ} (P : Params Bytes PQC)
    (cfgR : ConfigR (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (y : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC) {E : ℕ}
    {s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : StateGhostBounded E s) :
    ∀ r ∈ support ((SM.challR (sessionSchemeU P ℓ) Δ qep cfgR y).run s),
      StateGhostBounded (E + 1) r.2 := by
  rcases y with ⟨Q, m₀, m₁, optR⟩
  intro r hr
  unfold SM.challR SM.challImpl at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hok : !(cfgR.sendOK s Q)
  · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hs.mono (Nat.le_succ E)
  · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hr
    by_cases hwin : s.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hs.mono (Nat.le_succ E)
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_run_monadLift_bind,
        mem_support_bind_iff] at hr
      obtain ⟨⟨coins, bad⟩, -, hr⟩ := hr
      rcases hep : s.epMgmt Δ qep Q bad with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hs.mono (Nat.le_succ E)
      · simp only [hep] at hr
        by_cases hch : (!s₁.safeCh Δ Q || !cfgR.base.challAllowedIn (s₁.epoch Q))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hs.mono (Nat.le_succ E)
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          have hs₁ : StateGhostBounded E s₁ := by
            intro Q'; rw [epMgmt_st_eq hep]; exact hs Q'
          exact hs₁.record (Nat.le_succ E) (ghostBounded_send P (s₁.st Q) _ coins (hs₁ Q))

theorem StateGhostBounded.corrR {ℓ E : ℕ}
    (cfgR : ConfigR (GhostState Bytes) (CBC.Plain ℓ) Bytes) (Q : Party)
    {s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : StateGhostBounded E s) :
    ∀ r ∈ support ((SM.corrR cfgR Q).run s), StateGhostBounded (E + 1) r.2 := by
  intro r hr
  unfold SM.corrR at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split_ifs at hr
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hs.mono (Nat.le_succ E)
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr
    intro Q'
    exact (hs Q').mono (Nat.le_succ E)

theorem StateGhostBounded.corrRDedup {ℓ E : ℕ}
    (cfgR : ConfigR (GhostState Bytes) (CBC.Plain ℓ) Bytes) (Q : Party)
    {s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : StateGhostBounded E s) :
    ∀ r ∈ support ((Computational.Proofs.GameHop.CompDedup.corrRDedup cfgR Q).run s),
      StateGhostBounded (E + 1) r.2 := by
  intro r hr
  unfold Computational.Proofs.GameHop.CompDedup.corrRDedup at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split_ifs at hr
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hs.mono (Nat.le_succ E)
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr
    intro Q'
    exact (hs Q').mono (Nat.le_succ E)

section SpkStepPreservation

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
  (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (s : BitVec 256) (K B qep : ℕ)

omit [SampleableType PQC] in
theorem ghostBounded_receiveB0 {E : ℕ} (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (res : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ))
    (hres : res ∈ support (receiveB0 P ℓ Dh encT decT s g c rc)) :
    ∀ st' t' i' m', res = some (st', t', i', m') →
      GhostBounded (E + 1) st' ∧ t' ≤ 1 ∧ i' ≤ 2 ^ 32 := by
  intro st' t' i' m' hsome
  subst hsome
  unfold receiveB0 at hres
  rcases htry : SignalMessage.tryFrom P.codec c with _ | msg
  · simp [htry] at hres
  · rw [htry] at hres
    dsimp only at hres
    rcases hdec : decT msg.senderRatchetKey with _ | T
    · simp [hdec] at hres
    · rw [hdec] at hres
      dsimp only at hres
      split_ifs at hres with hbad
      · simp at hres
      · simp only [mem_support_bind_iff] at hres
        obtain ⟨prk, -, hfin⟩ := hres
        rcases hrc : rootCreateChain P.C ((expandPRG P.C.F).gen prk).1 msg.senderRatchetKey
            (KeyPair.generate P.C rc).privateKey with _ | ⟨rk2, ck2⟩
        · rw [hrc] at hfin; simp at hfin
        · rw [hrc] at hfin; dsimp only at hfin
          rcases htd : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
              msg .whisper rc _ with ⟨_ | m, s_out⟩
          · rw [htd] at hfin; simp at hfin
          · rw [htd] at hfin
            simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq,
              Prod.mk.injEq] at hfin
            rcases hfin with ⟨rfl, rfl, rfl, rfl⟩
            have hmem : ∀ e ∈ ([1] : List ℕ), e ≤ E + 1 := by
              intro e he; simp only [List.mem_singleton] at he; omega
            exact ⟨⟨by dsimp only; omega, mem_drop_le_of_forall_mem hmem _⟩, le_rfl,
              bv32_toNat_succ_le msg.counter⟩

theorem ghostBounded_receiveSpk {E : ℕ} (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (hg : GhostBounded E g)
    (res : Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ))
    (hres : res ∈ support (receiveSpk P ℓ Dh encT decT s g c rc)) :
    ∀ st' t' i' m', res = some (st', t', i', m') →
      GhostBounded (E + 1) st' ∧ t' ≤ E + 1 ∧ i' ≤ 2 ^ 32 := by
  intro st' t' i' m' hsome
  unfold receiveSpk at hres
  split_ifs at hres with hb0
  · obtain ⟨hg', ht, hi⟩ := ghostBounded_receiveB0 P ℓ Dh encT decT s g c rc res hres
      st' t' i' m' hsome
    exact ⟨hg', by omega, hi⟩
  · subst hsome
    simp only [support_pure, Set.mem_singleton_iff] at hres
    exact ghostBounded_receive_sessionSchemeU P g c rc st' t' i' m' hg hres.symm

theorem StateGhostBounded.deliverSpk {E : ℕ}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : StateGhostBounded E st) (Q : Party) (c : Bytes) :
    ∀ r ∈ support ((CryptoVerification.E2E.deliverSpk P ℓ Dh encT decT s (Q, c)).run st),
      StateGhostBounded (E + 1) r.2 := by
  intro r hr
  unfold CryptoVerification.E2E.deliverSpk at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split_ifs at hr with hwin
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hs.mono (Nat.le_succ E)
  · rcases htr : st.inTransit Q.other c with _ | rec_
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hs.mono (Nat.le_succ E)
    · simp only [htr, stateT_run_lift_bind, mem_support_bind_iff] at hr
      obtain ⟨rc, -, out, hout, hr⟩ := hr
      rcases out with _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hs.mono (Nat.le_succ E)
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨hst', -, -⟩ :=
          ghostBounded_receiveSpk P ℓ Dh encT decT s (st.st Q) c rc (hs Q)
            (some (st', t', i', m')) hout st' t' i' m' rfl
        exact hs.accept (Nat.le_succ E) hst'

theorem StateGhostBounded.injectSpk {E : ℕ}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : StateGhostBounded E st) (Q : Party) (c : Bytes) :
    ∀ r ∈ support ((CryptoVerification.E2E.injectSpk P ℓ Dh encT decT qep s (Q, c)).run st),
      StateGhostBounded (E + 1) r.2 := by
  intro r hr
  unfold CryptoVerification.E2E.injectSpk at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases href : (st.win || (st.inTransit Q.other c).isSome || !st.safeInj 3 ||
      !ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hs.mono (Nat.le_succ E)
  · simp only [href, Bool.false_eq_true, ↓reduceIte,
      stateT_run_lift_bind, mem_support_bind_iff] at hr
    obtain ⟨rc, -, out, hout, hr⟩ := hr
    rcases out with _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hs.mono (Nat.le_succ E)
    · dsimp only at hr
      split_ifs at hr with hqep ht
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hs.mono (Nat.le_succ E)
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨hst', -, -⟩ :=
          ghostBounded_receiveSpk P ℓ Dh encT decT s (st.st Q) c rc (hs Q)
            (some (st', t', i', m')) hout st' t' i' m' rfl
        exact hs.accept (Nat.le_succ E) hst'
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr
        intro Q'
        exact (hs Q').mono (Nat.le_succ E)

omit [SampleableType PQC] in
theorem ghostBounded_hop2DH {E : ℕ} (h : Hop2Hyb Pt)
    (t : ℕ) (coins : BitVec 256) (g : GhostState Bytes) (c : Bytes) (msg : SignalMessage)
    (rc : BitVec 256) (hg : GhostBounded E g) (_htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt)
    (r : Option ((GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × Option (Hop2Upd Pt)) ×
      (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt))
    (hr : r ∈ support ((hop2DH (ℓ := ℓ) P Dh encT decT h (some t) coins g msg rc).run st)) :
    r.2.1 = st.1 ∧
    ∀ st' t' i' m' uOpt, r.1 = some ((st', t', i', m'), uOpt) →
      GhostBounded (E + 1) st' ∧ t' ≤ E + 1 ∧ i' ≤ 2 ^ 32 := by
  unfold hop2DH at hr
  rcases hdec : decT msg.senderRatchetKey with _ | T
  · simp only [hdec, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact ⟨rfl, fun _ _ _ _ _ h => by cases h⟩
  · rw [hdec] at hr
    dsimp only at hr
    split_ifs at hr with hbad
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, fun _ _ _ _ _ h => by cases h⟩
    · rcases hsc : g.session.senderChain with _ | sc
      · simp only [hsc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, fun _ _ _ _ _ h => by cases h⟩
      · rw [hsc] at hr
        dsimp only at hr
        rw [StateT.run_bind, mem_support_bind_iff] at hr
        obtain ⟨⟨rhRes, s1⟩, hrh, hr⟩ := hr
        have hs1 : s1.1 = st.1 :=
          (hop2RecvHalf_support P ℓ h (some t) g.session.rootKey msg.senderRatchetKey
            sc.ratchetKey.privateKey (Dh.dh coins T) st (rhRes, s1) hrh).1
        rcases rhRes with _ | ⟨idx1, rkM, ckR⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact ⟨hs1, fun _ _ _ _ _ h => by cases h⟩
        · dsimp only at hr
          rw [stateT_run_lift_bind, mem_support_bind_iff] at hr
          obtain ⟨shRes, -, hr⟩ := hr
          rcases shRes with _ | ⟨idx2, rk2, ckS, pend⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact ⟨hs1, fun _ _ _ _ _ h => by cases h⟩
          · dsimp only at hr
            rcases htd : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
                msg .whisper rc _ with ⟨_ | m, s_out⟩
            · rw [htd] at hr
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact ⟨hs1, fun _ _ _ _ _ h => by cases h⟩
            · rw [htd] at hr
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              refine ⟨hs1, fun st' t' i' m' uOpt hsome => ?_⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at hsome
              rcases hsome with ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
              have h1 := hg.1
              have hmem : ∀ e ∈ g.chainEpochs ++ [g.epoch + 1], e ≤ E + 1 := by
                intro e he
                simp only [List.mem_append, List.mem_singleton] at he
                rcases he with he | rfl
                · exact le_trans (hg.2 e he) (Nat.le_succ E)
                · omega
              exact ⟨⟨by dsimp only; omega, mem_drop_le_of_forall_mem hmem _⟩, by omega,
                bv32_toNat_succ_le msg.counter⟩

theorem ghostBounded_hop2Recv {E : ℕ} (h : Hop2Hyb Pt)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (hg : GhostBounded E g)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt)
    (r : Option ((GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × Option (Hop2Upd Pt)) ×
      (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt))
    (hr : r ∈ support ((hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st)) :
    r.2.1 = st.1 ∧
    ∀ st' t' i' m' uOpt, r.1 = some ((st', t', i', m'), uOpt) →
      GhostBounded (E + 1) st' ∧ t' ≤ E + 1 ∧ i' ≤ 2 ^ 32 := by
  unfold hop2Recv at hr
  rcases htry : SignalMessage.tryFrom P.codec c with _ | msg
  · simp only [htry, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact ⟨rfl, fun _ _ _ _ _ h => by cases h⟩
  · rw [htry] at hr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    rcases hidx : st.2.idx g.party with _ | t
    · simp only [hidx, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨rfl, fun st' t' i' m' uOpt hsome => ?_⟩
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hsome
      obtain ⟨⟨st0, t0, i0, m0⟩, hrec, ⟨h1, _⟩⟩ := hsome
      simp only [Prod.mk.injEq] at h1
      rcases h1 with ⟨rfl, rfl, rfl, rfl⟩
      exact ghostBounded_receive_sessionSchemeU P g c rc st0 t0 i0 m0 hg hrec
    · simp only [hidx] at hr
      by_cases hneed : (g.session.receiverChains.findIdx?
          (·.senderRatchetKey == msg.senderRatchetKey)).isNone
      · simp only [hneed, ↓reduceIte] at hr
        exact ghostBounded_hop2DH P ℓ Dh encT decT h t (st.2.coins g.party)
          g c msg rc hg htry st r hr
      · simp only [hneed, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr
        refine ⟨rfl, fun st' t' i' m' uOpt hsome => ?_⟩
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hsome
        obtain ⟨⟨st0, t0, i0, m0⟩, hrec, ⟨h1, _⟩⟩ := hsome
        simp only [Prod.mk.injEq] at h1
        rcases h1 with ⟨rfl, rfl, rfl, rfl⟩
        exact ghostBounded_receive_sessionSchemeU P g c rc st0 t0 i0 m0 hg hrec

theorem StateGhostBounded.hop2Deliver {E : ℕ} (h : Hop2Hyb Pt)
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt}
    (hs : StateGhostBounded E st.1) (Q : Party) (c : Bytes) :
    ∀ r ∈ support ((CryptoVerification.E2E.hop2Deliver (ℓ := ℓ) P Dh encT decT s h (Q, c)).run st),
      StateGhostBounded (E + 1) r.2.1 := by
  intro r hr
  unfold CryptoVerification.E2E.hop2Deliver at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split_ifs at hr with hwin
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hs.mono (Nat.le_succ E)
  · rcases htr : st.1.inTransit Q.other c with _ | rec_
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hs.mono (Nat.le_succ E)
    · simp only [htr, stateT_run_lift_bind, mem_support_bind_iff] at hr
      obtain ⟨rc, -, hr⟩ := hr
      rw [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨⟨out, s1⟩, hout, hr⟩ := hr
      obtain ⟨hs1, hrec⟩ :=
        ghostBounded_hop2Recv P ℓ Dh encT decT h (st.1.st Q) c rc (hs Q) st (out, s1) hout
      rcases out with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; dsimp only; rw [hs1]; exact hs.mono (Nat.le_succ E)
      · simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        dsimp only
        rw [hs1]
        obtain ⟨hst', -, -⟩ := hrec st' t' i' m' uOpt rfl
        exact hs.accept (Nat.le_succ E) hst'

theorem StateGhostBounded.hop2Inject {E : ℕ} (h : Hop2Hyb Pt)
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt}
    (hs : StateGhostBounded E st.1) (Q : Party) (c : Bytes) :
    ∀ r ∈ support
        ((CryptoVerification.E2E.hop2Inject (ℓ := ℓ) P Dh encT decT qep s h (Q, c)).run st),
      StateGhostBounded (E + 1) r.2.1 := by
  intro r hr
  unfold CryptoVerification.E2E.hop2Inject at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases href : (st.1.win || (st.1.inTransit Q.other c).isSome || !st.1.safeInj 3 ||
      !ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hs.mono (Nat.le_succ E)
  · simp only [href, Bool.false_eq_true, ↓reduceIte,
      stateT_run_lift_bind, mem_support_bind_iff] at hr
    obtain ⟨rc, -, hr⟩ := hr
    rw [StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨out, s1⟩, hout, hr⟩ := hr
    obtain ⟨hs1, hrec⟩ :=
      ghostBounded_hop2Recv P ℓ Dh encT decT h (st.1.st Q) c rc (hs Q) st (out, s1) hout
    rcases out with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; dsimp only; rw [hs1]; exact hs.mono (Nat.le_succ E)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
      split_ifs at hr with hqep ht
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr; dsimp only; rw [hs1]; exact hs.mono (Nat.le_succ E)
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr; dsimp only; rw [hs1]
        obtain ⟨hst', -, -⟩ := hrec st' t' i' m' uOpt rfl
        exact hs.accept (Nat.le_succ E) hst'
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr; dsimp only; rw [hs1]
        intro Q'
        exact (hs Q').mono (Nat.le_succ E)

/-! ## Evaluation bridge for `spkLeakRedProg` -/

local notation "S" => spkLeakSessionSig Pt ℓ PQC
local notation "OSM" => spkLeakSessionSmOps P ℓ decT encT
local notation "OO" => spkLeakSessionOps P ℓ Dh encPt encT decT s
local notation "II" => e2ePrfIface Pt ℓ PQC
local notation "GS" =>
  @gsTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes

theorem receiveSpkC_eval_at {Γ : List (Ty S)}
    (sE : Expr OO Γ (.base .rcoins)) (gE : Expr OO Γ (.base .st))
    (cE : Expr OO Γ (.base .ct)) (rcE : Expr OO Γ (.base .rcoins)) (ρ : Env Γ)
    (hB_u : ∀ c rc st' t' i' m',
      (sessionSchemeU P ℓ).receive (gE.eval ρ) c rc = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hB_b0 : ∀ g c rc prk st' t' i' m',
      finishRecvB0 P ℓ g c rc prk = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B) :
    (receiveSpkC P ℓ Dh encPt encT decT s B sE gE cE rcE).eval ρ =
      receiveSpk P ℓ Dh encT decT (sE.eval ρ) (gE.eval ρ) (cE.eval ρ) (rcE.eval ρ) := by
  unfold receiveSpkC receiveSpk
  rw [eval_bind_ret, eval_ite]
  set sVal := sE.eval ρ
  set gVal := gE.eval ρ
  set cVal := cE.eval ρ
  set rcVal := rcE.eval ρ
  have hb0 : (opIsB0 P ℓ Dh encPt encT decT s (.fst (.snd (Expr.v0 (O := OO))))).eval
      (Env.cons ((Expr.pair sE (.pair gE (.pair cE rcE))).eval ρ) ρ) =
      (gVal.party == .B && gVal.epoch == 0) := by
    simp [gVal, Expr.eval, Expr.v0]
  rw [hb0]
  split_ifs with h
  · have hp : ((Expr.fst (.snd (Expr.v0 (O := OO)))).eval
        (Env.cons ((Expr.pair sE (.pair gE (.pair cE rcE))).eval ρ) ρ)).party = .B := by
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    exact receiveB0C_eval P ℓ Dh encPt encT decT s B hB_b0
      (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
      (Env.cons ((Expr.pair sE (.pair gE (.pair cE rcE))).eval ρ) ρ) hp
  · have hop : (Comp.ret (I := II) (opReceive P ℓ Dh encPt encT decT s B
        (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))))).eval
        (Env.cons ((Expr.pair sE (.pair gE (.pair cE rcE))).eval ρ) ρ) =
        pure (((sessionSchemeU P ℓ).receive gVal cVal rcVal).map
          fun (st', t', i', m') => (st', min t' B, min i' B, m')) := rfl
    rw [hop]
    rcases hrec : (sessionSchemeU P ℓ).receive gVal cVal rcVal with _ | ⟨st', t', i', m'⟩
    · rfl
    · obtain ⟨htB, hiB⟩ := hB_u cVal rcVal st' t' i' m' hrec
      simp [Nat.min_eq_left htB, Nat.min_eq_left hiB]

theorem deliverSpkC_eval_at
    {Γ : List (Ty S)} (stE : Expr OO Γ GS) (argE : Expr OO Γ (.prod .bool (.base .ct)))
    (ρ : Env Γ) (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Q : Party) (c : Bytes) (hBound : SMStateBounded K st)
    (hB_u : ∀ c rc st' t' i' m',
      (sessionSchemeU P ℓ).receive (st.st Q) c rc = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hB_b0 : ∀ g c rc prk st' t' i' m',
      finishRecvB0 P ℓ g c rc prk = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hst : stE.eval ρ = gsEnc st) (harg : argE.eval ρ = (partyEnc Q, c)) :
    (deliverSpkC P ℓ Dh encPt encT decT s K B stE argE).eval ρ =
      Prod.map (Option.map SM.smRrEnc) gsEnc <$>
        (CryptoVerification.E2E.deliverSpk P ℓ Dh encT decT s (Q, c)).run st := by
  unfold deliverSpkC CryptoVerification.E2E.deliverSpk
  rw [eval_bind_ret]
  have h0 : (Expr.pair stE argE).eval ρ = (gsEnc st, partyEnc Q, c) := by
    simp [Expr.eval, hst, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod GS (.prod .bool (.base .ct)) : Ty S))
    (gsEnc st, partyEnc Q, c) ρ
  rw [eval_ite]
  have hWin : (gsWin (.fst (Expr.v0 (O := OO)))).eval ρ₁ = st.win := rfl
  rw [hWin]
  by_cases hwin : st.win
  · simp [ρ₁, hwin, Comp.eval, StateT.run_bind, StateT.run_get, StateT.run_pure,
      Expr.eval, Expr.v0]
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte, eval_caseOpt, Expr.eval_liftL,
      StateT.run_bind, StateT.run_get, pure_bind]
    have hTrans : (inTransitE K (.fst .v0)
        (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) : Expr OSM _ (.opt recTy)).eval ρ₁ =
        (st.inTransit Q.other c).map recEnc := by
      refine inTransitE_eval K (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
        ρ₁ st Q.other eqCt_bytes_eq hBound.trans_le rfl ?_
      simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0]
    rw [hTrans]
    rcases htr : st.inTransit Q.other c with _ | r
    · simp [ρ₁, Comp.eval, StateT.run_pure, Expr.eval, Expr.v0]
    · simp only [Option.map_some, eval_bind, spkDrawBv_eval,
        stateT_run_lift_bind, map_bind]
      refine bind_congr fun rc => ?_
      set ρ₂ := Env.cons (t := (.base .rcoins : Ty S)) rc
        (Env.cons (t := recTy) (recEnc r) ρ₁)
      have hstQ : (pGet (gsSt (.fst (Expr.v2 (O := OO)))) (.fst (.snd .v2))).eval ρ₂ =
          st.st Q := by
        cases Q <;> rfl
      have hrec := receiveSpkC_eval_at P ℓ Dh encPt encT decT s B
        (opSpkSc P ℓ Dh encPt encT decT s)
        (pGet (gsSt (.fst .v2)) (.fst (.snd .v2))) (.snd (.snd .v2)) .v0 ρ₂
        (by rw [hstQ]; exact hB_u) hB_b0
      have hs0 : (opSpkSc P ℓ Dh encPt encT decT s (Γ := _)).eval ρ₂ = s := rfl
      have hc2 : (Expr.snd (.snd (Expr.v2 (O := OO)))).eval ρ₂ = c := rfl
      have hrc0 : (Expr.v0 (O := OO)).eval ρ₂ = rc := rfl
      rw [hs0, hstQ, hc2, hrc0] at hrec
      rw [hrec]
      refine bind_congr fun res => ?_
      rcases res with _ | ⟨st', t', i', m'⟩
      · rw [eval_caseOpt_v0_none]
        simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, SM.smRrEnc, Expr.eval, Expr.v3]
      · rw [eval_caseOpt_v0_some]
        set ρ₃ := Env.cons
          (t := (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) : Ty S))
          (st', t', i', m')
          (Env.cons (t := (.opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) : Ty S))
            (some (st', t', i', m')) ρ₂)
        have hAcc : (acceptE K (.fst (Expr.v4 (O := OO))) (.fst (.snd .v4)) (.fst .v0)
            (recPos .v3)).eval ρ₃ = gsEnc (st.accept Q st' r.pos) :=
          acceptE_eval K (.fst (Expr.v4 (O := OO))) (.fst (.snd .v4)) (.fst .v0) (recPos .v3)
            ρ₃ st Q r.pos hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl rfl
        have hChall : (challContainsE K (.fst (Expr.v4 (O := OO))) (recPos .v3)).eval ρ₃ =
            st.chall.contains r.pos :=
          challContainsE_eval K (.fst (Expr.v4 (O := OO))) (recPos .v3) ρ₃ st r.pos
            hBound.chall_le rfl rfl
        simp only [eval_ret, pair_eval, some_eval, inr_eval, ite_eval, hAcc, hChall,
          StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure, Prod.map]
        cases st.chall.contains r.pos <;> simp [ρ₃, SM.smRrEnc, Expr.eval, Expr.v0]

theorem injectSpkC_eval_at
    {Γ : List (Ty S)} (stE : Expr OO Γ GS) (argE : Expr OO Γ (.prod .bool (.base .ct)))
    (ρ : Env Γ) (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Q : Party) (c : Bytes) (hBound : SMStateBounded K st)
    (hB_u : ∀ c rc st' t' i' m',
      (sessionSchemeU P ℓ).receive (st.st Q) c rc = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hB_b0 : ∀ g c rc prk st' t' i' m',
      finishRecvB0 P ℓ g c rc prk = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hst : stE.eval ρ = gsEnc st) (harg : argE.eval ρ = (partyEnc Q, c)) :
    (injectSpkC P ℓ Dh encPt encT decT s K B qep stE argE).eval ρ =
      Prod.map (Option.map SM.smRrEnc) gsEnc <$>
        (CryptoVerification.E2E.injectSpk P ℓ Dh encT decT qep s (Q, c)).run st := by
  unfold injectSpkC CryptoVerification.E2E.injectSpk
  rw [eval_bind_ret]
  have h0 : (Expr.pair stE argE).eval ρ = (gsEnc st, partyEnc Q, c) := by
    simp [Expr.eval, hst, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod GS (.prod .bool (.base .ct)) : Ty S))
    (gsEnc st, partyEnc Q, c) ρ
  rw [eval_ite]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hRefuse : (orE (gsWin (.fst (Expr.v0 (O := OO))))
      (orE (isSomeE ((inTransitE K (.fst .v0)
          (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) : Expr OSM _ (.opt recTy)).liftL))
        (orE (.not (safeInjE 3 (.fst .v0)))
          (.not (opInjOK P ℓ Dh encPt encT decT s (.snd (.snd .v0))))))).eval ρ₁ =
      (st.win || (st.inTransit Q.other c).isSome || !st.safeInj 3 ||
        !ratchetKeyAdmissible protoSignalCodec decT encT c) := by
    have hTrans : (inTransitE K (.fst .v0)
        (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) : Expr OSM _ (.opt recTy)).eval ρ₁ =
        (st.inTransit Q.other c).map recEnc := by
      refine inTransitE_eval K (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
        ρ₁ st Q.other eqCt_bytes_eq hBound.trans_le rfl ?_
      simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0]
    simp only [orE_eval, isSomeE_eval, Expr.eval_liftL, Expr.eval, hTrans, Option.isSome_map]
    rw [safeInjE_eval 3 (.fst .v0) ρ₁ st rfl]
    simp [ρ₁, gsWin, gsEnc, opInjOK, spkLeakSessionOps, Ops.sum, spkLeakSessionSmOps, smOps,
      Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href : (st.win || (st.inTransit Q.other c).isSome || !st.safeInj 3 ||
      !ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp [ρ₁, href, Comp.eval, StateT.run_pure, Expr.eval, Expr.v0]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, eval_bind, spkDrawBv_eval,
      stateT_run_lift_bind, map_bind]
    refine bind_congr fun rc => ?_
    set ρ₂ := Env.cons (t := (.base .rcoins : Ty S)) rc ρ₁
    have hstQ : (pGet (gsSt (.fst (Expr.v1 (O := OO)))) (.fst (.snd .v1))).eval ρ₂ =
        st.st Q := by
      cases Q <;> rfl
    have hrec := receiveSpkC_eval_at P ℓ Dh encPt encT decT s B
      (opSpkSc P ℓ Dh encPt encT decT s)
      (pGet (gsSt (.fst .v1)) (.fst (.snd .v1))) (.snd (.snd .v1)) .v0 ρ₂
      (by rw [hstQ]; exact hB_u) hB_b0
    have hs0 : (opSpkSc P ℓ Dh encPt encT decT s (Γ := _)).eval ρ₂ = s := rfl
    have hc1 : (Expr.snd (.snd (Expr.v1 (O := OO)))).eval ρ₂ = c := rfl
    have hrc0 : (Expr.v0 (O := OO)).eval ρ₂ = rc := rfl
    rw [hs0, hstQ, hc1, hrc0] at hrec
    rw [hrec]
    refine bind_congr fun res => ?_
    rcases res with _ | ⟨st', t', i', m'⟩
    · rw [eval_caseOpt_v0_none]
      simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, SM.smRrEnc, Expr.eval, Expr.v2]
    · rw [eval_caseOpt_v0_some]
      set ρ₃ := Env.cons
        (t := (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) : Ty S))
        (st', t', i', m')
        (Env.cons (t := (.opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) : Ty S))
          (some (st', t', i', m')) ρ₂)
      rw [eval_ite]
      have hlt : (Expr.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₃ =
          decide (qep + 1 < t') := rfl
      rw [hlt]
      by_cases hqep : qep + 1 < t'
      · simp [ρ₃, ρ₂, ρ₁, hqep, Comp.eval, StateT.run_pure, SM.smRrEnc, Expr.eval, Expr.v3]
      · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ite]
        have hpos : (Expr.pair (otherE (.fst (.snd (Expr.v3 (O := OO)))))
            (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval ρ₃ =
            posEnc ⟨Q.other, t', i'⟩ := by
          simp [ρ₃, ρ₂, ρ₁, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0, Expr.v3]
        have htriv : (trivialE K 3 (.fst (Expr.v3 (O := OO)))
            (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₃ =
            st.trivial 3 ⟨Q.other, t', i'⟩ :=
          trivialE_eval K 3 (.fst (Expr.v3 (O := OO))) _ ρ₃ st ⟨Q.other, t', i'⟩
            hBound.trans_le hBound.comp_le rfl hpos
        rw [htriv]
        by_cases ht : st.trivial 3 ⟨Q.other, t', i'⟩
        · have hAcc : (acceptE K (.fst (Expr.v3 (O := OO))) (.fst (.snd .v3)) (.fst .v0)
              (.pair (otherE (.fst (.snd .v3)))
                (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₃ =
              gsEnc (st.accept Q st' ⟨Q.other, t', i'⟩) :=
            acceptE_eval K (.fst (Expr.v3 (O := OO))) (.fst (.snd .v3)) (.fst .v0) _
              ρ₃ st Q ⟨Q.other, t', i'⟩
              hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl hpos
          simp only [ht, ↓reduceIte, eval_ret, pair_eval, hAcc,
            StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure, Prod.map]
          simp [ρ₃, SM.smRrEnc, Expr.eval, Expr.v0]
        · simp only [ht, Bool.false_eq_true, ↓reduceIte, eval_ret, pair_eval,
            StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure, Prod.map]
          rw [gsSetWin_eval (.fst (Expr.v3 (O := OO))) (.bool true) ρ₃ st rfl]
          simp [SM.smRrEnc, Expr.eval]

private theorem map_liftM_probComp {κ : Type} {G : OracleSpec κ} {α β : Type}
    (f : α → β) (mx : ProbComp α) :
    f <$> (liftM mx : OracleComp (unifSpec + G) α) =
      (liftM (f <$> mx) : OracleComp (unifSpec + G) β) := by
  simp only [← liftComp_eq_liftM, map_eq_bind_pure_comp, Function.comp_def,
    liftComp_bind, liftComp_pure]

private theorem map_canonComp_transmitR {Key St Msg Coins RCoins C : Type}
    [SampleableType Coins] (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ)
    (cfg : ConfigR St Msg C) (hSendOK : ∀ s P, cfg.sendOK (canonComp s) P = cfg.sendOK s P)
    (x : Party × Msg × Option Coins) (st : SM.GameState St Msg C) :
    Prod.map id canonComp <$> (SM.transmitR sm Δ qep cfg x).run st =
      Prod.map id canonComp <$> (SM.transmitR sm Δ qep cfg x).run (canonComp st) := by
  rcases x with ⟨Q, m, optR⟩
  dsimp only [SM.transmitR, SM.transmitImpl]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hSendOK]
  cases cfg.sendOK st Q
  · simp [canonComp_idem]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      StateT.run_get, pure_bind]
    have hw : (canonComp st).win = st.win := rfl
    rw [hw]
    cases st.win
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, map_bind, bind_assoc, pure_bind]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      rw [← canonComp_epMgmt]
      cases st.epMgmt Δ qep Q bad with
      | none => simp [canonComp_idem]
      | some s' =>
        simp only [Option.map_some, StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, map_pure, Prod.map]
        have he : (canonComp s').epoch Q = s'.epoch Q := rfl
        have hi : (canonComp s').idx Q = s'.idx Q := rfl
        have hst : (canonComp s').st Q = s'.st Q := rfl
        rw [he, hi, hst, canonComp_record]
    · simp [canonComp_idem]

private theorem map_canonComp_challR {Key St Msg Coins RCoins C : Type}
    [SampleableType Coins] (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ)
    (cfg : ConfigR St Msg C) (hSendOK : ∀ s P, cfg.sendOK (canonComp s) P = cfg.sendOK s P)
    (x : Party × Msg × Msg × Option Coins) (st : SM.GameState St Msg C) :
    Prod.map id canonComp <$> (SM.challR sm Δ qep cfg x).run st =
      Prod.map id canonComp <$> (SM.challR sm Δ qep cfg x).run (canonComp st) := by
  rcases x with ⟨Q, m₀, m₁, optR⟩
  dsimp only [SM.challR, SM.challImpl]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hSendOK]
  cases cfg.sendOK st Q
  · simp [canonComp_idem]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      StateT.run_get, pure_bind]
    have hw : (canonComp st).win = st.win := rfl
    rw [hw]
    cases st.win
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, map_bind, bind_assoc, pure_bind]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      rw [← canonComp_epMgmt]
      cases st.epMgmt Δ qep Q bad with
      | none => simp [canonComp_idem]
      | some s' =>
        simp only [Option.map_some, canonComp_safeCh]
        have he : (canonComp s').epoch Q = s'.epoch Q := rfl
        by_cases hch : (!(s'.safeCh Δ Q) || !(cfg.base.challAllowedIn (s'.epoch Q))) = true
        · rw [he]; simp [hch, canonComp_idem]
        · rw [he]
          simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_set, pure_bind, StateT.run_pure, map_pure, Prod.map]
          have hb : (canonComp st).b = st.b := rfl
          have hi : (canonComp s').idx Q = s'.idx Q := rfl
          have hst : (canonComp s').st Q = s'.st Q := rfl
          rw [hb, hi, hst, canonComp_record]
    · simp [canonComp_idem]

private theorem map_canonComp_corrRDedup {St Msg C : Type}
    (cfg : ConfigR St Msg C) (hCorrOK : ∀ s P, cfg.corrOK (canonComp s) P = cfg.corrOK s P)
    (Q : Party) (st : SM.GameState St Msg C) :
    Prod.map id canonComp <$> (corrRDedup cfg Q).run st =
      Prod.map id canonComp <$> (SM.corrR cfg Q).run (canonComp st) := by
  dsimp only [corrRDedup, SM.corrR]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, canonComp_corrAllowed,
    canonComp_inWindow, hCorrOK]
  have hw : (canonComp st).win = st.win := rfl
  have hst : (canonComp st).st Q = st.st Q := rfl
  rw [hw, hst]
  split_ifs
  · simp [canonComp_idem]
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, map_pure, Prod.map]
    rw [canonComp_afterCorrDedup]

private theorem map_canonComp_corrR {St Msg C : Type}
    (cfg : ConfigR St Msg C) (hCorrOK : ∀ s P, cfg.corrOK (canonComp s) P = cfg.corrOK s P)
    (Q : Party) (st : SM.GameState St Msg C) :
    Prod.map id canonComp <$> (SM.corrR cfg Q).run st =
      Prod.map id canonComp <$> (SM.corrR cfg Q).run (canonComp st) := by
  dsimp only [SM.corrR]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, canonComp_corrAllowed,
    canonComp_inWindow, hCorrOK]
  have hw : (canonComp st).win = st.win := rfl
  have hst : (canonComp st).st Q = st.st Q := rfl
  rw [hw, hst]
  split_ifs
  · simp [canonComp_idem]
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, map_pure, Prod.map]
    rw [canonComp_afterCorr]

def spkOracleImplDedup :
    QueryImpl (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
      (StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
        (OracleComp (unifSpec + prfSpec Pt (BitVec 256))))
  | .inl u => StateT.lift (query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl u))
  | .inr (.inl (.inl (.inl (.inl x)))) =>
    liftSpkGameM (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inl (.inr x)))) =>
    liftSpkGameM (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inr x))) =>
    CryptoVerification.E2E.deliverSpk P ℓ Dh encT decT s x
  | .inr (.inl (.inr x)) =>
    CryptoVerification.E2E.injectSpk P ℓ Dh encT decT qep s x
  | .inr (.inr x) =>
    liftSpkGameM (corrRDedup (configRefuseEarlyBobCorr decT encT) x)

theorem map_canonComp_simulateQ_spkOracleImplDedup_eq {α : Type}
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) α)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    Prod.map id canonComp <$>
        (simulateQ (spkOracleImplDedup P ℓ Dh encT decT s qep) oa).run st =
      Prod.map id canonComp <$>
        (simulateQ (spkOracleImpl P ℓ Dh encT decT qep s) oa).run st := by
  have hSendOK : ∀ st' Q,
      (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := CBC.Plain ℓ)
        decT encT).sendOK (canonComp st') Q =
        (configRefuseEarlyBobCorr decT encT).sendOK st' Q := fun _ _ => rfl
  have hCorrOK : ∀ st' Q,
      (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := CBC.Plain ℓ)
        decT encT).corrOK (canonComp st') Q =
        (configRefuseEarlyBobCorr decT encT).corrOK st' Q := fun _ _ => rfl
  have hDel : ∀ x st',
      Prod.map id canonComp <$>
          (CryptoVerification.E2E.deliverSpk P ℓ Dh encT decT s x).run st' =
        Prod.map id canonComp <$>
          (CryptoVerification.E2E.deliverSpk P ℓ Dh encT decT s x).run (canonComp st') := by
    rintro ⟨Q, c⟩ st'
    unfold CryptoVerification.E2E.deliverSpk
    simp only [StateT.run_bind, StateT.run_get, pure_bind, canonComp_inTransit]
    have hw : (canonComp st').win = st'.win := rfl
    rw [hw]
    split_ifs
    · simp [canonComp_idem]
    · cases st'.inTransit Q.other c with
      | none => simp [canonComp_idem]
      | some r =>
        simp only [stateT_run_lift_bind, map_bind]
        have hst : (canonComp st').st Q = st'.st Q := rfl
        rw [hst]
        refine bind_congr fun rc => bind_congr fun out => ?_
        cases out with
        | none => simp [canonComp_idem]
        | some quad =>
          rcases quad with ⟨st'', t', i', m'⟩
          have hch : (canonComp st').chall = st'.chall := rfl
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            map_pure, Prod.map, canonComp_accept, canonComp_idem]
          rw [hch]
  have hInj : ∀ x st',
      Prod.map id canonComp <$>
          (CryptoVerification.E2E.injectSpk P ℓ Dh encT decT qep s x).run st' =
        Prod.map id canonComp <$>
          (CryptoVerification.E2E.injectSpk P ℓ Dh encT decT qep s x).run (canonComp st') := by
    rintro ⟨Q, c⟩ st'
    unfold CryptoVerification.E2E.injectSpk
    simp only [StateT.run_bind, StateT.run_get, pure_bind, canonComp_inTransit, canonComp_safeInj]
    have hw : (canonComp st').win = st'.win := rfl
    rw [hw]
    by_cases href : (st'.win || (st'.inTransit Q.other c).isSome || !st'.safeInj 3 ||
        !ratchetKeyAdmissible protoSignalCodec decT encT c)
    · simp [href, canonComp_idem]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, stateT_run_lift_bind, map_bind]
      have hst : (canonComp st').st Q = st'.st Q := rfl
      rw [hst]
      refine bind_congr fun rc => bind_congr fun out => ?_
      cases out with
      | none => simp [canonComp_idem]
      | some quad =>
        rcases quad with ⟨st'', t', i', m'⟩
        dsimp only
        by_cases hqep : qep + 1 < t'
        · simp [hqep, canonComp_idem]
        · simp only [hqep, ↓reduceIte, canonComp_trivial]
          cases st'.trivial 3 ⟨Q.other, t', i'⟩ <;>
            simp [canonComp_accept, canonComp_setWin, canonComp_idem]
  refine map_run_simulateQ_eq_of_idem_proj
    (spkOracleImplDedup P ℓ Dh encT decT s qep)
    (spkOracleImpl P ℓ Dh encT decT qep s) canonComp ?_ ?_ oa rfl
  · rintro (u | (((x | x) | x) | x) | Q) st'
    · simp [spkOracleImplDedup, spkOracleImpl, StateT.run_lift, Prod.map, canonComp_idem]
    · dsimp only [spkOracleImplDedup, spkOracleImpl, liftSpkGameM, StateT.run_mk]
      rw [map_liftM_probComp, map_liftM_probComp,
          map_canonComp_transmitR _ _ _ _ hSendOK]
    · dsimp only [spkOracleImplDedup, spkOracleImpl, liftSpkGameM, StateT.run_mk]
      rw [map_liftM_probComp, map_liftM_probComp,
          map_canonComp_challR _ _ _ _ hSendOK]
    · exact hDel x st'
    · exact hInj x st'
    · dsimp only [spkOracleImplDedup, spkOracleImpl, liftSpkGameM, StateT.run_mk]
      rw [map_liftM_probComp, map_liftM_probComp,
          map_canonComp_corrRDedup _ hCorrOK]
  · rintro (u | (((x | x) | x) | x) | Q) st'
    · simp [spkOracleImpl, StateT.run_lift, Prod.map, canonComp_idem]
    · dsimp only [spkOracleImpl, liftSpkGameM, StateT.run_mk]
      rw [map_liftM_probComp, map_liftM_probComp,
          map_canonComp_transmitR _ _ _ _ hSendOK]
    · dsimp only [spkOracleImpl, liftSpkGameM, StateT.run_mk]
      rw [map_liftM_probComp, map_liftM_probComp,
          map_canonComp_challR _ _ _ _ hSendOK]
    · exact hDel x st'
    · exact hInj x st'
    · dsimp only [spkOracleImpl, liftSpkGameM, StateT.run_mk]
      rw [map_liftM_probComp, map_liftM_probComp,
          map_canonComp_corrR _ hCorrOK]

/-- Evaluating `spkLeakRedProg` on a `qAdv`-query adversary agrees with `spkLeakRed` whenever
`qAdv * qAdv ≤ K * K`, `qAdv ≤ B`, and `2 ^ 32 ≤ B`. -/
theorem spkLeakRedProg_eval_of_le
    (qAdv : ℕ) (hK : qAdv * qAdv ≤ K * K) (hqB : qAdv ≤ B) (h32B : 2 ^ 32 ≤ B)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
    (hA : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)) qAdv) :
    (spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).eval (fun _ => A) () =
      spkLeakRed P Dh encPt encT decT qep s A := by
  let R := spkLeakRedProg P ℓ Dh encPt encT decT s K B qep
  let abs : R.σ.denote → SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes := gsDec
  let Inv : ℕ → R.σ.denote → Prop :=
    fun q v => SMBudgetInv qAdv K q (gsDec v) ∧ StateGhostBounded (qAdv - q) (gsDec v)
  let initImpl : Unit →
      OracleComp (unifSpec + MACScheme.prfSpec Pt (BitVec 256))
        (Unit × SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) := fun _ => do
    let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
      OracleComp (unifSpec + MACScheme.prfSpec Pt (BitVec 256)) Bool)
    let ck0 ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
      OracleComp (unifSpec + MACScheme.prfSpec Pt (BitVec 256)) (BitVec 256))
    let rest ← (liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
      OracleComp (unifSpec + MACScheme.prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256))
    let stA ← initAOracle (Pt := Pt) P Dh ck0 s rest.1 rest.2
    let stB := P.initB ⟨0, ck0, s, rest.1, rest.2⟩
    let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
      { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
    return ((), initSt)
  let finishImpl : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes → Bool →
      OracleComp (unifSpec + MACScheme.prfSpec Pt (BitVec 256)) Bool :=
    fun fin b' => pure (fin.b == b' || fin.win)
  have hinit : (Prod.map id abs <$> R.init.eval (.cons () .nil)) = initImpl () := by
    simp only [R, spkLeakRedProg, initImpl, abs, Comp.eval, spkDrawBool_eval, spkDrawBv_eval,
      map_bind]
    refine bind_congr fun b => bind_congr fun ck0 => ?_
    rw [liftM_sample_prod_bind_bv256]
    refine bind_congr fun alice => bind_congr fun pqr => ?_
    rw [initAOracleC_eval]
    simp only [gsMk, map_pure, Prod.map, id_eq, Expr.eval, opInitB_eval]
    simp only [opSpkSc, opZeroBv, e2eInitB, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
      Env.get_cons_zero, Env.get_cons_succ, spkLeakSessionOps, Ops.sum, spkLeakOps]
    refine bind_congr fun stA => ?_
    congr 1; congr 1
    simp [gsDec]
    refine ⟨?_, ?_, ?_⟩ <;> (funext Q; cases Q <;> rfl)
  have hinitInv : ∀ r ∈ support (R.init.eval (.cons () .nil)), Inv qAdv r.2 := by
    intro r hr
    have hmem : (r.1, abs r.2) ∈ support (Prod.map id abs <$> R.init.eval (.cons () .nil)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨r, hr, rfl⟩
    rw [hinit] at hmem
    simp only [initImpl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨b, -, ck0, -, rest, -, stA, hstA, hmem⟩
    have habs : abs r.2 = _ := (Prod.ext_iff.mp hmem).2
    refine ⟨?_, ?_⟩
    · change SMBudgetInv qAdv K qAdv (abs r.2)
      rw [habs]
      exact SMBudgetInv.init hK _ b
    · change StateGhostBounded (qAdv - qAdv) (abs r.2)
      rw [Nat.sub_self, habs]
      intro Q; cases Q
      · exact ghostBounded_initAOracle P Dh ck0 s rest.1 rest.2 stA hstA
      · exact ghostBounded_initB P _
  have hU : ∀ n st,
      (spkOracleImplDedup P ℓ Dh encT decT s qep (.inl n)).run st =
        (StateT.lift ((e2ePrfIface Pt ℓ PQC).fwdU n)).run st := fun _ _ => rfl
  have hB_b0 : ∀ g c rc prk st' t' i' m',
      finishRecvB0 P ℓ g c rc prk = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B := by
    intro g c rc prk st' t' i' m' hfin
    obtain ⟨-, ht, hi⟩ := ghostBounded_finishRecvB0 (E := 0) P g c rc prk st' t' i' m' hfin
    exact ⟨by omega, le_trans hi h32B⟩
  have hstep_eq : ∀ m t v, Inv (m + 1) v →
      (Prod.map id abs <$> ((R.impl (.inr t)).run v)) =
        (spkOracleImplDedup P ℓ Dh encT decT s qep (.inr t)).run (abs v) := by
    dsimp only [R, CostedReduction.impl, handlerImpl, spkLeakRedProg, abs, Inv]
    intro m t v ⟨hv, hgb⟩
    set st := gsDec v
    have hv_enc : v = gsEnc st := (gsEnc_gsDec v).symm
    have hBound : SMStateBounded K st := hv.toBounded
    have hm_le : m + 1 ≤ qAdv := by have := hv.trans_le; omega
    have hB_u : ∀ Q c rc st' t' i' m',
        (sessionSchemeU P ℓ).receive (st.st Q) c rc = some (st', t', i', m') →
          t' ≤ B ∧ i' ≤ B := by
      intro Q c rc st' t' i' m' hrec
      obtain ⟨-, ht, hi⟩ :=
        ghostBounded_receive_sessionSchemeU P (st.st Q) c rc st' t' i' m' (hgb Q) hrec
      exact ⟨by omega, le_trans hi h32B⟩
    have hCfg := configSpkS_agrees (PQC := PQC) P ℓ encT decT K
    have hCoins : ∀ {Γ} (ρ' : Env Γ),
        (spkDrawCoins ℓ (Pt := Pt) (PQC := PQC) (O' := OSM) (Γ := Γ)).eval ρ' =
          some <$> (e2ePrfIface Pt ℓ PQC).liftP ($ᵗ PQC : ProbComp PQC) :=
      fun ρ' => spkDrawCoins_eval ℓ ρ'
    simp only [spkOracleImplC, StateT.run_mk,
      eval_bind_ret, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rcases t with (((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q
    · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v4,
        Env.get_cons_zero, Env.get_cons_succ, Comp.eval_liftL]
      rw [transmitRC_eval (I := II) (sessionSchemeUPt P ℓ) 3 qep K
        (ConfigRC.spkS OSM) (configRefuseEarlyBobCorr decT encT) hCfg rfl
        (spkDrawCoins ℓ (PQC := PQC)) hCoins _ _ _ st Q msg optR hBound ?_ ?_]
      · simp only [spkOracleImplDedup, liftSpkGameM, StateT.run_mk,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq,
          gsDec_gsEnc, Prod.mk.eta, bind_pure]
        rfl
      · exact hv_enc
      · rfl
    · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v4,
        Env.get_cons_zero, Env.get_cons_succ, Comp.eval_liftL]
      rw [challRC_eval (I := II) (sessionSchemeUPt P ℓ) 3 qep K
        (ConfigRC.spkS OSM) (configRefuseEarlyBobCorr decT encT) hCfg rfl
        (spkDrawCoins ℓ (PQC := PQC)) hCoins _ _ _ st Q m₀ m₁ optR hBound ?_ ?_]
      · simp only [spkOracleImplDedup, liftSpkGameM, StateT.run_mk,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq,
          gsDec_gsEnc, Prod.mk.eta, bind_pure]
        rfl
      · exact hv_enc
      · rfl
    · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v3,
        Env.get_cons_zero, Env.get_cons_succ]
      rw [deliverSpkC_eval_at P ℓ Dh encPt encT decT s K B
        _ _ _ st Q c hBound (hB_u Q) hB_b0 ?_ ?_]
      · dsimp only [spkOracleImplDedup, e2eCodec, smCodec]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
          Prod.map, id_eq, gsDec_gsEnc, Option.map_map, smRrDec_smRrEnc, Option.map_id',
          Prod.mk.eta, bind_pure]
      · exact hv_enc
      · rfl
    · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
        Env.get_cons_zero, Env.get_cons_succ]
      rw [injectSpkC_eval_at P ℓ Dh encPt encT decT s K B qep
        _ _ _ st Q c hBound (hB_u Q) hB_b0 ?_ ?_]
      · dsimp only [spkOracleImplDedup, e2eCodec, smCodec]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
          Prod.map, id_eq, gsDec_gsEnc, Option.map_map, smRrDec_smRrEnc, Option.map_id',
          Prod.mk.eta, bind_pure]
      · exact hv_enc
      · rfl
    · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1,
        Env.get_cons_zero, Env.get_cons_succ, Comp.eval_liftL]
      rw [corrRC_eval (I := II) K (ConfigRC.spkS OSM) (configRefuseEarlyBobCorr decT encT)
        hCfg _ _ _ st Q hBound ?_ ?_]
      · simp only [spkOracleImplDedup, liftSpkGameM, StateT.run_mk,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq,
          gsDec_gsEnc, Prod.mk.eta, bind_pure]
        rfl
      · exact hv_enc
      · rfl
  have hstep : ∀ m t v, Inv (m + 1) v →
      (Prod.map id abs <$> ((R.impl (.inr t)).run v)) =
        (spkOracleImplDedup P ℓ Dh encT decT s qep (.inr t)).run (abs v) ∧
      ∀ r ∈ support ((R.impl (.inr t)).run v), Inv m r.2 := by
    intro m t v hv
    have heq := hstep_eq m t v hv
    refine ⟨heq, fun r hr => ?_⟩
    have hmem : (r.1, abs r.2) ∈ support (Prod.map id abs <$> ((R.impl (.inr t)).run v)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨r, hr, rfl⟩
    rw [heq] at hmem
    have hm_le : m + 1 ≤ qAdv := by have := hv.1.trans_le; omega
    have hsub : qAdv - (m + 1) + 1 ≤ qAdv - m := by omega
    rcases t with (((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q
    · rw [spkOracleImplDedup, mem_support_liftSpkGameM] at hmem
      exact ⟨hv.1.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT)
        (Q, msg, optR) (r.1, abs r.2) hmem,
        (hv.2.transmitR P (configRefuseEarlyBobCorr decT encT) (Q, msg, optR) (r.1, abs r.2) hmem).mono hsub⟩
    · rw [spkOracleImplDedup, mem_support_liftSpkGameM] at hmem
      exact ⟨hv.1.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT)
        (Q, m₀, m₁, optR) (r.1, abs r.2) hmem,
        (hv.2.challR P (configRefuseEarlyBobCorr decT encT) (Q, m₀, m₁, optR) (r.1, abs r.2) hmem).mono hsub⟩
    · exact ⟨deliverSpk_inv P ℓ Dh encT decT s K (abs v) Q c qAdv m hv.1 (r.1, abs r.2) hmem,
        (hv.2.deliverSpk P ℓ Dh encT decT s Q c (r.1, abs r.2) hmem).mono hsub⟩
    · exact ⟨injectSpk_inv P ℓ Dh encT decT s K qep (abs v) Q c qAdv m hv.1 (r.1, abs r.2) hmem,
        (hv.2.injectSpk P ℓ Dh encT decT s qep Q c (r.1, abs r.2) hmem).mono hsub⟩
    · rw [spkOracleImplDedup, mem_support_liftSpkGameM] at hmem
      exact ⟨hv.1.corrRDedup (configRefuseEarlyBobCorr decT encT) Q (r.1, abs r.2) hmem,
        (hv.2.corrRDedup (configRefuseEarlyBobCorr decT encT) Q (r.1, abs r.2) hmem).mono hsub⟩
  have hfin : ∀ v b', Inv 0 v →
      R.finish.eval (.cons v (.cons b' .nil)) = finishImpl (abs v) b' := by
    intro v b' _
    rcases v with ⟨stAB, b, win, rest⟩
    simp [R, spkLeakRedProg, finishImpl, abs, gsDec, gsB, gsWin, orE_eval, boolEq_eval,
      Comp.eval, Expr.eval, Expr.v0, Expr.v1]
  have hmono : ∀ {m n} (v), m ≤ n → Inv n v → Inv m v :=
    fun _ hmn hv => ⟨hv.1.mono hmn, hv.2.mono (by omega)⟩
  have heval := R.eval_eq_simulateQ_of_abs abs Inv initImpl
    (spkOracleImplDedup P ℓ Dh encT decT s qep) finishImpl qAdv ()
    hinit hinitInv hU hstep hfin hmono (fun _ => A) (fun _ => hA)
  rw [heval]
  simp only [initImpl, finishImpl, spkLeakRed, bind_assoc, pure_bind]
  refine bind_congr fun b => bind_congr fun ck0 => bind_congr fun rest =>
    bind_congr fun stA => ?_
  have hsim := congrArg
    (fun p => (fun x : Bool × SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes =>
      (x.2.b == x.1 || x.2.win)) <$> p)
    (map_canonComp_simulateQ_spkOracleImplDedup_eq P ℓ Dh encT decT s qep A
      ({ st := fun Q => match Q with | .A => stA | .B => P.initB ⟨0, ck0, s, rest.1, rest.2⟩,
         b := b } : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes))
  simp only [Functor.map_map] at hsim
  have hsim' :
      ((simulateQ (spkOracleImplDedup P ℓ Dh encT decT s qep) A).run
        { st := fun Q => match Q with | .A => stA | .B => P.initB ⟨0, ck0, s, rest.1, rest.2⟩,
          b := b } >>= fun x => pure (x.2.b == x.1 || x.2.win)) =
      ((simulateQ (spkOracleImpl P ℓ Dh encT decT qep s) A).run
        { st := fun Q => match Q with | .A => stA | .B => P.initB ⟨0, ck0, s, rest.1, rest.2⟩,
          b := b } >>= fun x => pure (x.2.b == x.1 || x.2.win)) := by
    simpa only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq, canonComp] using hsim
  rw [hsim']
  refine bind_congr_of_mem_support' _ fun ⟨b', fin⟩ hfin' => ?_
  have hb := simulateQ_spkOracleImpl_b P ℓ Dh encT decT s qep A _ (b', fin) hfin'
  dsimp only at hb ⊢
  rw [hb]

/-! ## Evaluation bridges for `hop2PrfRedKProg` and `hop2PrgRedKProg` -/

theorem hop2FinishNoneC_eval_at (h : Hop2Hyb Pt) {Γ : List (Ty S)}
    (aux1E : Expr OO Γ (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
    (gE : Expr OO Γ (.base .st)) (cE : Expr OO Γ (.base .ct)) (rcE : Expr OO Γ (.base .rcoins))
    (rkckE : Expr OO Γ (.prod (.base .rcoins) (.base .rcoins))) (ρ : Env Γ)
    (gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (aux1 : Hop2Aux Pt)
    (g : GhostState Bytes) (c : Bytes) (msg : SignalMessage) (sc : SenderChain)
    (rc rkM ckR : BitVec 256) (T : Pt)
    (hB_dh : ∀ rk2 ckR' ckS st' t' i' m',
      finishHop2DH P ℓ g c rc rk2 ckR' ckS = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hsc : g.session.senderChain = some sc)
    (haux1 : aux1E.eval ρ = hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux1)
    (hg : gE.eval ρ = g) (hc : cE.eval ρ = c) (hrc : rcE.eval ρ = rc)
    (hrkck : rkckE.eval ρ = (rkM, ckR)) :
    Prod.map (hop2OutDec (PQC := PQC) (ℓ := ℓ))
        (fun aux' => (gs, hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux')) <$>
      (hop2FinishNoneC P ℓ Dh encPt encT decT s B (I := II) aux1E gE cE rcE rkckE).eval ρ =
      ((do
        let newKey := KeyPair.generate P.C rc
        match ← StateT.lift (hop2SendHalf P h none rkM msg.senderRatchetKey newKey.privateKey
            (Dh.dh rc T)) with
        | none => return none
        | some (idx2, rk2, ckS, pend) =>
          let cur := sc.chainKey.index
          let sess' : SessionState Bytes :=
            { g.session with
              previousCounter := if cur = 0 then 0 else cur - 1
              rootKey := rk2
              receiverChains := RatchetState.evictReceiverChains
                (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
              senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
          match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              rc sess' with
          | (.error _, _) => return none
          | (.ok m, s_out) =>
            let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
              ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
            return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
              g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨idx2, rc, pend⟩) :
          Hop2M Pt ℓ (Hop2Out Pt ℓ)).run (gs, aux1)) := by
  unfold hop2FinishNoneC hop2SendHalf
  rw [eval_bind_ret]
  have h0 : (Expr.pair aux1E (.pair gE (.pair cE (.pair rcE rkckE)))).eval ρ =
      (hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux1, g, c, rc, rkM, ckR) := by
    simp [Expr.eval, haux1, hg, hc, hrc, hrkck]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
      (.prod (.base .st) (.prod (.base .ct) (.prod (.base .rcoins)
        (.prod (.base .rcoins) (.base .rcoins))))) : Ty S))
    (hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux1, g, c, rc, rkM, ckR) ρ
  rw [eval_caseOpt]
  have hshr : (opSendHalfReal P ℓ Dh encPt encT decT s
      (.fst (.snd (.snd (.snd (.snd .v0)))))
      (.fst (.snd (.snd .v0)))
      (.fst (.snd (.snd (.snd .v0))))).eval ρ₁ = sendHalfReal P rkM c rc := by
    simp [ρ₁, Expr.eval, Expr.v0]
  rw [hshr]
  unfold sendHalfReal
  rw [htry]
  dsimp only
  rcases rootCreateChain P.C rkM msg.senderRatchetKey
      (KeyPair.generate P.C rc).privateKey with _ | ⟨rk2, ck⟩
  · rw [stateT_run_lift_bind, pure_bind]
    simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec, Expr.eval, Expr.v0]
  · dsimp only
    rw [stateT_run_lift_bind, pure_bind]
    dsimp only
    set ρ₂ := Env.cons (t := (.prod (.base .rcoins) (.base .rcoins) : Ty S)) (rk2, ck.key) ρ₁
    rw [eval_caseOpt]
    have hfinDH : (opFinishHop2DH P ℓ Dh encPt encT decT s B
        (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
        (.fst .v0) (.snd (.snd (.snd (.snd (.snd .v1))))) (.snd .v0)).eval ρ₂ =
        (finishHop2DH P ℓ g c rc rk2 ckR ck.key).map
          (fun x => (x.1, min x.2.1 B, min x.2.2.1 B, x.2.2.2)) := by
      simp [ρ₂, ρ₁, Expr.eval, Expr.v0, Expr.v1]
    rw [hfinDH]
    have hfinEq : (finishHop2DH P ℓ g c rc rk2 ckR ck.key).map
        (fun x => (x.1, min x.2.1 B, min x.2.2.1 B, x.2.2.2)) =
        finishHop2DH P ℓ g c rc rk2 ckR ck.key := by
      rcases h : finishHop2DH P ℓ g c rc rk2 ckR ck.key with _ | ⟨st', t', i', m'⟩
      · rfl
      · obtain ⟨htB, hiB⟩ := hB_dh rk2 ckR ck.key st' t' i' m' h
        simp [Nat.min_eq_left htB, Nat.min_eq_left hiB]
    rw [hfinEq]
    unfold finishHop2DH
    rw [htry, hsc]
    dsimp only
    rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
        msg .whisper rc _ with ⟨_ | m, s_out⟩
    · simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec, Expr.eval, Expr.v1]
    · simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec, hop2UpdDec,
        Expr.eval, Expr.v0, Expr.v2]

theorem hop2DHC_eval_at (h : Hop2Hyb Pt)
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO II Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr OO Γ (.base .rcoins)) (qE : Expr OO Γ (.base .key)) (ρ' : Env Γ),
      c1E.eval ρ' = h.chall.1 → (stepC c1E qE).eval ρ' = h.step (qE.eval ρ'))
    {Γ : List (Ty S)}
    (auxE : Expr OO Γ (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
    (challE : Expr OO Γ (hop2ChallTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
    (tE : Expr OO Γ .nat) (coinsE : Expr OO Γ (.base .rcoins))
    (gE : Expr OO Γ (.base .st)) (cE : Expr OO Γ (.base .ct))
    (rcE : Expr OO Γ (.base .rcoins)) (ρ : Env Γ)
    (gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (t : ℕ) (coins : BitVec 256) (g : GhostState Bytes) (c : Bytes) (msg : SignalMessage)
    (rc : BitVec 256) (hlazy : aux.lazy.length ≤ K) (hmade : aux.made.length ≤ K + 1)
    (hB_dh : ∀ rk2 ckR ckS st' t' i' m',
      finishHop2DH P ℓ g c rc rk2 ckR ckS = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (haux : auxE.eval ρ = hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux) (hchall : challE.eval ρ = h.chall)
    (ht : tE.eval ρ = t) (hcoins : coinsE.eval ρ = coins)
    (hg : gE.eval ρ = g) (hc : cE.eval ρ = c) (hrc : rcE.eval ρ = rc) :
    Prod.map (hop2OutDec (PQC := PQC) (ℓ := ℓ))
        (fun aux' => (gs, hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux')) <$>
      (hop2DHC P ℓ Dh encPt encT decT s K B h.k (spkDrawBv P ℓ Dh encPt encT decT s) stepC
        auxE challE tE coinsE gE cE rcE).eval ρ =
      (hop2DH (ℓ := ℓ) P Dh encT decT h (some t) coins g msg rc).run (gs, aux) := by
  unfold hop2DHC hop2DH
  rw [eval_bind_ret]
  have h0 : (Expr.pair auxE (.pair challE (.pair tE (.pair coinsE (.pair gE (.pair cE rcE)))))).eval
      ρ = (hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux, h.chall, t, coins, g, c, rc) := by
    simp [Expr.eval, haux, hchall, ht, hcoins, hg, hc, hrc]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
      (.prod (hop2ChallTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
        (.prod .nat (.prod (.base .rcoins) (.prod (.base .st)
          (.prod (.base .ct) (.base .rcoins)))))) : Ty S))
    (hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux, h.chall, t, coins, g, c, rc) ρ
  rw [eval_caseOpt]
  have hdt : (opDhTargetPt P ℓ Dh encPt encT decT s
      (.fst (.snd (.snd (.snd (.snd .v0)))))
      (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))).eval ρ₁ =
      dhTargetPt P encT decT g c := by
    simp [ρ₁, Expr.eval, Expr.v0]
  rw [hdt]
  unfold dhTargetPt
  rw [htry]
  dsimp only
  rcases hdec : decT msg.senderRatchetKey with _ | T
  · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec, Expr.eval, Expr.v0]
  · dsimp only
    split_ifs with hbad
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec, Expr.eval, Expr.v0]
    · rcases hsc : g.session.senderChain with _ | sc
      · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec, Expr.eval, Expr.v0]
      · dsimp only
        set ρ₂ := Env.cons (t := (.base .key : Ty S)) T ρ₁
        rw [eval_ite]
        have hZero : (opIsZeroPt P ℓ Dh encPt encT decT s
            (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0)).eval ρ₂ =
            decide (Dh.dh coins T = 0) := rfl
        rw [hZero]
        by_cases hQ0 : Dh.dh coins T = 0
        · simp [ρ₂, ρ₁, hop2RecvHalf, hQ0, Comp.eval, StateT.run_pure,
            Prod.map, hop2OutDec, Expr.eval, Expr.v1]
        · simp only [hop2RecvHalf, hQ0, decide_false, Bool.false_eq_true, ↓reduceIte,
            eval_ite, leN_eval]
          have hle : decide ((Expr.fst (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ ≤
              (Expr.nat (O := OO) h.k).eval ρ₂) = decide (t ≤ h.k) := rfl
          rw [hle]
          by_cases htk : t ≤ h.k
          · simp only [htk, decide_true, ↓reduceIte, eval_caseOpt,
              StateT.run_bind, StateT.run_get, pure_bind]
            have hlk := hop2LookupE_eval P ℓ Dh encPt encT decT s (K + 1)
              (auxMade (.fst .v1)) (.fst (.snd (.snd .v1)))
              (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0)
              ρ₂ aux.made t (Dh.dh coins T) hmade rfl rfl rfl
            rw [hlk]
            rcases aux.made.lookup (t, Dh.dh coins T) with _ | ck
            · simp only [eval_bind, StateT.run_bind, map_bind]
              have hlazy_eval := hop2LazyC_eval P ℓ Dh encPt encT decT s K
                (.fst .v1) (.fst (.snd (.snd .v1)))
                (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0)
                ρ₂ gs aux t (Dh.dh coins T) hlazy rfl rfl rfl
              rw [← hlazy_eval, bind_map_left, bind_assoc]
              refine bind_congr fun a => ?_
              rcases a with ⟨u, aux1⟩
              rw [StateT.run_pure, pure_bind]
              dsimp only [Prod.map, id_eq]
              set ρ₃ := Env.cons (t := (.prod (.base .rcoins)
                (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)) : Ty S)) (u, aux1) ρ₂
              exact hop2FinishNoneC_eval_at P ℓ Dh encPt encT decT s B h
                (.snd .v0) (.fst (.snd (.snd (.snd (.snd .v2)))))
                (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
                (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
                (opRootExpand P ℓ Dh encPt encT decT s (.fst .v0)) ρ₃
                gs (hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux1) g c msg sc rc
                (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
                (Ratchet.rootExpand P.C.F (keyToBytes32 u)).2 T hB_dh htry hsc
                rfl rfl rfl rfl
                (by simp [ρ₃, opRootExpand, expandPRG, spkLeakSessionOps, Ops.sum,
                  spkLeakOps, Expr.eval, Expr.v0])
            · dsimp only
              set ρ₃ := Env.cons (t := (.base .rcoins : Ty S)) ck ρ₂
              rw [eval_bind, StateT.run_pure, pure_bind, stateT_run_lift_bind, map_bind]
              have hsh := hop2SendHalfC_eval P ℓ Dh encPt encT decT s h stepC hStep
                (.fst (.snd .v2)) (.some (.add (.fst (.snd (.snd .v2))) (.nat 1)))
                (opZeroBv P ℓ Dh encPt encT decT s)
                (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
                (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
                (opDh P ℓ Dh encPt encT decT s
                  (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))) .v1)
                ρ₃ (some (t + 1)) 0 c msg rc (Dh.dh rc T) htry rfl rfl
                (by simp [opZeroBv, spkLeakSessionOps, Ops.sum, spkLeakOps, Expr.eval]; rfl)
                rfl rfl rfl
              rw [hsh]
              refine bind_congr fun shRes => ?_
              rcases shRes with _ | ⟨idx2, rk2, ckS, pend⟩
              · rw [eval_caseOpt_v0_none]
                simp [ρ₃, ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec,
                  Expr.eval, Expr.v3]
              · rw [eval_caseOpt_v0_some]
                set ρ₅ := Env.cons
                  (t := (.prod (.opt .nat)
                    (.prod (.base .rcoins)
                      (.prod (.base .rcoins)
                        (.opt (hop2EntryTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))))) : Ty S))
                  (idx2, rk2, ckS, pend)
                  (Env.cons (t := hop2SendHalfResTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
                    (some (idx2, rk2, ckS, pend)) ρ₃)
                rw [eval_caseOpt]
                have hfinDH : (opFinishHop2DH P ℓ Dh encPt encT decT s B
                    (.fst (.snd (.snd (.snd (.snd .v4)))))
                    (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))
                    (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))
                    (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))).eval ρ₅ =
                    (finishHop2DH P ℓ g c rc rk2 ck ckS).map
                      (fun x => (x.1, min x.2.1 B, min x.2.2.1 B, x.2.2.2)) := by
                  simp [ρ₅, ρ₃, ρ₂, ρ₁, Expr.eval, Expr.v0, Expr.v2, Expr.v4]
                rw [hfinDH]
                have hfinEq : (finishHop2DH P ℓ g c rc rk2 ck ckS).map
                    (fun x => (x.1, min x.2.1 B, min x.2.2.1 B, x.2.2.2)) =
                    finishHop2DH P ℓ g c rc rk2 ck ckS := by
                  rcases h : finishHop2DH P ℓ g c rc rk2 ck ckS with _ | ⟨st', t', i', m'⟩
                  · rfl
                  · obtain ⟨htB, hiB⟩ := hB_dh rk2 ck ckS st' t' i' m' h
                    simp [Nat.min_eq_left htB, Nat.min_eq_left hiB]
                rw [hfinEq]
                unfold finishHop2DH
                rw [htry, hsc]
                dsimp only
                rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
                    msg .whisper rc _ with ⟨_ | m, s_out⟩
                · simp [ρ₅, ρ₃, ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec,
                    Expr.eval, Expr.v4]
                · simp [ρ₅, ρ₃, ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec,
                    hop2UpdDec, Expr.eval, Expr.v0, Expr.v1, Expr.v5]
          · simp only [htk, decide_false, Bool.false_eq_true, ↓reduceIte, eval_bind, map_bind]
            rw [StateT.run_bind, stateT_run_lift_bind, bind_assoc]
            have hst := hStep (.fst (.fst (.snd .v1)))
              (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0) ρ₂ rfl
            have hq1 : (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0).eval
                ρ₂ = Dh.dh coins T := rfl
            rw [hq1] at hst
            rw [hst]
            refine bind_congr fun u => ?_
            rw [StateT.run_pure, pure_bind]
            dsimp only
            set ρ₃ := Env.cons (t := (.base .rcoins : Ty S)) u ρ₂
            exact hop2FinishNoneC_eval_at P ℓ Dh encPt encT decT s B h
              (.fst .v2) (.fst (.snd (.snd (.snd (.snd .v2)))))
              (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
              (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
              (opRootExpand P ℓ Dh encPt encT decT s .v0) ρ₃
              gs aux g c msg sc rc
              (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
              (Ratchet.rootExpand P.C.F (keyToBytes32 u)).2 T hB_dh htry hsc
              rfl rfl rfl rfl
              (by simp [ρ₃, opRootExpand, expandPRG, spkLeakSessionOps, Ops.sum,
                spkLeakOps, Expr.eval, Expr.v0])

theorem hop2RecvC_eval_at (h : Hop2Hyb Pt)
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO II Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr OO Γ (.base .rcoins)) (qE : Expr OO Γ (.base .key)) (ρ' : Env Γ),
      c1E.eval ρ' = h.chall.1 → (stepC c1E qE).eval ρ' = h.step (qE.eval ρ'))
    {Γ : List (Ty S)}
    (auxE : Expr OO Γ (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
    (challE : Expr OO Γ (hop2ChallTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
    (gE : Expr OO Γ (.base .st)) (cE : Expr OO Γ (.base .ct))
    (rcE : Expr OO Γ (.base .rcoins)) (ρ : Env Γ)
    (gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (hlazy : aux.lazy.length ≤ K) (hmade : aux.made.length ≤ K + 1)
    (hB_u : ∀ st' t' i' m',
      (sessionSchemeU P ℓ).receive g c rc = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hB_dh : ∀ rk2 ckR ckS st' t' i' m',
      finishHop2DH P ℓ g c rc rk2 ckR ckS = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (haux : auxE.eval ρ = hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux) (hchall : challE.eval ρ = h.chall)
    (hg : gE.eval ρ = g) (hc : cE.eval ρ = c) (hrc : rcE.eval ρ = rc) :
    Prod.map (hop2OutDec (PQC := PQC) (ℓ := ℓ))
        (fun aux' => (gs, hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux')) <$>
      (hop2RecvC P ℓ Dh encPt encT decT s K B h.k (spkDrawBv P ℓ Dh encPt encT decT s) stepC
        auxE challE gE cE rcE).eval ρ =
      (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run (gs, aux) := by
  unfold hop2RecvC hop2Recv
  rw [eval_bind_ret]
  have h0 : (Expr.pair auxE (.pair challE (.pair gE (.pair cE rcE)))).eval ρ =
      (hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux, h.chall, g, c, rc) := by
    simp [Expr.eval, haux, hchall, hg, hc, hrc]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
      (.prod (hop2ChallTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
        (.prod (.base .st) (.prod (.base .ct) (.base .rcoins)))) : Ty S))
    (hop2AuxEnc (PQC := PQC) (ℓ := ℓ) aux, h.chall, g, c, rc) ρ
  rw [eval_ite]
  have hwok : (opWireOk P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v0))))).eval ρ₁ =
      (SignalMessage.tryFrom P.codec c).isOk := by
    simp [ρ₁, Expr.eval, Expr.v0]
  rw [hwok]
  rcases htry : SignalMessage.tryFrom P.codec c with _ | msg
  · simp [ρ₁, Except.isOk, Except.toBool, Comp.eval, StateT.run_pure, Prod.map,
      hop2OutDec, Expr.eval, Expr.v0]
  · simp only [Except.isOk, Except.toBool, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_caseOpt]
    have hidx : (pGet (auxIdx (.fst (Expr.v0 (O := OO))))
        (opStParty P ℓ Dh encPt encT decT s (.fst (.snd (.snd .v0))))).eval ρ₁ =
        aux.idx g.party := by
      change (if partyEnc g.party then aux.idx .B else aux.idx .A) = aux.idx g.party
      cases g.party <;> rfl
    rw [hidx]
    have hrec_eq : ((sessionSchemeU P ℓ).receive g c rc).map
        (fun x => (x.1, min x.2.1 B, min x.2.2.1 B, x.2.2.2)) =
        (sessionSchemeU P ℓ).receive g c rc := by
      rcases h : (sessionSchemeU P ℓ).receive g c rc with _ | ⟨st', t', i', m'⟩
      · rfl
      · obtain ⟨htB, hiB⟩ := hB_u st' t' i' m' h
        simp [Nat.min_eq_left htB, Nat.min_eq_left hiB]
    rcases aux.idx g.party with _ | t
    · dsimp only
      rw [eval_caseOpt]
      have hop : (opReceive P ℓ Dh encPt encT decT s B
          (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
          (.snd (.snd (.snd (.snd .v0))))).eval ρ₁ =
          ((sessionSchemeU P ℓ).receive g c rc).map
            (fun x => (x.1, min x.2.1 B, min x.2.2.1 B, x.2.2.2)) := rfl
      rw [hop, hrec_eq]
      rcases (sessionSchemeU P ℓ).receive g c rc with _ | r <;>
        simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec, Expr.eval, Expr.v0, Expr.v1]
    · dsimp only
      set ρ₂ := Env.cons (t := .nat) t ρ₁
      rw [eval_ite]
      have hndh : (opNeedsDH P ℓ Dh encPt encT decT s
          (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))).eval ρ₂ =
          (g.session.receiverChains.findIdx?
            (·.senderRatchetKey == msg.senderRatchetKey)).isNone := by
        rw [opNeedsDH_eval]
        change needsDH P g c = _
        unfold needsDH
        rw [htry]
      rw [hndh]
      by_cases hneed : (g.session.receiverChains.findIdx?
          (·.senderRatchetKey == msg.senderRatchetKey)).isNone
      · simp only [hneed, ↓reduceIte]
        have hcoins : (pGet (auxCoins (.fst (Expr.v1 (O := OO))))
            (opStParty P ℓ Dh encPt encT decT s (.fst (.snd (.snd .v1))))).eval ρ₂ =
            aux.coins g.party := by
          change (if partyEnc g.party then aux.coins .B else aux.coins .A) = aux.coins g.party
          cases g.party <;> rfl
        exact hop2DHC_eval_at P ℓ Dh encPt encT decT s K B h stepC hStep
          (.fst .v1) (.fst (.snd .v1)) .v0
          (pGet (auxCoins (.fst .v1)) (opStParty P ℓ Dh encPt encT decT s (.fst (.snd (.snd .v1)))))
          (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
          (.snd (.snd (.snd (.snd .v1))))
          ρ₂ gs aux t (aux.coins g.party) g c msg rc hlazy hmade hB_dh htry
          rfl rfl rfl hcoins rfl rfl rfl
      · simp only [hneed, Bool.false_eq_true, ↓reduceIte, eval_caseOpt]
        have hop : (opReceive P ℓ Dh encPt encT decT s B
            (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
            (.snd (.snd (.snd (.snd .v1))))).eval ρ₂ =
            ((sessionSchemeU P ℓ).receive g c rc).map
              (fun x => (x.1, min x.2.1 B, min x.2.2.1 B, x.2.2.2)) := rfl
        rw [hop, hrec_eq]
        rcases (sessionSchemeU P ℓ).receive g c rc with _ | r <;>
          simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec,
            Expr.eval, Expr.v0, Expr.v1, Expr.v2]

theorem hop2DeliverC_eval_at (h : Hop2Hyb Pt)
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO II Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr OO Γ (.base .rcoins)) (qE : Expr OO Γ (.base .key)) (ρ' : Env Γ),
      c1E.eval ρ' = h.chall.1 → (stepC c1E qE).eval ρ' = h.step (qE.eval ρ'))
    {Γ : List (Ty S)}
    (stE : Expr OO Γ (hop2StTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
    (argE : Expr OO Γ (.prod .bool (.base .ct))) (ρ : Env Γ)
    (gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (Q : Party) (c : Bytes)
    (hBound : SMStateBounded K gs) (hlazy : aux.lazy.length ≤ K) (hmade : aux.made.length ≤ K + 1)
    (hB_u : ∀ rc st' t' i' m',
      (sessionSchemeU P ℓ).receive (gs.st Q) c rc = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hB_dh : ∀ rc rk2 ckR ckS st' t' i' m',
      finishHop2DH P ℓ (gs.st Q) c rc rk2 ckR ckS = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hst : stE.eval ρ = hop2StEnc (PQC := PQC) (gs, aux) h.chall)
    (harg : argE.eval ρ = (partyEnc Q, c)) :
    Prod.map (Option.map SM.smRrDec) (hop2StDec (PQC := PQC)) <$>
      (hop2DeliverC P ℓ Dh encPt encT decT s K B h.k (spkDrawBv P ℓ Dh encPt encT decT s) stepC
        stE argE).eval ρ =
      (CryptoVerification.E2E.hop2Deliver (ℓ := ℓ) P Dh encT decT s h (Q, c)).run (gs, aux) := by
  unfold hop2DeliverC CryptoVerification.E2E.hop2Deliver
  rw [eval_bind_ret]
  have h0 : (Expr.pair stE argE).eval ρ =
      (hop2StEnc (PQC := PQC) (gs, aux) h.chall, partyEnc Q, c) := by
    simp [Expr.eval, hst, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod (hop2StTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
    (.prod .bool (.base .ct)) : Ty S))
    (hop2StEnc (PQC := PQC) (gs, aux) h.chall, partyEnc Q, c) ρ
  rw [eval_ite]
  have hWin : (gsWin (.fst (.fst (Expr.v0 (O := OO))))).eval ρ₁ = gs.win := rfl
  rw [hWin]
  by_cases hwin : gs.win
  · simp [ρ₁, hwin, Comp.eval, StateT.run_bind, StateT.run_get, StateT.run_pure,
      Prod.map, Expr.eval, Expr.v0]
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte, eval_caseOpt, Expr.eval_liftL,
      StateT.run_bind, StateT.run_get, pure_bind]
    have hTrans : (inTransitE K (.fst (.fst .v0))
        (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) : Expr OSM _ (.opt recTy)).eval ρ₁ =
        (gs.inTransit Q.other c).map recEnc := by
      refine inTransitE_eval K (.fst (.fst .v0)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
        ρ₁ gs Q.other eqCt_bytes_eq hBound.trans_le rfl ?_
      simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0]
    rw [hTrans]
    rcases gs.inTransit Q.other c with _ | r
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [Option.map_some, eval_bind, spkDrawBv_eval, hop2Unif,
        stateT_run_lift_bind, map_bind]
      refine bind_congr fun rc => ?_
      set ρ₂ := Env.cons (t := (.base .rcoins : Ty S)) rc
        (Env.cons (t := recTy) (recEnc r) ρ₁)
      have hstQ : (pGet (gsSt (.fst (.fst (Expr.v2 (O := OO))))) (.fst (.snd .v2))).eval ρ₂ =
          gs.st Q := by
        cases Q <;> rfl
      have hrec := hop2RecvC_eval_at P ℓ Dh encPt encT decT s K B h stepC hStep
        (.fst (.snd (.fst .v2))) (.snd (.snd (.fst .v2)))
        (pGet (gsSt (.fst (.fst .v2))) (.fst (.snd .v2))) (.snd (.snd .v2)) .v0
        ρ₂ gs aux (gs.st Q) c rc hlazy hmade (hB_u rc) (hB_dh rc) rfl rfl hstQ rfl rfl
      rw [StateT.run_bind, ← hrec, bind_map_left]
      refine bind_congr fun ⟨outRaw, aux2⟩ => ?_
      rcases outRaw with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
      · rw [eval_caseOpt_fst_v0_none]
        simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec, SM.smRrDec,
          hop2StDec, hop2StEnc, Expr.eval, Expr.v0, Expr.v3]
      · rw [eval_caseOpt_fst_v0_some]
        set ρ₃ := Env.cons (t := .prod (hop2OutTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
          (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
          (some ((st', t', i', m'), uOpt), aux2) ρ₂
        set ρ₄ := Env.cons (t := .prod (hop2RecvResTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
          (.opt (hop2UpdTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))))
          ((st', t', i', m'), uOpt) ρ₃
        have hAcc : (acceptE K (.fst (.fst (Expr.v4 (O := OO)))) (.fst (.snd .v4))
            (.fst (.fst .v0)) (recPos .v3)).eval ρ₄ = gsEnc (gs.accept Q st' r.pos) :=
          acceptE_eval K (.fst (.fst (Expr.v4 (O := OO)))) (.fst (.snd .v4))
            (.fst (.fst .v0)) (recPos .v3)
            ρ₄ gs Q r.pos hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl rfl
        have hChall : (challContainsE K (.fst (.fst (Expr.v4 (O := OO))))
            (recPos .v3)).eval ρ₄ = gs.chall.contains r.pos :=
          challContainsE_eval K (.fst (.fst (Expr.v4 (O := OO)))) (recPos .v3)
            ρ₄ gs r.pos hBound.chall_le rfl rfl
        have hCom : (hop2CommitE (.snd (Expr.v1 (O := OO))) (.fst (.snd .v4))
            (.snd .v0)).eval ρ₄ =
            hop2AuxEnc (PQC := PQC) (ℓ := ℓ) (hop2Commit (hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2) Q
              (uOpt.map (hop2UpdDec (PQC := PQC) (ℓ := ℓ)))) := by
          refine hop2CommitE_eval (PQC := PQC) (ℓ := ℓ) (.snd .v1) (.fst (.snd .v4)) (.snd .v0)
            ρ₄ (hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2) Q uOpt ?_ rfl rfl
          simp [ρ₄, ρ₃, Expr.eval, Expr.v1]
        have hBad : (orE (auxBad (.snd (Expr.v1 (O := OO))))
            (opBadAt P ℓ Dh encPt encT decT s (opSpkSc P ℓ Dh encPt encT decT s)
              (pGet (gsSt (.fst (.fst .v4))) (.fst (.snd .v4))) (.snd (.snd .v4)))).eval ρ₄ =
            ((hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2).bad || hop2BadAt P s (gs.st Q) c) := by
          rw [orE_eval]
          have h1 : (auxBad (.snd (Expr.v1 (O := OO)))).eval ρ₄ =
              (hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2).bad := rfl
          have h2 : (opBadAt P ℓ Dh encPt encT decT s (opSpkSc P ℓ Dh encPt encT decT s)
              (pGet (gsSt (.fst (.fst .v4))) (.fst (.snd .v4))) (.snd (.snd .v4))).eval ρ₄ =
              hop2BadAt P s (gs.st Q) c := by
            rw [opBadAt_eval]
            cases Q <;> rfl
          rw [h1, h2]
        have hAuxFin : hop2AuxDec (PQC := PQC) (ℓ := ℓ)
            ((auxSetBad (hop2CommitE (.snd (Expr.v1 (O := OO))) (.fst (.snd .v4)) (.snd .v0))
              (orE (auxBad (.snd .v1))
                (opBadAt P ℓ Dh encPt encT decT s (opSpkSc P ℓ Dh encPt encT decT s)
                  (pGet (gsSt (.fst (.fst .v4))) (.fst (.snd .v4)))
                  (.snd (.snd .v4))))).eval ρ₄) =
            { hop2Commit (hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2) Q
                (uOpt.map (hop2UpdDec (PQC := PQC) (ℓ := ℓ))) with
              bad := (hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2).bad || hop2BadAt P s (gs.st Q) c } :=
          hop2AuxDec_auxSetBad (PQC := PQC) (ℓ := ℓ) _ _ ρ₄ _ _ hCom hBad
        dsimp only [hop2OutDec, Option.map, Prod.map, id_eq]
        simp only [eval_ret, pair_eval, some_eval, inr_eval, ite_eval, hAcc, hChall,
          StateT.run_get, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure, Prod.map, Option.map, SM.smRrDec, hop2StDec, gsDec_gsEnc, hAuxFin]
        rfl

theorem hop2InjectC_eval_at (h : Hop2Hyb Pt)
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO II Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr OO Γ (.base .rcoins)) (qE : Expr OO Γ (.base .key)) (ρ' : Env Γ),
      c1E.eval ρ' = h.chall.1 → (stepC c1E qE).eval ρ' = h.step (qE.eval ρ'))
    {Γ : List (Ty S)}
    (stE : Expr OO Γ (hop2StTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
    (argE : Expr OO Γ (.prod .bool (.base .ct))) (ρ : Env Γ)
    (gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (Q : Party) (c : Bytes)
    (hBound : SMStateBounded K gs) (hlazy : aux.lazy.length ≤ K) (hmade : aux.made.length ≤ K + 1)
    (hB_u : ∀ rc st' t' i' m',
      (sessionSchemeU P ℓ).receive (gs.st Q) c rc = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hB_dh : ∀ rc rk2 ckR ckS st' t' i' m',
      finishHop2DH P ℓ (gs.st Q) c rc rk2 ckR ckS = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (hst : stE.eval ρ = hop2StEnc (PQC := PQC) (gs, aux) h.chall)
    (harg : argE.eval ρ = (partyEnc Q, c)) :
    Prod.map (Option.map SM.smRrDec) (hop2StDec (PQC := PQC)) <$>
      (hop2InjectC P ℓ Dh encPt encT decT s K B qep h.k (spkDrawBv P ℓ Dh encPt encT decT s) stepC
        stE argE).eval ρ =
      (CryptoVerification.E2E.hop2Inject (ℓ := ℓ) P Dh encT decT qep s h (Q, c)).run (gs, aux) := by
  unfold hop2InjectC CryptoVerification.E2E.hop2Inject
  rw [eval_bind_ret]
  have h0 : (Expr.pair stE argE).eval ρ =
      (hop2StEnc (PQC := PQC) (gs, aux) h.chall, partyEnc Q, c) := by
    simp [Expr.eval, hst, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod (hop2StTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
    (.prod .bool (.base .ct)) : Ty S))
    (hop2StEnc (PQC := PQC) (gs, aux) h.chall, partyEnc Q, c) ρ
  rw [eval_ite]
  have hRefuse : (orE (gsWin (.fst (.fst (Expr.v0 (O := OO)))))
      (orE (isSomeE ((inTransitE K (.fst (.fst .v0)) (otherE (.fst (.snd .v0)))
          (.snd (.snd .v0)) : Expr OSM _ (.opt recTy)).liftL))
        (orE (.not (safeInjE 3 (.fst (.fst .v0))))
          (.not (opInjOK P ℓ Dh encPt encT decT s (.snd (.snd .v0))))))).eval ρ₁ =
      (gs.win || (gs.inTransit Q.other c).isSome || !gs.safeInj 3 ||
        !ratchetKeyAdmissible protoSignalCodec decT encT c) := by
    have hTrans : (inTransitE K (.fst (.fst .v0))
        (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) : Expr OSM _ (.opt recTy)).eval ρ₁ =
        (gs.inTransit Q.other c).map recEnc := by
      refine inTransitE_eval K (.fst (.fst .v0)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
        ρ₁ gs Q.other eqCt_bytes_eq hBound.trans_le rfl ?_
      simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0]
    simp only [orE_eval, isSomeE_eval, Expr.eval, Expr.eval_liftL, hTrans, Option.isSome_map]
    rw [safeInjE_eval 3 (.fst (.fst .v0)) ρ₁ gs rfl]
    simp [ρ₁, gsWin, gsEnc, hop2StEnc, opInjOK, spkLeakSessionOps, Ops.sum, spkLeakSessionSmOps, smOps,
      Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href : (gs.win || (gs.inTransit Q.other c).isSome || !gs.safeInj 3 ||
      !ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, href, ↓reduceIte,
      Comp.eval, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, eval_bind, spkDrawBv_eval, hop2Unif,
      map_bind]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [href, Bool.false_eq_true, ↓reduceIte]
    rw [stateT_run_lift_bind]
    refine bind_congr fun rc => ?_
    set ρ₂ := Env.cons (t := (.base .rcoins : Ty S)) rc ρ₁
    have hstQ : (pGet (gsSt (.fst (.fst (Expr.v1 (O := OO))))) (.fst (.snd .v1))).eval ρ₂ =
        gs.st Q := by
      cases Q <;> rfl
    have hrec := hop2RecvC_eval_at P ℓ Dh encPt encT decT s K B h stepC hStep
      (.fst (.snd (.fst .v1))) (.snd (.snd (.fst .v1)))
      (pGet (gsSt (.fst (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) .v0
      ρ₂ gs aux (gs.st Q) c rc hlazy hmade (hB_u rc) (hB_dh rc) rfl rfl hstQ rfl rfl
    rw [StateT.run_bind, ← hrec, bind_map_left]
    refine bind_congr fun ⟨outRaw, aux2⟩ => ?_
    rcases outRaw with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
    · rw [eval_caseOpt_fst_v0_none]
      simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, hop2OutDec, SM.smRrDec,
        hop2StDec, hop2StEnc, Expr.eval, Expr.v0, Expr.v2]
    · rw [eval_caseOpt_fst_v0_some]
      set ρ₃ := Env.cons (t := .prod (hop2OutTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
        (hop2AuxTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
        (some ((st', t', i', m'), uOpt), aux2) ρ₂
      set ρ₄ := Env.cons (t := .prod (hop2RecvResTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))
        (.opt (hop2UpdTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ))))
        ((st', t', i', m'), uOpt) ρ₃
      dsimp only [hop2OutDec, Option.map, Prod.map, id_eq]
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      have hBad : (orE (auxBad (.snd (Expr.v1 (O := OO))))
          (opBadAt P ℓ Dh encPt encT decT s (opSpkSc P ℓ Dh encPt encT decT s)
            (pGet (gsSt (.fst (.fst .v3))) (.fst (.snd .v3))) (.snd (.snd .v3)))).eval ρ₄ =
          ((hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2).bad || hop2BadAt P s (gs.st Q) c) := by
        rw [orE_eval]
        have h1 : (auxBad (.snd (Expr.v1 (O := OO)))).eval ρ₄ =
            (hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2).bad := rfl
        have h2 : (opBadAt P ℓ Dh encPt encT decT s (opSpkSc P ℓ Dh encPt encT decT s)
            (pGet (gsSt (.fst (.fst .v3))) (.fst (.snd .v3))) (.snd (.snd .v3))).eval ρ₄ =
            hop2BadAt P s (gs.st Q) c := by
          rw [opBadAt_eval]
          cases Q <;> rfl
        rw [h1, h2]
      let auxBadVal : Hop2Aux Pt :=
        { hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2 with
          bad := (hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2).bad || hop2BadAt P s (gs.st Q) c }
      have hAuxBad : (auxSetBad (.snd (Expr.v1 (O := OO)))
          (orE (auxBad (.snd .v1))
            (opBadAt P ℓ Dh encPt encT decT s (opSpkSc P ℓ Dh encPt encT decT s)
              (pGet (gsSt (.fst (.fst .v3))) (.fst (.snd .v3)))
              (.snd (.snd .v3))))).eval ρ₄ =
          hop2AuxEnc (PQC := PQC) (ℓ := ℓ) auxBadVal := by
        have := hop2AuxDec_auxSetBad (PQC := PQC) (ℓ := ℓ) (.snd (Expr.v1 (O := OO)))
          (orE (auxBad (.snd .v1))
            (opBadAt P ℓ Dh encPt encT decT s (opSpkSc P ℓ Dh encPt encT decT s)
              (pGet (gsSt (.fst (.fst .v3))) (.fst (.snd .v3)))
              (.snd (.snd .v3)))) ρ₄ (hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2)
          ((hop2AuxDec (PQC := PQC) (ℓ := ℓ) aux2).bad || hop2BadAt P s (gs.st Q) c)
          (by simp [ρ₄, ρ₃, Expr.eval, Expr.v1]) hBad
        rw [← hop2AuxEnc_hop2AuxDec ((auxSetBad _ _).eval ρ₄), this]
      have hgs3 : (Expr.fst (.fst (Expr.v3 (O := OO)))).eval ρ₄ = gsEnc gs := rfl
      rw [eval_ite]
      have hlt : (Expr.lt (.nat (qep + 1)) (.fst (.snd (.fst (Expr.v0 (O := OO)))))).eval ρ₄ =
          decide (qep + 1 < t') := rfl
      rw [hlt]
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, decide_true, ↓reduceIte, eval_ret, pair_eval, some_eval,
          hgs3, hAuxBad, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, map_pure, Prod.map, Option.map, SM.smRrDec, hop2StDec, gsDec_gsEnc,
          hop2AuxDec_hop2AuxEnc]
        rfl
      · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ite]
        have hpos : (Expr.pair (otherE (.fst (.snd (Expr.v3 (O := OO)))))
            (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))).eval ρ₄ =
            posEnc ⟨Q.other, t', i'⟩ := by
          simp [ρ₄, ρ₃, ρ₂, ρ₁, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0, Expr.v3]
        have htriv : (trivialE K 3 (.fst (.fst (Expr.v3 (O := OO))))
            (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0))))))).eval ρ₄ =
            gs.trivial 3 ⟨Q.other, t', i'⟩ :=
          trivialE_eval K 3 (.fst (.fst (Expr.v3 (O := OO)))) _ ρ₄ gs ⟨Q.other, t', i'⟩
            hBound.trans_le hBound.comp_le rfl hpos
        rw [htriv]
        by_cases ht : gs.trivial 3 ⟨Q.other, t', i'⟩
        · have hAcc : (acceptE K (.fst (.fst (Expr.v3 (O := OO)))) (.fst (.snd .v3))
              (.fst (.fst .v0))
              (.pair (otherE (.fst (.snd .v3)))
                (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0))))))).eval ρ₄ =
              gsEnc (gs.accept Q st' ⟨Q.other, t', i'⟩) :=
            acceptE_eval K (.fst (.fst (Expr.v3 (O := OO)))) (.fst (.snd .v3))
              (.fst (.fst .v0)) _ ρ₄ gs Q ⟨Q.other, t', i'⟩
              hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl hpos
          have hCom : (hop2CommitE
              (auxSetBad (.snd (Expr.v1 (O := OO)))
                (orE (auxBad (.snd .v1))
                  (opBadAt P ℓ Dh encPt encT decT s (opSpkSc P ℓ Dh encPt encT decT s)
                    (pGet (gsSt (.fst (.fst .v3))) (.fst (.snd .v3)))
                    (.snd (.snd .v3)))))
              (.fst (.snd .v3)) (.snd .v0)).eval ρ₄ =
              hop2AuxEnc (PQC := PQC) (ℓ := ℓ) (hop2Commit auxBadVal Q
                (uOpt.map (hop2UpdDec (PQC := PQC) (ℓ := ℓ)))) :=
            hop2CommitE_eval (PQC := PQC) (ℓ := ℓ) _ (.fst (.snd .v3)) (.snd .v0)
              ρ₄ auxBadVal Q uOpt hAuxBad rfl rfl
          simp only [ht, ↓reduceIte, eval_ret, pair_eval, some_eval, inr_eval, hAcc, hCom,
            StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
            Prod.map, Option.map, SM.smRrDec, hop2StDec, gsDec_gsEnc, hop2AuxDec_hop2AuxEnc]
          rfl
        · have hWinSet : (gsSetWin (.fst (.fst (Expr.v3 (O := OO)))) (.bool true)).eval ρ₄ =
              gsEnc { gs with win := true } :=
            gsSetWin_eval (.fst (.fst (Expr.v3 (O := OO)))) (.bool true) ρ₄ gs rfl
          simp only [ht, Bool.false_eq_true, ↓reduceIte, eval_ret, pair_eval, some_eval,
            hWinSet, hAuxBad, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, map_pure, Prod.map, Option.map, SM.smRrDec, hop2StDec, gsDec_gsEnc,
            hop2AuxDec_hop2AuxEnc]
          rfl

private theorem map_hop2Lift_canonComp {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (aux : Hop2Aux Pt) :
    Prod.map id (Prod.map canonComp id) <$> (hop2Lift (Pt := Pt) m).run (gs, aux) =
      (fun p => (p.1, (p.2, aux))) <$>
        (liftM (Prod.map id canonComp <$> m.run gs) : Hop2Comp Pt _) := by
  simp only [hop2Lift, StateT.run_mk, ← liftComp_eq_liftM,
    map_eq_bind_pure_comp, Function.comp_def, liftComp_bind, liftComp_pure,
    bind_assoc, pure_bind, Prod.map, id_eq]

private theorem hop2Lazy_run_eq_map (t : ℕ) (Q : Pt) (aux : Hop2Aux Pt) :
    ∃ m : Hop2Comp Pt (BitVec 256 × Hop2Aux Pt),
      ∀ gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes,
        (hop2Lazy (ℓ := ℓ) t Q).run (gs, aux) = (fun p => (p.1, (gs, p.2))) <$> m := by
  cases hlk : aux.lazy.lookup (t, Q) with
  | some u =>
    refine ⟨pure (u, aux), fun gs => ?_⟩
    simp [hop2Lazy, hlk, StateT.run_bind, StateT.run_get, StateT.run_pure]
  | none =>
    refine ⟨(fun u => (u, { aux with lazy := ((t, Q), u) :: aux.lazy })) <$> hop2Unif (Pt := Pt),
      fun gs => ?_⟩
    simp only [hop2Lazy, hlk, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
      StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private theorem hop2RecvHalf_run_eq_map (h : Hop2Hyb Pt) (idx : Option ℕ) (rk : Ratchet.RootKey)
    (their : PublicKey) (our : PrivateKey) (Q : Pt) (aux : Hop2Aux Pt) :
    ∃ m : Hop2Comp Pt (Option (Option ℕ × Ratchet.RootKey × BitVec 256) × Hop2Aux Pt),
      ∀ gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes,
        (hop2RecvHalf (ℓ := ℓ) P h idx rk their our Q).run (gs, aux) =
          (fun p => (p.1, (gs, p.2))) <$> m := by
  unfold hop2RecvHalf
  cases idx with
  | none =>
    cases hrc : rootCreateChain P.C rk their our with
    | error _ => exact ⟨pure (none, aux), fun gs => by simp [StateT.run_pure]⟩
    | ok pr => exact ⟨pure (some (none, pr.1, pr.2.key), aux), fun gs => by simp [StateT.run_pure]⟩
  | some t =>
    by_cases hQ : Q = 0
    · exact ⟨pure (none, aux), fun gs => by simp [hQ, StateT.run_pure]⟩
    · simp only [hQ, ↓reduceIte]
      by_cases htk : t ≤ h.k
      · simp only [htk, ↓reduceIte]
        cases hmk : aux.made.lookup (t, Q) with
        | some ck =>
          exact ⟨pure (some (some (t + 1), 0, ck), aux), fun gs => by
            simp [hmk, StateT.run_bind, StateT.run_get, StateT.run_pure]⟩
        | none =>
          obtain ⟨m₀, hm₀⟩ := hop2Lazy_run_eq_map (ℓ := ℓ) t Q aux
          refine ⟨(fun p => (let (rk', ck) := Ratchet.rootExpand P.C.F (keyToBytes32 p.1);
              some (none, rk', ck), p.2)) <$> m₀, fun gs => ?_⟩
          simp only [hmk, StateT.run_bind, StateT.run_get, StateT.run_pure, hm₀ gs,
            map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      · refine ⟨(fun u => (let (rk', ck) := Ratchet.rootExpand P.C.F (keyToBytes32 u);
            some (none, rk', ck), aux)) <$> h.step Q, fun gs => ?_⟩
        simp only [htk, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private theorem hop2DH_run_eq_map (h : Hop2Hyb Pt) (idx : Option ℕ) (coins : BitVec 256)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256) (aux : Hop2Aux Pt) :
    ∃ m : Hop2Comp Pt (Hop2Out Pt ℓ × Hop2Aux Pt),
      ∀ gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes,
        (hop2DH (ℓ := ℓ) P Dh encT decT h idx coins g msg rc).run (gs, aux) =
          (fun p => (p.1, (gs, p.2))) <$> m := by
  unfold hop2DH
  cases decT msg.senderRatchetKey with
  | none => exact ⟨pure (none, aux), fun gs => by simp [StateT.run_pure]⟩
  | some T =>
    dsimp only
    by_cases hbad : T = 0 ∨ encT T ≠ msg.senderRatchetKey
    · exact ⟨pure (none, aux), fun gs => by simp [hbad, StateT.run_pure]⟩
    · simp only [hbad, ↓reduceIte]
      cases g.session.senderChain with
      | none => exact ⟨pure (none, aux), fun gs => by simp [StateT.run_pure]⟩
      | some sc =>
        dsimp only
        obtain ⟨m₁, hm₁⟩ := hop2RecvHalf_run_eq_map P ℓ h idx g.session.rootKey
          msg.senderRatchetKey sc.ratchetKey.privateKey (Dh.dh coins T) aux
        let newKey := KeyPair.generate P.C rc
        let cont : Option (Option ℕ × Ratchet.RootKey × BitVec 256) → Hop2Aux Pt →
            Hop2Comp Pt (Hop2Out Pt ℓ × Hop2Aux Pt)
          | none, aux' => pure (none, aux')
          | some (idx1, rkM, ckR), aux' => do
            let out2 ← hop2SendHalf P h idx1 rkM msg.senderRatchetKey newKey.privateKey (Dh.dh rc T)
            match out2 with
            | none => pure (none, aux')
            | some (idx2, rk2, ckS, pend) =>
              let cur := sc.chainKey.index
              let sess' : SessionState Bytes :=
                { g.session with
                  previousCounter := if cur = 0 then 0 else cur - 1
                  rootKey := rk2
                  receiverChains := RatchetState.evictReceiverChains
                    (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                  senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
              match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg
                  .whisper rc sess' with
              | (.error _, _) => pure (none, aux')
              | (.ok m, s_out) =>
                let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
                  ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
                pure (some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
                  g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m),
                  some ⟨idx2, rc, pend⟩), aux')
        refine ⟨m₁ >>= fun p => cont p.1 p.2, fun gs => ?_⟩
        simp only [StateT.run_bind, hm₁ gs, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
          pure_bind]
        refine bind_congr fun ⟨r1, aux'⟩ => ?_
        cases r1 with
        | none => simp [cont, StateT.run_pure]
        | some trip =>
          rcases trip with ⟨idx1, rkM, ckR⟩
          simp only [cont, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
          refine bind_congr fun out2 => ?_
          cases out2 with
          | none => simp [StateT.run_pure]
          | some quad =>
            rcases quad with ⟨idx2, rk2, ckS, pend⟩
            dsimp only
            rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg
                .whisper rc _ with ⟨_ | m, s_out⟩ <;>
              simp [StateT.run_pure]

private theorem hop2Recv_run_eq_map (h : Hop2Hyb Pt) (g : GhostState Bytes) (c : Bytes)
    (rc : BitVec 256) (aux : Hop2Aux Pt) :
    ∃ m : Hop2Comp Pt (Hop2Out Pt ℓ × Hop2Aux Pt),
      ∀ gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes,
        (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run (gs, aux) =
          (fun p => (p.1, (gs, p.2))) <$> m := by
  unfold hop2Recv
  cases SignalMessage.tryFrom P.codec c with
  | error _ => exact ⟨pure (none, aux), fun gs => by simp [StateT.run_pure]⟩
  | ok msg =>
    dsimp only
    cases hidx : aux.idx g.party with
    | none =>
      refine ⟨pure (((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none)), aux),
        fun gs => ?_⟩
      simp [StateT.run_bind, StateT.run_get, StateT.run_pure, hidx]
    | some t =>
      by_cases hneed : (g.session.receiverChains.findIdx?
          (·.senderRatchetKey == msg.senderRatchetKey)).isNone
      · obtain ⟨m₀, hm₀⟩ := hop2DH_run_eq_map P ℓ Dh encT decT h (some t) (aux.coins g.party)
          g msg rc aux
        refine ⟨m₀, fun gs => ?_⟩
        simp [StateT.run_bind, StateT.run_get, hidx, hneed, hm₀ gs]
      · refine ⟨pure (((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none)), aux),
          fun gs => ?_⟩
        simp [StateT.run_bind, StateT.run_get, StateT.run_pure, hidx, hneed]

def hop2ImplDedup (h : Hop2Hyb Pt) :
    QueryImpl (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (Hop2M Pt ℓ)
  | .inl u => StateT.lift (query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl u))
  | .inr (.inl (.inl (.inl (.inl y)))) =>
    hop2Lift (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y)
  | .inr (.inl (.inl (.inl (.inr y)))) =>
    hop2Lift (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y)
  | .inr (.inl (.inl (.inr y))) => CryptoVerification.E2E.hop2Deliver P Dh encT decT s h y
  | .inr (.inl (.inr y)) => CryptoVerification.E2E.hop2Inject P Dh encT decT qep s h y
  | .inr (.inr y) => hop2Lift (corrRDedup (configRefuseEarlyBobCorr decT encT) y)

theorem map_canonComp_simulateQ_hop2ImplDedup_eq (h : Hop2Hyb Pt) {α : Type}
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) α)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) :
    Prod.map id (Prod.map canonComp id) <$>
        (simulateQ (hop2ImplDedup P ℓ Dh encT decT s qep h) oa).run st =
      Prod.map id (Prod.map canonComp id) <$>
        (simulateQ (hop2Impl P Dh encT decT qep s h) oa).run st := by
  have hSendOK : ∀ st' Q,
      (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := CBC.Plain ℓ)
        decT encT).sendOK (canonComp st') Q =
        (configRefuseEarlyBobCorr decT encT).sendOK st' Q := fun _ _ => rfl
  have hCorrOK : ∀ st' Q,
      (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := CBC.Plain ℓ)
        decT encT).corrOK (canonComp st') Q =
        (configRefuseEarlyBobCorr decT encT).corrOK st' Q := fun _ _ => rfl
  have hDel : ∀ y (gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (aux : Hop2Aux Pt),
      Prod.map id (Prod.map canonComp id) <$>
          (CryptoVerification.E2E.hop2Deliver (ℓ := ℓ) P Dh encT decT s h y).run (gs, aux) =
        Prod.map id (Prod.map canonComp id) <$>
          (CryptoVerification.E2E.hop2Deliver (ℓ := ℓ) P Dh encT decT s h y).run
            (canonComp gs, aux) := by
    rintro ⟨Q, c⟩ gs aux
    unfold CryptoVerification.E2E.hop2Deliver
    simp only [StateT.run_bind, StateT.run_get, pure_bind, canonComp_inTransit]
    have hw : (canonComp gs).win = gs.win := rfl
    rw [hw]
    split_ifs
    · simp [Prod.map, canonComp_idem]
    · cases gs.inTransit Q.other c with
      | none => simp [Prod.map, canonComp_idem]
      | some r =>
        simp only [stateT_run_lift_bind, map_bind]
        refine bind_congr fun rc => ?_
        have hst : (canonComp gs).st Q = gs.st Q := rfl
        rw [hst]
        obtain ⟨m₀, hm₀⟩ := hop2Recv_run_eq_map P ℓ Dh encT decT h (gs.st Q) c rc aux
        simp only [StateT.run_bind, hm₀ gs, hm₀ (canonComp gs),
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun ⟨out, aux'⟩ => ?_
        cases out with
        | none => simp [StateT.run_pure, Prod.map, canonComp_idem]
        | some pr =>
          rcases pr with ⟨⟨st'', t', i', m'⟩, u⟩
          have hch : (canonComp gs).chall = gs.chall := rfl
          simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
            pure_bind, Prod.map, canonComp_accept, canonComp_idem]
          rw [hch]
  have hInj : ∀ y (gs : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (aux : Hop2Aux Pt),
      Prod.map id (Prod.map canonComp id) <$>
          (CryptoVerification.E2E.hop2Inject (ℓ := ℓ) P Dh encT decT qep s h y).run (gs, aux) =
        Prod.map id (Prod.map canonComp id) <$>
          (CryptoVerification.E2E.hop2Inject (ℓ := ℓ) P Dh encT decT qep s h y).run
            (canonComp gs, aux) := by
    rintro ⟨Q, c⟩ gs aux
    unfold CryptoVerification.E2E.hop2Inject
    simp only [StateT.run_bind, StateT.run_get, pure_bind, canonComp_inTransit, canonComp_safeInj]
    have hw : (canonComp gs).win = gs.win := rfl
    rw [hw]
    by_cases href : (gs.win || (gs.inTransit Q.other c).isSome || !gs.safeInj 3 ||
        !ratchetKeyAdmissible protoSignalCodec decT encT c)
    · simp [href, Prod.map, canonComp_idem]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, stateT_run_lift_bind, map_bind]
      refine bind_congr fun rc => ?_
      have hst : (canonComp gs).st Q = gs.st Q := rfl
      rw [hst]
      obtain ⟨m₀, hm₀⟩ := hop2Recv_run_eq_map P ℓ Dh encT decT h (gs.st Q) c rc aux
      simp only [StateT.run_bind, hm₀ gs, hm₀ (canonComp gs),
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨out, aux'⟩ => ?_
      cases out with
      | none => simp [StateT.run_pure, Prod.map, canonComp_idem]
      | some pr =>
        rcases pr with ⟨⟨st'', t', i', m'⟩, u⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        by_cases hqep : qep + 1 < t'
        · simp [hqep, StateT.run_set, Prod.map, canonComp_idem]
        · simp only [hqep, ↓reduceIte, canonComp_trivial]
          cases gs.trivial 3 ⟨Q.other, t', i'⟩ <;>
            simp [StateT.run_set, Prod.map,
              canonComp_accept, canonComp_setWin, canonComp_idem]
  refine map_run_simulateQ_eq_of_idem_proj
    (hop2ImplDedup P ℓ Dh encT decT s qep h)
    (hop2Impl P Dh encT decT qep s h) (Prod.map canonComp id) ?_ ?_ oa rfl
  · rintro (u | (((y | y) | y) | y) | Q) ⟨gs, aux⟩
    · simp [hop2ImplDedup, hop2Impl, StateT.run_lift, Prod.map, canonComp_idem]
    · dsimp only [hop2ImplDedup, hop2Impl, Prod.map, id_eq]
      rw [map_hop2Lift_canonComp, map_hop2Lift_canonComp,
          map_canonComp_transmitR _ _ _ _ hSendOK]
    · dsimp only [hop2ImplDedup, hop2Impl, Prod.map, id_eq]
      rw [map_hop2Lift_canonComp, map_hop2Lift_canonComp,
          map_canonComp_challR _ _ _ _ hSendOK]
    · exact hDel y gs aux
    · exact hInj y gs aux
    · dsimp only [hop2ImplDedup, hop2Impl, Prod.map, id_eq]
      rw [map_hop2Lift_canonComp, map_hop2Lift_canonComp,
          map_canonComp_corrRDedup _ hCorrOK]
  · rintro (u | (((y | y) | y) | y) | Q) ⟨gs, aux⟩
    · simp [hop2Impl, StateT.run_lift, Prod.map, canonComp_idem]
    · dsimp only [hop2Impl, Prod.map, id_eq]
      rw [map_hop2Lift_canonComp, map_hop2Lift_canonComp,
          map_canonComp_transmitR _ _ _ _ hSendOK]
    · dsimp only [hop2Impl, Prod.map, id_eq]
      rw [map_hop2Lift_canonComp, map_hop2Lift_canonComp,
          map_canonComp_challR _ _ _ _ hSendOK]
    · exact hDel y gs aux
    · exact hInj y gs aux
    · dsimp only [hop2Impl, Prod.map, id_eq]
      rw [map_hop2Lift_canonComp, map_hop2Lift_canonComp,
          map_canonComp_corrR _ hCorrOK]

set_option maxHeartbeats 800000 in
theorem hop2GameRedProg_eval_of_le (k qAdv : ℕ)
    (hK : qAdv * qAdv ≤ K * K) (hqB : qAdv ≤ B) (h32B : 2 ^ 32 ≤ B)
    {rIn : Ty S}
    (initChall : Comp OO II [rIn] (hop2ChallTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)))
    (stepC : ∀ {Γ}, Expr OO Γ (.base .rcoins) → Expr OO Γ (.base .key) →
      Comp OO II Γ (.base .rcoins))
    (step : Ratchet.RootKey × BitVec 256 → Pt → Hop2Comp Pt (BitVec 256))
    (hStep : ∀ (chall : Ratchet.RootKey × BitVec 256) {Γ}
      (c1E : Expr OO Γ (.base .rcoins)) (qE : Expr OO Γ (.base .key)) (ρ' : Env Γ),
      c1E.eval ρ' = chall.1 → (stepC c1E qE).eval ρ' = step chall (qE.eval ρ'))
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
    (hA : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)) qAdv)
    (xIn : rIn.denote) :
    (hop2GameRedProg P ℓ Dh encPt encT decT s K B qep k
      (spkDrawBool P ℓ Dh encPt encT decT s) (spkDrawCoins ℓ (PQC := PQC))
      (spkDrawBv P ℓ Dh encPt encT decT s) initChall stepC).eval (fun _ => A) xIn =
      (do
        let chall ← initChall.eval (.cons xIn .nil)
        hop2Game P ℓ Dh encT decT qep s ⟨k, chall, step chall⟩ A) := by
  simp only [CostedReduction.eval, hop2GameRedProg, eval_bind, bind_assoc]
  refine bind_congr fun chall => ?_
  let h : Hop2Hyb Pt := ⟨k, chall, step chall⟩
  let R : CostedReduction OO II (SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (e2eCodec Pt ℓ PQC)
      (hop2ChallTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)) .unit .bool .bool :=
    hop2GameRedProg P ℓ Dh encPt encT decT s K B qep k
      (spkDrawBool P ℓ Dh encPt encT decT s) (spkDrawCoins ℓ (PQC := PQC))
      (spkDrawBv P ℓ Dh encPt encT decT s) (.ret .v0) stepC
  change R.eval (fun _ => A) chall = hop2Game P ℓ Dh encT decT qep s h A
  let abs : R.σ.denote →
      SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt :=
    hop2StDec (PQC := PQC)
  let Inv : ℕ → R.σ.denote → Prop :=
    fun q v => Hop2BudgetInv (Pt := Pt) (ℓ := ℓ) qAdv K q
      (hop2StDec (PQC := PQC) v) ∧
      StateGhostBounded (qAdv - q) (hop2StDec (PQC := PQC) v).1 ∧ v.2.2 = chall
  let initImpl : (Ratchet.RootKey × BitVec 256) →
      Hop2Comp Pt (Unit × (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt)) :=
    fun ch => do
      let b ← (liftM ($ᵗ Bool : ProbComp Bool) : Hop2Comp Pt Bool)
      let ck0 ← hop2Unif (Pt := Pt)
      let x ← hop2Unif (Pt := Pt)
      let alice ← hop2Unif (Pt := Pt)
      let pqr ← hop2Unif (Pt := Pt)
      let u1 ← hop2Unif (Pt := Pt)
      let ck1 := if k = 0 then ch.2 else u1
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
      return ((), (initSt, aux0))
  let finishImpl : (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) →
      Bool → Hop2Comp Pt Bool :=
    fun fin _ => pure fin.2.bad
  have hinit_both := hop2InitAfterChallC_eval P ℓ Dh encPt encT decT s k
    .v0 (.cons chall (.cons chall .nil)) chall rfl
  have hinit : (Prod.map id abs <$> R.init.eval (.cons chall .nil)) = initImpl chall := by
    simp only [R, hop2GameRedProg, eval_bind_ret]
    exact hinit_both.1
  have hinitInv : ∀ r ∈ support (R.init.eval (.cons chall .nil)), Inv qAdv r.2 := by
    intro r hr
    have hch : r.2.2.2 = chall := by
      simp only [R, hop2GameRedProg, eval_bind_ret] at hr
      exact hinit_both.2 r hr
    have hmem : (r.1, abs r.2) ∈ support (Prod.map id abs <$> R.init.eval (.cons chall .nil)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨r, hr, rfl⟩
    rw [hinit] at hmem
    simp only [initImpl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨b, -, ck0, -, x, -, alice, -, pqr, -, u1, -, hmem⟩
    have habs : abs r.2 = _ := (Prod.ext_iff.mp hmem).2
    refine ⟨?_, ?_, hch⟩
    · change Hop2BudgetInv ℓ qAdv K qAdv (abs r.2)
      rw [habs]
      exact Hop2BudgetInv.init ℓ hK _ b _ _ alice x
    · change StateGhostBounded (qAdv - qAdv) (abs r.2).1
      rw [Nat.sub_self, habs]
      intro Q; cases Q
      · exact ghostBounded_e2eInitA P (0, ck0, x, alice, pqr, if k = 0 then chall.2 else u1)
      · exact ghostBounded_initB P _
  have hU : ∀ (n : ℕ) (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt),
      (hop2ImplDedup P ℓ Dh encT decT s qep h (.inl n)).run st =
        (StateT.lift ((e2ePrfIface Pt ℓ PQC).fwdU n)).run st := fun _ _ => rfl
  have hstep : ∀ m t v, Inv (m + 1) v →
      (Prod.map id abs <$> ((R.impl (.inr t)).run v)) =
        (hop2ImplDedup P ℓ Dh encT decT s qep h (.inr t)).run (abs v) ∧
      ∀ r ∈ support ((R.impl (.inr t)).run v), Inv m r.2 := by
    dsimp only [R, CostedReduction.impl, handlerImpl, hop2GameRedProg, abs, Inv]
    intro m t v ⟨hv, hgb, hv_ch⟩
    set st := hop2StDec (PQC := PQC) v
    have hv_enc : v = hop2StEnc (PQC := PQC) st h.chall := by
      change v = hop2StEnc (PQC := PQC) (hop2StDec (PQC := PQC) v) chall
      rw [← hv_ch, hop2StEnc_hop2StDec]
    have hBound : SMStateBounded K st.1 := hv.sm.toBounded
    have hlazy : st.2.lazy.length ≤ K := hv.lazy_len_le
    have hmade : st.2.made.length ≤ K + 1 := hv.made_len_le
    have hm_le : m + 1 ≤ qAdv := by have := hv.sm.trans_le; omega
    have hsub : qAdv - (m + 1) + 1 ≤ qAdv - m := by omega
    have hB_u : ∀ Q c rc st' t' i' m',
        (sessionSchemeU P ℓ).receive (st.1.st Q) c rc = some (st', t', i', m') →
          t' ≤ B ∧ i' ≤ B := by
      intro Q c rc st' t' i' m' hrec
      obtain ⟨-, ht, hi⟩ :=
        ghostBounded_receive_sessionSchemeU P (st.1.st Q) c rc st' t' i' m' (hgb Q) hrec
      exact ⟨by omega, le_trans hi h32B⟩
    have hB_dh : ∀ Q c rc rk2 ckR ckS st' t' i' m',
        finishHop2DH P ℓ (st.1.st Q) c rc rk2 ckR ckS = some (st', t', i', m') →
          t' ≤ B ∧ i' ≤ B := by
      intro Q c rc rk2 ckR ckS st' t' i' m' hfin
      obtain ⟨-, ht, hi⟩ :=
        ghostBounded_finishHop2DH P (st.1.st Q) c rc rk2 ckR ckS st' t' i' m' (hgb Q) hfin
      exact ⟨by omega, le_trans hi h32B⟩
    have hCfg := configSpkS_agrees (PQC := PQC) P ℓ encT decT K
    have hCoins : ∀ {Γ} (ρ' : Env Γ),
        (spkDrawCoins ℓ (Pt := Pt) (PQC := PQC) (O' := OSM) (Γ := Γ)).eval ρ' =
          some <$> (e2ePrfIface Pt ℓ PQC).liftP ($ᵗ PQC : ProbComp PQC) :=
      fun ρ' => spkDrawCoins_eval ℓ ρ'
    have hStep' : ∀ {Γ} (c1E : Expr OO Γ (.base .rcoins)) (qE : Expr OO Γ (.base .key))
        (ρ' : Env Γ), c1E.eval ρ' = h.chall.1 → (stepC c1E qE).eval ρ' = h.step (qE.eval ρ') :=
      fun c1E qE ρ' hc1 => hStep chall c1E qE ρ' hc1
    have hstep_ch : ∀ t',
        (Prod.map id (hop2StDec (PQC := PQC)) <$>
          ((StateT.mk fun s_1 : (hop2StTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote => do
          let p ← (hop2ImplC P ℓ Dh encPt encT decT s K B qep k (spkDrawCoins ℓ (PQC := PQC))
            (spkDrawBv P ℓ Dh encPt encT decT s) stepC .v0 .v1).eval
            (.cons s_1 (.cons ((e2eCodec Pt ℓ PQC).qenc t') .nil))
          pure ((e2eCodec Pt ℓ PQC).rdec t' p.1, p.2)).run v)) =
          (hop2ImplDedup P ℓ Dh encT decT s qep h (.inr t')).run st ∧
        ∀ r ∈ support ((StateT.mk fun s_1 : (hop2StTy (Pt := Pt) (PQC := PQC) (ℓ := ℓ)).denote => do
          let p ← (hop2ImplC P ℓ Dh encPt encT decT s K B qep k (spkDrawCoins ℓ (PQC := PQC))
            (spkDrawBv P ℓ Dh encPt encT decT s) stepC .v0 .v1).eval
            (.cons s_1 (.cons ((e2eCodec Pt ℓ PQC).qenc t') .nil))
          pure ((e2eCodec Pt ℓ PQC).rdec t' p.1, p.2)).run v), r.2.2.2 = chall := by
      intro t'
      simp only [hop2ImplC, StateT.run_mk, eval_bind_ret]
      rcases t' with (((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q
      · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v4, Expr.v5,
          Env.get_cons_zero, Env.get_cons_succ, Comp.eval_liftL, bind_assoc, pure_bind]
        refine ⟨?_, ?_⟩
        · rw [transmitRC_eval (I := II) (sessionSchemeUPt P ℓ) 3 qep K
            (ConfigRC.spkS OSM) (configRefuseEarlyBobCorr decT encT) hCfg rfl
            (spkDrawCoins ℓ (PQC := PQC)) hCoins _ _ _ st.1 Q msg optR hBound
            (by rw [hv_enc]; rfl) rfl]
          dsimp only [hop2ImplDedup, hop2Lift, StateT.run_mk, e2eCodec, smCodec]
          simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
            Prod.map, id_eq, hop2StDec, gsDec_gsEnc]
          refine bind_congr fun x => ?_
          rw [hv_enc]; rfl
        · intro r hr
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
          obtain ⟨p, -, rfl⟩ := hr
          exact hv_ch
      · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v4, Expr.v5,
          Env.get_cons_zero, Env.get_cons_succ, Comp.eval_liftL, bind_assoc, pure_bind]
        refine ⟨?_, ?_⟩
        · rw [challRC_eval (I := II) (sessionSchemeUPt P ℓ) 3 qep K
            (ConfigRC.spkS OSM) (configRefuseEarlyBobCorr decT encT) hCfg rfl
            (spkDrawCoins ℓ (PQC := PQC)) hCoins _ _ _ st.1 Q m₀ m₁ optR hBound
            (by rw [hv_enc]; rfl) rfl]
          dsimp only [hop2ImplDedup, hop2Lift, StateT.run_mk, e2eCodec, smCodec]
          simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
            Prod.map, id_eq, hop2StDec, gsDec_gsEnc]
          refine bind_congr fun x => ?_
          rw [hv_enc]; rfl
        · intro r hr
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
          obtain ⟨p, -, rfl⟩ := hr
          exact hv_ch
      · dsimp only [e2eCodec, smCodec, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v3,
          Env.get_cons_zero, Env.get_cons_succ]
        simp only [bind_assoc, pure_bind]
        refine ⟨?_, ?_⟩
        · dsimp only [hop2ImplDedup]
          rw [map_bind_pure_fst (Option.map SM.smRrDec) (hop2StDec (PQC := PQC))]
          exact hop2DeliverC_eval_at P ℓ Dh encPt encT decT s K B h stepC hStep'
            (.fst .v3) .v0 _ st.1 st.2 Q c hBound hlazy hmade (hB_u Q c) (hB_dh Q c) hv_enc rfl
        · intro r hr
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
          obtain ⟨p, hp, rfl⟩ := hr
          exact (hop2DeliverC_chall P ℓ Dh encPt encT decT s K B k stepC
            (.fst .v3) .v0 _ p hp).trans hv_ch
      · dsimp only [e2eCodec, smCodec, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
          Env.get_cons_zero, Env.get_cons_succ]
        simp only [bind_assoc, pure_bind]
        refine ⟨?_, ?_⟩
        · dsimp only [hop2ImplDedup]
          rw [map_bind_pure_fst (Option.map SM.smRrDec) (hop2StDec (PQC := PQC))]
          exact hop2InjectC_eval_at P ℓ Dh encPt encT decT s K B qep h stepC hStep'
            (.fst .v2) .v0 _ st.1 st.2 Q c hBound hlazy hmade (hB_u Q c) (hB_dh Q c) hv_enc rfl
        · intro r hr
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
          obtain ⟨p, hp, rfl⟩ := hr
          exact (hop2InjectC_chall P ℓ Dh encPt encT decT s K B qep k stepC
            (.fst .v2) .v0 _ p hp).trans hv_ch
      · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
          Env.get_cons_zero, Env.get_cons_succ, Comp.eval_liftL, bind_assoc, pure_bind]
        refine ⟨?_, ?_⟩
        · rw [corrRC_eval (I := II) K (ConfigRC.spkS OSM) (configRefuseEarlyBobCorr decT encT)
            hCfg _ _ _ st.1 Q hBound (by rw [hv_enc]; rfl) rfl]
          dsimp only [hop2ImplDedup, hop2Lift, StateT.run_mk, e2eCodec, smCodec]
          simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
            Prod.map, id_eq, hop2StDec, gsDec_gsEnc]
          refine bind_congr fun x => ?_
          rw [hv_enc]; rfl
        · intro r hr
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
          obtain ⟨p, -, rfl⟩ := hr
          exact hv_ch
    obtain ⟨heq, hch⟩ := hstep_ch t
    refine ⟨heq, fun r hr => ⟨?_, ?_, hch r hr⟩⟩
    have hmem : (r.1, hop2StDec (PQC := PQC) r.2) ∈
        support ((hop2ImplDedup P ℓ Dh encT decT s qep h (.inr t)).run st) := by
      rw [← heq]
      simp only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨r, hr, rfl⟩
    · rcases t with (((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q
      · rw [hop2ImplDedup, mem_support_hop2Lift] at hmem
        obtain ⟨h1, h2⟩ := hmem
        have hsm' := hv.sm.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT)
          (Q, msg, optR) (r.1, (hop2StDec (PQC := PQC) r.2).1) h1
        have hl := hv.lazy_le
        have hm := hv.made_le
        exact ⟨hsm', by rw [h2]; omega, by rw [h2]; omega⟩
      · rw [hop2ImplDedup, mem_support_hop2Lift] at hmem
        obtain ⟨h1, h2⟩ := hmem
        have hsm' := hv.sm.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT)
          (Q, m₀, m₁, optR) (r.1, (hop2StDec (PQC := PQC) r.2).1) h1
        have hl := hv.lazy_le
        have hm := hv.made_le
        exact ⟨hsm', by rw [h2]; omega, by rw [h2]; omega⟩
      · exact hop2Deliver_inv P ℓ Dh encT decT s K h st Q c qAdv m hv
          (r.1, hop2StDec (PQC := PQC) r.2) hmem
      · exact hop2Inject_inv P ℓ Dh encT decT s K qep h st Q c qAdv m hv
          (r.1, hop2StDec (PQC := PQC) r.2) hmem
      · rw [hop2ImplDedup, mem_support_hop2Lift] at hmem
        obtain ⟨h1, h2⟩ := hmem
        have hsm' := hv.sm.corrRDedup (configRefuseEarlyBobCorr decT encT) Q
          (r.1, (hop2StDec (PQC := PQC) r.2).1) h1
        have hl := hv.lazy_le
        have hm := hv.made_le
        exact ⟨hsm', by rw [h2]; omega, by rw [h2]; omega⟩
    · have hmem2 : (r.1, hop2StDec (PQC := PQC) r.2) ∈
          support ((hop2ImplDedup P ℓ Dh encT decT s qep h (.inr t)).run st) := by
        rw [← heq]
        simp only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨r, hr, rfl⟩
      rcases t with (((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q
      · rw [hop2ImplDedup, mem_support_hop2Lift] at hmem2
        exact (hgb.transmitR P (configRefuseEarlyBobCorr decT encT) (Q, msg, optR)
          (r.1, (hop2StDec (PQC := PQC) r.2).1) hmem2.1).mono hsub
      · rw [hop2ImplDedup, mem_support_hop2Lift] at hmem2
        exact (hgb.challR P (configRefuseEarlyBobCorr decT encT) (Q, m₀, m₁, optR)
          (r.1, (hop2StDec (PQC := PQC) r.2).1) hmem2.1).mono hsub
      · exact (hgb.hop2Deliver P ℓ Dh encT decT s h Q c
          (r.1, hop2StDec (PQC := PQC) r.2) hmem2).mono hsub
      · exact (hgb.hop2Inject P ℓ Dh encT decT s qep h Q c
          (r.1, hop2StDec (PQC := PQC) r.2) hmem2).mono hsub
      · rw [hop2ImplDedup, mem_support_hop2Lift] at hmem2
        exact (hgb.corrRDedup (configRefuseEarlyBobCorr decT encT) Q
          (r.1, (hop2StDec (PQC := PQC) r.2).1) hmem2.1).mono hsub
  have hfin : ∀ v b', Inv 0 v →
      R.finish.eval (.cons v (.cons b' .nil)) = finishImpl (abs v) b' := by
    intro v b' _; rfl
  have hmono : ∀ {m n} (v), m ≤ n → Inv n v → Inv m v :=
    fun _ hmn h => ⟨h.1.mono hmn, h.2.1.mono (by omega), h.2.2⟩
  have heval := R.eval_eq_simulateQ_of_abs abs Inv initImpl
    (hop2ImplDedup P ℓ Dh encT decT s qep h) finishImpl qAdv chall
    hinit hinitInv hU hstep hfin hmono (fun _ => A) (fun _ => hA)
  rw [heval]
  dsimp only [initImpl, finishImpl, hop2Game, h]
  simp only [bind_assoc, pure_bind]
  have hbad : ∀ st₀ : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt,
      ((simulateQ (hop2ImplDedup P ℓ Dh encT decT s qep h) A).run st₀ >>=
          fun z => pure z.2.2.bad) =
        ((simulateQ (hop2Impl P Dh encT decT qep s h) A).run st₀ >>=
          fun z => pure z.2.2.bad) := by
    intro st₀
    have hsim := congrArg
      (fun p => (fun z : Bool × (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) =>
        z.2.2.bad) <$> p)
      (map_canonComp_simulateQ_hop2ImplDedup_eq P ℓ Dh encT decT s qep h A st₀)
    simp only [Functor.map_map] at hsim
    simpa only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq] using hsim
  refine bind_congr fun b => bind_congr fun ck0 => bind_congr fun x =>
    bind_congr fun alice => bind_congr fun pqr => bind_congr fun u1 => hbad _

/-- Evaluating `hop2PrfRedKProg` on a `qAdv`-query adversary agrees with `hop2PrfRedK` whenever
`qAdv * qAdv ≤ K * K`, `qAdv ≤ B`, and `2 ^ 32 ≤ B`. -/
theorem hop2PrfRedKProg_eval_of_le (k qAdv : ℕ)
    (hK : qAdv * qAdv ≤ K * K) (hqB : qAdv ≤ B) (h32B : 2 ^ 32 ≤ B)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
    (hA : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)) qAdv) :
    (hop2PrfRedKProg P ℓ Dh encPt encT decT s K B qep k).eval (fun _ => A) () =
      hop2PrfRedK P ℓ Dh encT decT qep s k A := by
  have h := hop2GameRedProg_eval_of_le P ℓ Dh encPt encT decT s K B qep k qAdv hK hqB h32B
    (rIn := .unit)
    (.bind (spkDrawBv P ℓ Dh encPt encT decT s)
      (.bind (spkDrawBv P ℓ Dh encPt encT decT s)
        (.ret (.pair .v1 .v0))))
    (fun _ qE => .query () qE)
    (fun _ I => evalQuery (Input := Pt) (Tag := BitVec 256) I)
    (fun _ {_} _ qE ρ' _ => by
      dsimp only [Comp.eval, e2ePrfIface, Iface.withSamp, prfIface, evalQuery]
      exact id_map _)
    A hA ()
  rw [hop2PrfRedKProg_eq, h]
  unfold hop2PrfRedK
  simp only [eval_bind, eval_ret, spkDrawBv_eval, hop2Unif, bind_assoc, pure_bind,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]

/-- Evaluating `hop2PrgRedKProg` on a `qAdv`-query adversary and challenge `rc` agrees with
`hop2PrgRedK` whenever `qAdv * qAdv ≤ K * K`, `qAdv ≤ B`, and `2 ^ 32 ≤ B`. -/
theorem hop2PrgRedKProg_eval_of_le (k qAdv : ℕ)
    (hK : qAdv * qAdv ≤ K * K) (hqB : qAdv ≤ B) (h32B : 2 ^ 32 ≤ B)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
    (hA : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)) qAdv)
    (rc : Ratchet.RootKey × BitVec 256) :
    (hop2PrgRedKProg P ℓ Dh encPt encT decT s K B qep k).eval (fun _ => A) rc =
      hop2PrgRedK P ℓ Dh encPt encT decT qep s k A rc := by
  let prfReal : QueryImpl (MACScheme.prfSpec Pt (BitVec 256)) ProbComp := fun I =>
    pure ((extractPRF P.C.F encPt).tag rc.1 I)
  rw [CostedReduction.eval_toPrf (hop2PrgRedKProg P ℓ Dh encPt encT decT s K B qep k) prfReal,
    hop2PrgRedKProg_toPrf]
  unfold hop2PrgRedK
  congr 1
  refine (hop2GameRedProg_eval_of_le P ℓ Dh encPt encT decT s K B qep k qAdv hK hqB h32B
    (.ret .v0)
    (fun c1E qE => .ret (opExtractTag P ℓ Dh encPt encT decT s c1E qE))
    (fun ch I => pure ((extractPRF P.C.F encPt).tag ch.1 I))
    (fun ch {_} c1E qE ρ' hc1 => by
      change pure ((extractPRF P.C.F encPt).tag (c1E.eval ρ') (qE.eval ρ')) =
        pure ((extractPRF P.C.F encPt).tag ch.1 (qE.eval ρ'))
      rw [hc1])
    A hA rc).trans ?_
  simp [Comp.eval, Expr.eval, Expr.v0]

end SpkStepPreservation

/-! ## Cost and query bounds -/

section GRedBoundedE2E

private theorem bits_small :
    bits 0 = 1 ∧ bits 1 = 1 ∧ bits 2 = 2 ∧ bits 3 = 2 ∧ bits 10 = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bits_max_q_pow32 (q : ℕ) : bits (max (q + 1) (2 ^ 32)) ≤ q + 33 := by
  rcases le_total (q + 1) (2 ^ 32) with h | h
  · rw [max_eq_right h]
    have h32 : bits (2 ^ 32) = 33 := by decide
    omega
  · rw [max_eq_left h]
    have := bits_le_self_add_one (q + 1)
    omega

theorem spkLeakRedUProg_gRedBounded {Pt : Type} (q qep : ℕ) :
    GRedBounded (spkLeakRedUProg (Pt := Pt))
      (fun _ => 1) (fun _ => 0) (q + 1) (q + 1) (ratchetCostBudget q qep) := by
  refine gRedBounded_of_bounds_const _ (fun _ => 1) (fun _ => 0) (q + 1) (q + 1)
    (ratchetCostBudget q qep) ?_ ?_ ?_ spkLeakRedUOps_sizeHonest
    (SampSizeHonest.sum SampSizeHonest.empty spkLeakRedUSamp_sizeHonest)
  · rw [spkLeakRedUProg_totalCost]
    unfold ratchetCostBudget maxForwardJumps
    have hb : 1 ≤ bits qep := ReductionDsl.one_le_bits qep
    nlinarith
  · simp [CostedReduction.size, spkLeakRedUProg, Comp.size, Expr.size, Expr.v0, Expr.v1,
      reductionSizeBudget]
  · simp [CostedReduction.totalQueries, spkLeakRedUProg, Comp.queries]

@[simp] private theorem ops_sum_opSize_inl {S : Sig} (O₁ O₂ : Ops S) (o : O₁.Op) :
    (O₁.sum O₂).opSize (Sum.inl o) = O₁.opSize o := rfl

private theorem expr_size_liftL {S : Sig} {O₁ O₂ : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O₁ Γ t) : (e.liftL (O₂ := O₂)).size = e.size := by
  induction e <;> simp [Expr.liftL, Expr.size, *]; assumption

private theorem comp_size_liftL {S : Sig} {O₁ O₂ : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O₁ I Γ t) :
    (c.liftL (O₂ := O₂)).size = c.size := by
  induction c <;> simp [Comp.liftL, Comp.size, expr_size_liftL, *]

private theorem epMgmtE_three_size_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (qep : ℕ) (s : Expr O' Γ gsTy) (p bad : Expr O' Γ .bool) :
    (epMgmtE (O' := O') 3 qep s p bad).size ≤
      s.size + p.size + bad.size + 2 * bits qep + 1000 := by
  simp [epMgmtE, sendsInE, safeChE, healedByE, leN, leakE, maxOptE, maxN,
    gsMk, pSet, pGet, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans,
    gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs,
    Expr.size, Expr.v0, Expr.v1, bits_small]
  omega

private theorem recordE_three_size_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) (st' : Expr O' Γ (.base .st))
    (r : Expr O' Γ recTy) (isChall : Expr O' Γ .bool) :
    (recordE (O' := O') 3 s p st' r isChall).size ≤
      s.size + p.size + st'.size + r.size + isChall.size + 600 := by
  simp [recordE, safeChE, healedByE, leN, recPos, posIdx, gsMk, pSet, pGet,
    gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp,
    gsMaxAcc, gsLeaks, gsCorrs, Expr.size, Expr.v0, Expr.v1, bits_small]
  omega

private theorem inTransitE_e2e_size_le {Pt PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) {Γ}
    (K : ℕ) (s : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ gsTy)
    (qParty : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ .bool)
    (c : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ (.base .ct)) :
    (inTransitE K s qParty c).size ≤
      s.size + qParty.size + c.size + bits K + 100 := by
  simp [inTransitE, boolEq, posSender, recPos, recCt, gsTrans,
    Expr.size, Expr.v0, Expr.v1]
  omega

private theorem deleteE_size_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    (deleteE (O' := O') K s pos).size ≤
      s.size + pos.size + 3 * bits K + 400 := by
  simp [deleteE, posEq, boolEq, posSender, posEpoch, posIdx, recPos,
    gsMk, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp,
    gsMaxAcc, gsLeaks, gsCorrs, Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem acceptE_size_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (st' : Expr O' Γ (.base .st)) (pos : Expr O' Γ posTy) :
    (acceptE (O' := O') K s p st' pos).size ≤
      s.size + p.size + st'.size + 2 * pos.size + 3 * bits K + 1000 := by
  have hd := deleteE_size_le K s pos
  simp only [acceptE, posEpoch, posIdx, maxN, leN, maxAccSet, maxAccGet,
    gsMk, pSet, pGet, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans,
    gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs, Expr.size, Expr.v0] at hd ⊢
  omega

private theorem challContainsE_size_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    (challContainsE (O' := O') K s pos).size ≤
      s.size + pos.size + bits K + 100 := by
  simp [challContainsE, posEq, boolEq, posSender, posEpoch, posIdx, gsChall,
    Expr.size, Expr.v0, Expr.v1]
  omega

private theorem trivialE_three_size_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    (trivialE (O' := O') K 3 s pos).size ≤
      s.size + pos.size + 2 * bits K + 400 := by
  simp [trivialE, compContainsE, orE, posEq, boolEq, posSender, posEpoch, posIdx, recPos,
    healedByE, leN, gsComp, gsTrans, gsTL, Expr.size, Expr.v0, Expr.v1, bits_small]
  omega

private theorem corrAllowedE_size_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    (corrAllowedE (O' := O') K s p).size ≤
      s.size + p.size + 3 * bits K + 300 := by
  simp [corrAllowedE, compContainsE, posEq, boolEq, posSender, posEpoch, posIdx,
    otherE, recPos, gsComp, gsChall, gsTrans, Expr.size, Expr.v0, Expr.v1]
  omega

private theorem afterCorrE_size_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    (afterCorrE (O' := O') K s p).size ≤
      s.size + p.size + 30 * bits K + 6000 := by
  simp [afterCorrE, posEq, boolEq, posSender, posEpoch, posIdx, recPos, otherE,
    leakE, maxOptE, maxN, leN, gsMk, pGet, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL,
    gsTrans, gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs, Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem epMgmtE_three_cost_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (qep : ℕ) (s : Expr O' Γ gsTy) (p bad : Expr O' Γ .bool) :
    (epMgmtE (O' := O') 3 qep s p bad).cost ≤
      s.cost + p.cost + bad.cost + 2 * bits qep + 500 := by
  simp [epMgmtE, sendsInE, safeChE, healedByE, leN, leakE, maxOptE, maxN,
    gsMk, pSet, pGet, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans,
    gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs,
    Expr.cost, Expr.v0, Expr.v1, bits_small]
  omega

theorem recordE_three_cost_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) (st' : Expr O' Γ (.base .st))
    (r : Expr O' Γ recTy) (isChall : Expr O' Γ .bool) :
    (recordE (O' := O') 3 s p st' r isChall).cost ≤
      s.cost + p.cost + st'.cost + r.cost + isChall.cost + 300 := by
  simp [recordE, safeChE, healedByE, leN, recPos, posIdx, gsMk, pSet, pGet,
    gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp,
    gsMaxAcc, gsLeaks, gsCorrs, Expr.cost, Expr.v0, Expr.v1, bits_small]
  omega

theorem inTransitE_e2e_cost_le {Pt PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) {Γ}
    (K : ℕ) (s : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ gsTy)
    (qParty : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ .bool)
    (c : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ (.base .ct)) :
    (inTransitE K s qParty c).cost ≤
      s.cost + qParty.cost + c.cost + 30 * (K + 1) + 50 := by
  simp [inTransitE, boolEq, posSender, recPos, recCt, gsTrans,
    Expr.cost, Expr.v0, Expr.v1]
  omega

theorem deleteE_cost_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    (deleteE (O' := O') K s pos).cost ≤
      s.cost + pos.cost + 150 * (K + 1) + 150 := by
  simp [deleteE, posEq, boolEq, posSender, posEpoch, posIdx, recPos,
    gsMk, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp,
    gsMaxAcc, gsLeaks, gsCorrs, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem acceptE_cost_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (st' : Expr O' Γ (.base .st)) (pos : Expr O' Γ posTy) :
    (acceptE (O' := O') K s p st' pos).cost ≤
      s.cost + p.cost + st'.cost + 2 * pos.cost + 150 * (K + 1) + 700 := by
  have hd := deleteE_cost_le K s pos
  simp only [acceptE, posEpoch, posIdx, maxN, leN, maxAccSet, maxAccGet,
    gsMk, pSet, pGet, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans,
    gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs, Expr.cost, Expr.v0]
  omega

theorem challContainsE_cost_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    (challContainsE (O' := O') K s pos).cost ≤
      s.cost + pos.cost + 40 * (K + 1) + 50 := by
  simp [challContainsE, posEq, boolEq, posSender, posEpoch, posIdx, gsChall,
    Expr.cost, Expr.v0, Expr.v1]
  omega

theorem trivialE_three_cost_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    (trivialE (O' := O') K 3 s pos).cost ≤
      s.cost + pos.cost + 80 * (K + 1) + 300 := by
  simp [trivialE, compContainsE, orE, posEq, boolEq, posSender, posEpoch, posIdx, recPos,
    healedByE, leN, gsComp, gsTrans, gsTL, Expr.cost, Expr.v0, Expr.v1, bits_small]
  omega

theorem corrAllowedE_cost_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    (corrAllowedE (O' := O') K s p).cost ≤
      s.cost + p.cost + 40 * ((K + 1) * (K + 1)) + 100 * (K + 1) + 100 := by
  simp [corrAllowedE, compContainsE, posEq, boolEq, posSender, posEpoch, posIdx,
    otherE, recPos, gsComp, gsChall, gsTrans, Expr.cost, Expr.v0, Expr.v1]
  nlinarith

theorem afterCorrE_cost_le {Key St St₂ Msg Coins RCoins C : Type}
    {O' : Ops (smSig Key St St₂ Msg Coins RCoins C)} {Γ}
    (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    (afterCorrE (O' := O') K s p).cost ≤
      s.cost + p.cost + 450 * ((K + 1) * (K + 1)) + 300 * (K + 1) + 5000 := by
  simp [afterCorrE, posEq, boolEq, posSender, posEpoch, posIdx, recPos, otherE,
    leakE, maxOptE, maxN, leN, gsMk, pGet, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL,
    gsTrans, gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  nlinarith

theorem transmitRC_spkS_cost_le {Pt PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawCoins : ∀ {Γ}, Comp (spkLeakSessionSmOps P ℓ decT encT) I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ}, (drawCoins (Γ := Γ)).cost ≤ 10)
    (qep : ℕ) {Γ} (s : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ gsTy)
    (arg : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ
      (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) :
    (transmitRC (I := I) 3 qep (ConfigRC.spkS (spkLeakSessionSmOps P ℓ decT encT)) drawCoins s arg).cost ≤
      s.cost + arg.cost + 2 * bits qep + 1000 := by
  let OSM := spkLeakSessionSmOps P ℓ decT encT
  have hep := epMgmtE_three_cost_le (O' := OSM) qep (.fst .v2) (.fst (.snd .v2)) (.snd .v0)
    (Γ := .prod (.base .coins) .bool :: .opt (.prod (.base .coins) .bool) ::
      .prod gsTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) :: Γ)
  have hrec := recordE_three_cost_le (O' := OSM) .v1 (.fst (.snd .v4)) (.fst .v0)
    (.pair (.pair (.fst (.snd .v4)) (.pair (pGet (gsEpoch .v1) (.fst (.snd .v4)))
      (.add (pGet (gsIdx .v1) (.fst (.snd .v4))) (.nat 1))))
      (.pair (.fst (.snd (.snd .v4))) (.snd .v0))) (.bool false)
    (Γ := .prod (.base .st) (.base .ct) :: gsTy ::
      .prod (.base .coins) .bool :: .opt (.prod (.base .coins) .bool) ::
      .prod gsTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) :: Γ)
  have hc := hCoins (Γ := .prod gsTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) :: Γ)
  simp only [transmitRC, samIfNecC, ConfigRC.spkS, orE, noBobEpoch0E,
    pGet, gsWin, gsSt, gsEpoch, gsIdx, spkLeakSessionSmOps, smOps,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, bits_small] at hep hrec hc ⊢
  omega

theorem challRC_spkS_cost_le {Pt PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawCoins : ∀ {Γ}, Comp (spkLeakSessionSmOps P ℓ decT encT) I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ}, (drawCoins (Γ := Γ)).cost ≤ 10)
    (qep : ℕ) {Γ} (s : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ gsTy)
    (arg : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins)))))) :
    (challRC (I := I) 3 qep (ConfigRC.spkS (spkLeakSessionSmOps P ℓ decT encT)) drawCoins s arg).cost ≤
      s.cost + arg.cost + 2 * bits qep + 1200 := by
  let OSM := spkLeakSessionSmOps P ℓ decT encT
  have hep := epMgmtE_three_cost_le (O' := OSM) qep (.fst .v2) (.fst (.snd .v2)) (.snd .v0)
    (Γ := .prod (.base .coins) .bool :: .opt (.prod (.base .coins) .bool) ::
      .prod gsTy (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) :: Γ)
  have hrec := recordE_three_cost_le (O' := OSM) .v1 (.fst (.snd .v4)) (.fst .v0)
    (.pair (.pair (.fst (.snd .v4))
      (.pair (pGet (gsEpoch .v1) (.fst (.snd .v4)))
        (.add (pGet (gsIdx .v1) (.fst (.snd .v4))) (.nat 1))))
      (.pair (.ite (gsB (.fst .v4)) (.fst (.snd (.snd (.snd .v4)))) (.fst (.snd (.snd .v4))))
        (.snd .v0))) (.bool true)
    (Γ := .prod (.base .st) (.base .ct) :: gsTy ::
      .prod (.base .coins) .bool :: .opt (.prod (.base .coins) .bool) ::
      .prod gsTy (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) :: Γ)
  have hc := hCoins (Γ :=
    .prod gsTy (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) :: Γ)
  simp only [challRC, samIfNecC, ConfigRC.spkS, ConfigRC.challMsgE, orE, noBobEpoch0E,
    safeChE, healedByE, leN, pGet, gsWin, gsSt, gsB, gsEpoch, gsIdx, gsTL, spkLeakSessionSmOps, smOps,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, bits_small] at hep hrec hc ⊢
  omega

theorem corrRC_spkS_cost_le {Pt PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (K : ℕ) {Γ} (s : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ gsTy)
    (p : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ .bool) :
    (corrRC (I := I) K (ConfigRC.spkS (spkLeakSessionSmOps P ℓ decT encT)) s p).cost ≤
      s.cost + p.cost + 500 * ((K + 1) * (K + 1)) + 400 * (K + 1) + 6000 := by
  let OSM := spkLeakSessionSmOps P ℓ decT encT
  have hca := corrAllowedE_cost_le (O' := OSM) K (.fst .v0) (.snd .v0)
    (Γ := .prod gsTy .bool :: Γ)
  have hac := afterCorrE_cost_le (O' := OSM) K (.fst .v0) (.snd .v0)
    (Γ := .prod gsTy .bool :: Γ)
  simp only [corrRC, ConfigRC.spkS, orE, inWindowE, sendsInE,
    noSpkCorrE, noCorrB0E, noBobEpoch0E, noCorrBWinE, pGet, gsWin, gsSt, gsEpoch,
    spkLeakSessionSmOps, smOps,
    Comp.cost, Expr.cost, Expr.v0, bits_small] at hca hac ⊢
  omega

private theorem transmitRC_spkS_size_le {Pt PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawCoins : ∀ {Γ}, Comp (spkLeakSessionSmOps P ℓ decT encT) I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ}, (drawCoins (Γ := Γ)).size ≤ 10)
    (qep : ℕ) {Γ} (s : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ gsTy)
    (arg : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ
      (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) :
    (transmitRC (I := I) 3 qep (ConfigRC.spkS (spkLeakSessionSmOps P ℓ decT encT)) drawCoins s arg).size ≤
      s.size + arg.size + 2 * bits qep + 2000 := by
  let OSM := spkLeakSessionSmOps P ℓ decT encT
  have hep := epMgmtE_three_size_le (O' := OSM) qep (.fst .v2) (.fst (.snd .v2)) (.snd .v0)
    (Γ := .prod (.base .coins) .bool :: .opt (.prod (.base .coins) .bool) ::
      .prod gsTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) :: Γ)
  have hrec := recordE_three_size_le (O' := OSM) .v1 (.fst (.snd .v4)) (.fst .v0)
    (.pair (.pair (.fst (.snd .v4)) (.pair (pGet (gsEpoch .v1) (.fst (.snd .v4)))
      (.add (pGet (gsIdx .v1) (.fst (.snd .v4))) (.nat 1))))
      (.pair (.fst (.snd (.snd .v4))) (.snd .v0))) (.bool false)
    (Γ := .prod (.base .st) (.base .ct) :: gsTy ::
      .prod (.base .coins) .bool :: .opt (.prod (.base .coins) .bool) ::
      .prod gsTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) :: Γ)
  have hc := hCoins (Γ := .prod gsTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) :: Γ)
  simp only [transmitRC, samIfNecC, ConfigRC.spkS, orE, noBobEpoch0E,
    pGet, gsWin, gsSt, gsEpoch, gsIdx,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, bits_small] at hep hrec hc ⊢
  omega

private theorem challRC_spkS_size_le {Pt PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawCoins : ∀ {Γ}, Comp (spkLeakSessionSmOps P ℓ decT encT) I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ}, (drawCoins (Γ := Γ)).size ≤ 10)
    (qep : ℕ) {Γ} (s : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ gsTy)
    (arg : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins)))))) :
    (challRC (I := I) 3 qep (ConfigRC.spkS (spkLeakSessionSmOps P ℓ decT encT)) drawCoins s arg).size ≤
      s.size + arg.size + 2 * bits qep + 2500 := by
  let OSM := spkLeakSessionSmOps P ℓ decT encT
  have hep := epMgmtE_three_size_le (O' := OSM) qep (.fst .v2) (.fst (.snd .v2)) (.snd .v0)
    (Γ := .prod (.base .coins) .bool :: .opt (.prod (.base .coins) .bool) ::
      .prod gsTy (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) :: Γ)
  have hrec := recordE_three_size_le (O' := OSM) .v1 (.fst (.snd .v4)) (.fst .v0)
    (.pair (.pair (.fst (.snd .v4))
      (.pair (pGet (gsEpoch .v1) (.fst (.snd .v4)))
        (.add (pGet (gsIdx .v1) (.fst (.snd .v4))) (.nat 1))))
      (.pair (.ite (gsB (.fst .v4)) (.fst (.snd (.snd (.snd .v4)))) (.fst (.snd (.snd .v4))))
        (.snd .v0))) (.bool true)
    (Γ := .prod (.base .st) (.base .ct) :: gsTy ::
      .prod (.base .coins) .bool :: .opt (.prod (.base .coins) .bool) ::
      .prod gsTy (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) :: Γ)
  have hc := hCoins (Γ :=
    .prod gsTy (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) :: Γ)
  simp only [challRC, samIfNecC, ConfigRC.spkS, ConfigRC.challMsgE, orE, noBobEpoch0E,
    safeChE, healedByE, leN, pGet, gsWin, gsSt, gsB, gsEpoch, gsIdx, gsTL,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, bits_small] at hep hrec hc ⊢
  omega

private theorem corrRC_spkS_size_le {Pt PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (K : ℕ) {Γ} (s : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ gsTy)
    (p : Expr (spkLeakSessionSmOps P ℓ decT encT) Γ .bool) :
    (corrRC (I := I) K (ConfigRC.spkS (spkLeakSessionSmOps P ℓ decT encT)) s p).size ≤
      s.size + p.size + 35 * bits K + 7000 := by
  let OSM := spkLeakSessionSmOps P ℓ decT encT
  have hca := corrAllowedE_size_le (O' := OSM) K (.fst .v0) (.snd .v0)
    (Γ := .prod gsTy .bool :: Γ)
  have hac := afterCorrE_size_le (O' := OSM) K (.fst .v0) (.snd .v0)
    (Γ := .prod gsTy .bool :: Γ)
  simp only [corrRC, ConfigRC.spkS, orE, inWindowE, sendsInE,
    noSpkCorrE, noCorrB0E, noBobEpoch0E, noCorrBWinE, pGet, gsWin, gsSt, gsEpoch,
    Comp.size, Expr.size, Expr.v0, bits_small] at hca hac ⊢
  omega

theorem receiveSpkC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (B : ℕ) {Γ}
    (sE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (gE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .st))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins)) :
    (receiveSpkC P ℓ Dh encPt encT decT s B sE gE cE rcE).cost ≤
      sE.cost + gE.cost + cE.cost + rcE.cost + 2 * bits B + 200 := by
  simp [receiveSpkC, receiveB0C, e2ePrfIface, Iface.withSamp, prfIface,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem deliverSpkC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B : ℕ) {Γ}
    (stE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ gsTy)
    (arg : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.prod .bool (.base .ct))) :
    (deliverSpkC P ℓ Dh encPt encT decT s K B stE arg).cost ≤
      stE.cost + arg.cost + 2 * bits B + 250 * (K + 1) + 1050 := by
  have htr := inTransitE_e2e_cost_le P ℓ decT encT K (.fst .v0) (otherE (.fst (.snd .v0)))
    (.snd (.snd .v0)) (Γ := .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hrec := receiveSpkC_cost_le P ℓ Dh encPt encT decT s B
    (opSpkSc P ℓ Dh encPt encT decT s) (pGet (gsSt (.fst .v2)) (.fst (.snd .v2)))
    (.snd (.snd .v2)) .v0
    (Γ := .base .rcoins :: recTy :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hacc := acceptE_cost_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst .v4) (.fst (.snd .v4)) (.fst .v0) (recPos .v3)
    (Γ := .prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) ::
      .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) ::
      .base .rcoins :: recTy :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hch := challContainsE_cost_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst .v4) (recPos .v3)
    (Γ := .prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) ::
      .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) ::
      .base .rcoins :: recTy :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  simp only [deliverSpkC, Comp.cost, Expr.cost_liftL]
  simp only [spkDrawBv, opSpkSc_cost, pGet, gsWin, gsSt, recPos, otherE,
    e2ePrfIface, Iface.withSamp, prfIface, Samplers.sum, unifSamplers,
    Sum.elim_inr, Comp.cost, Expr.cost,
    Expr.v0, Expr.v2, Expr.v3, Expr.v4] at htr hrec hacc hch ⊢
  omega

theorem injectSpkC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep : ℕ) {Γ}
    (stE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ gsTy)
    (arg : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.prod .bool (.base .ct))) :
    (injectSpkC P ℓ Dh encPt encT decT s K B qep stE arg).cost ≤
      stE.cost + arg.cost + 2 * bits B + bits (qep + 1) + 350 * (K + 1) + 2200 := by
  have htr := inTransitE_e2e_cost_le P ℓ decT encT K (.fst .v0) (otherE (.fst (.snd .v0)))
    (.snd (.snd .v0)) (Γ := .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hrec := receiveSpkC_cost_le P ℓ Dh encPt encT decT s B
    (opSpkSc P ℓ Dh encPt encT decT s) (pGet (gsSt (.fst .v1)) (.fst (.snd .v1)))
    (.snd (.snd .v1)) .v0
    (Γ := .base .rcoins :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have htv := trivialE_three_cost_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K (.fst .v3)
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
    (Γ := .prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) ::
      .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) ::
      .base .rcoins :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hacc := acceptE_cost_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst .v3) (.fst (.snd .v3)) (.fst .v0)
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
    (Γ := .prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) ::
      .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) ::
      .base .rcoins :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  simp only [injectSpkC, orE, isSomeE, Comp.cost, Expr.cost, Expr.cost_liftL]
  simp only [safeInjE, healedByE, minN, leN, opInjOK_cost,
    spkDrawBv, opSpkSc_cost, pGet, otherE, gsSetWin, gsMk,
    gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs,
    e2ePrfIface, Iface.withSamp, prfIface, Samplers.sum, unifSamplers,
    Sum.elim_inr, Comp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, bits_small] at htr hrec htv hacc ⊢
  omega

theorem spkLeakRedProg_handle_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep : ℕ) :
    (spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).handle.cost ≤
      4 * bits B + 4 * bits qep + bits (qep + 1) +
        500 * ((K + 1) * (K + 1)) + 1200 * (K + 1) + 12000 := by
  have hCoins : ∀ {Γ}, (spkDrawCoins ℓ (Pt := Pt) (PQC := PQC)
      (O' := spkLeakSessionSmOps P ℓ decT encT) (Γ := Γ)).cost ≤ 10 := by
    intro Γ
    simp [spkDrawCoins, e2ePrfIface, Iface.withSamp, prfIface, Samplers.sum, unifSamplers,
      Comp.cost, Expr.cost, Expr.v0]
  let Q1 : Ty (spkLeakSessionSig Pt ℓ PQC) := .prod .bool (.prod (.base .msg) (.opt (.base .coins)))
  let Q2 : Ty (spkLeakSessionSig Pt ℓ PQC) :=
    .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))
  let Q3 : Ty (spkLeakSessionSig Pt ℓ PQC) := .prod .bool (.base .ct)
  let G0 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) :=
    .prod gsTy (e2eCodec Pt ℓ PQC).Q :: [gsTy, (e2eCodec Pt ℓ PQC).Q]
  let G1 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum (Ty.sum (Ty.sum Q1 Q2) Q3) Q3 :: G0
  let G2 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum (Ty.sum Q1 Q2) Q3 :: G1
  let G3 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum Q1 Q2 :: G2
  have htr := transmitRC_spkS_cost_le P ℓ decT encT (I := e2ePrfIface Pt ℓ PQC)
    (spkDrawCoins ℓ (PQC := PQC)) hCoins qep (.fst .v4) .v0 (Γ := Q1 :: G3)
  have hch := challRC_spkS_cost_le P ℓ decT encT (I := e2ePrfIface Pt ℓ PQC)
    (spkDrawCoins ℓ (PQC := PQC)) hCoins qep (.fst .v4) .v0 (Γ := Q2 :: G3)
  have hdl := deliverSpkC_cost_le P ℓ Dh encPt encT decT s K B (.fst .v3) .v0
    (Γ := Q3 :: G2)
  have hij := injectSpkC_cost_le P ℓ Dh encPt encT decT s K B qep (.fst .v2) .v0
    (Γ := Q3 :: G1)
  have hcr := corrRC_spkS_cost_le P ℓ decT encT (I := e2ePrfIface Pt ℓ PQC)
    K (.fst .v1) .v0 (Γ := .bool :: G0)
  simp only [spkLeakRedProg, spkOracleImplC, Comp.cost_liftL, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at htr hch hdl hij hcr ⊢
  omega

private theorem receiveSpkC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (B : ℕ) {Γ}
    (sE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (gE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .st))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins)) :
    (receiveSpkC P ℓ Dh encPt encT decT s B sE gE cE rcE).size ≤
      sE.size + gE.size + cE.size + rcE.size + 300 := by
  simp [receiveSpkC, receiveB0C, opIsB0, opSenderKeyPt, opFinishRecvB0, opReceive,
    opStParty, opStEpoch, opParseSenderKey, opDecT, opIsZeroPt, opEqBytes, opEncT, opDh,
    opRootExpand, opRootCreateChain, opResetEpoch0, opPushRecvChain, opSetSenderChain,
    opSetRootKey, opTryDecryptWhisper, orE,
    spkLeakSessionOps, Ops.sum, spkLeakSessionSmOps, smOps, spkLeakOps,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, bits_small]
  omega

private theorem deliverSpkC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B : ℕ) {Γ}
    (stE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ gsTy)
    (arg : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.prod .bool (.base .ct))) :
    (deliverSpkC P ℓ Dh encPt encT decT s K B stE arg).size ≤
      stE.size + arg.size + 5 * bits K + 2000 := by
  have htr := inTransitE_e2e_size_le P ℓ decT encT K (.fst .v0) (otherE (.fst (.snd .v0)))
    (.snd (.snd .v0)) (Γ := .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hrec := receiveSpkC_size_le P ℓ Dh encPt encT decT s B
    (opSpkSc P ℓ Dh encPt encT decT s) (pGet (gsSt (.fst .v2)) (.fst (.snd .v2)))
    (.snd (.snd .v2)) .v0
    (Γ := .base .rcoins :: recTy :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hacc := acceptE_size_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst .v4) (.fst (.snd .v4)) (.fst .v0) (recPos .v3)
    (Γ := .prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) ::
      .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) ::
      .base .rcoins :: recTy :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hch := challContainsE_size_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst .v4) (recPos .v3)
    (Γ := .prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) ::
      .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) ::
      .base .rcoins :: recTy :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  simp only [deliverSpkC, Comp.size, expr_size_liftL]
  simp only [spkDrawBv, opSpkSc, pGet, gsWin, gsSt, recPos, otherE,
    Comp.size, Expr.size, spkLeakSessionOps, Ops.sum, spkLeakOps, Sum.elim_inr,
    Expr.v0, Expr.v2, Expr.v3, Expr.v4] at htr hrec hacc hch ⊢
  omega

private theorem injectSpkC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep : ℕ) {Γ}
    (stE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ gsTy)
    (arg : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.prod .bool (.base .ct))) :
    (injectSpkC P ℓ Dh encPt encT decT s K B qep stE arg).size ≤
      stE.size + arg.size + bits (qep + 1) + 6 * bits K + 3000 := by
  have htr := inTransitE_e2e_size_le P ℓ decT encT K (.fst .v0) (otherE (.fst (.snd .v0)))
    (.snd (.snd .v0)) (Γ := .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hrec := receiveSpkC_size_le P ℓ Dh encPt encT decT s B
    (opSpkSc P ℓ Dh encPt encT decT s) (pGet (gsSt (.fst .v1)) (.fst (.snd .v1)))
    (.snd (.snd .v1)) .v0
    (Γ := .base .rcoins :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have htv := trivialE_three_size_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K (.fst .v3)
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
    (Γ := .prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) ::
      .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) ::
      .base .rcoins :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  have hacc := acceptE_size_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst .v3) (.fst (.snd .v3)) (.fst .v0)
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
    (Γ := .prod (.base .st) (.prod .nat (.prod .nat (.base .msg))) ::
      .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg)))) ::
      .base .rcoins :: .prod gsTy (.prod .bool (.base .ct)) :: Γ)
  simp only [injectSpkC, orE, isSomeE, Comp.size, Expr.size, expr_size_liftL]
  simp only [safeInjE, healedByE, minN, leN, opInjOK, spkDrawBv, opSpkSc, pGet, otherE,
    gsSetWin, gsMk, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp,
    gsMaxAcc, gsLeaks, gsCorrs,
    Comp.size, Expr.size, spkLeakSessionOps, Ops.sum, spkLeakSessionSmOps, smOps, spkLeakOps,
    Sum.elim_inl, Sum.elim_inr,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, bits_small] at htr hrec htv hacc ⊢
  omega

theorem spkLeakRedProg_handle_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep : ℕ) :
    (spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).handle.size ≤
      50 * bits K + 4 * bits qep + bits (qep + 1) + 20000 := by
  have hCoins : ∀ {Γ}, (spkDrawCoins ℓ (Pt := Pt) (PQC := PQC)
      (O' := spkLeakSessionSmOps P ℓ decT encT) (Γ := Γ)).size ≤ 10 := by
    intro Γ
    simp [spkDrawCoins, Comp.size, Expr.size, Expr.v0]
  let Q1 : Ty (spkLeakSessionSig Pt ℓ PQC) := .prod .bool (.prod (.base .msg) (.opt (.base .coins)))
  let Q2 : Ty (spkLeakSessionSig Pt ℓ PQC) :=
    .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))
  let Q3 : Ty (spkLeakSessionSig Pt ℓ PQC) := .prod .bool (.base .ct)
  let G0 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) :=
    .prod gsTy (e2eCodec Pt ℓ PQC).Q :: [gsTy, (e2eCodec Pt ℓ PQC).Q]
  let G1 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum (Ty.sum (Ty.sum Q1 Q2) Q3) Q3 :: G0
  let G2 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum (Ty.sum Q1 Q2) Q3 :: G1
  let G3 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum Q1 Q2 :: G2
  have htr := transmitRC_spkS_size_le P ℓ decT encT (I := e2ePrfIface Pt ℓ PQC)
    (spkDrawCoins ℓ (PQC := PQC)) hCoins qep (.fst .v4) .v0 (Γ := Q1 :: G3)
  have hch := challRC_spkS_size_le P ℓ decT encT (I := e2ePrfIface Pt ℓ PQC)
    (spkDrawCoins ℓ (PQC := PQC)) hCoins qep (.fst .v4) .v0 (Γ := Q2 :: G3)
  have hdl := deliverSpkC_size_le P ℓ Dh encPt encT decT s K B (.fst .v3) .v0
    (Γ := Q3 :: G2)
  have hij := injectSpkC_size_le P ℓ Dh encPt encT decT s K B qep (.fst .v2) .v0
    (Γ := Q3 :: G1)
  have hcr := corrRC_spkS_size_le P ℓ decT encT (I := e2ePrfIface Pt ℓ PQC)
    K (.fst .v1) .v0 (Γ := .bool :: G0)
  simp only [spkLeakRedProg, spkOracleImplC, comp_size_liftL, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at htr hch hdl hij hcr ⊢
  omega

theorem spkLeakRedProg_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep : ℕ) :
    (spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).size ≤
      50 * bits K + 4 * bits qep + bits (qep + 1) + 21000 := by
  have hh := spkLeakRedProg_handle_size_le P ℓ Dh encPt encT decT s K B qep
  have hif : (spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).init.size +
      (spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).finish.size ≤ 1000 := by
    simp [spkLeakRedProg, spkDrawBool, spkDrawBv, initAOracleC, opSpkSc, opZeroBv, opDh,
      opBasePt, opRootExpand, opInitA, opInitB, opSetPendingPreKey, opSetSenderChain,
      opAddRecvChain, opNewSession, opGenPub, gsMk, orE, boolEq, gsB, gsWin,
      spkLeakSessionOps, Ops.sum, spkLeakOps,
      Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, bits_small]
  unfold CostedReduction.size
  omega

theorem spkLeakRedProg_gRedBounded {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded
      (spkLeakRedProg P ℓ Dh encPt encT decT s q (max (q + 1) (2 ^ 32)) qep)
      (fun _ => 1) (fun _ => 0) q (q + 1)
      (ratchetCostBudget q qep + 2 ^ 12 * (q + 1) ^ 2 * q) := by
  let B3 := ratchetCostBudget q qep + 2 ^ 12 * (q + 1) ^ 2 * q
  refine gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) B3
    ?_ ?_ ?_ (e2eFullOps_sizeHonest P ℓ Dh encPt encT decT s) (e2ePrfSamp_sizeHonest ℓ (PQC := PQC))
  · rw [spkLeakRedProg_totalCost]
    have hh := spkLeakRedProg_handle_cost_le P ℓ Dh encPt encT decT s
      q (max (q + 1) (2 ^ 32)) qep
    have hbB := bits_max_q_pow32 q
    have hb : 1 ≤ bits qep := ReductionDsl.one_le_bits qep
    have hbq1 : bits (qep + 1) ≤ bits qep + 1 := by
      have hadd := ReductionDsl.bits_add qep 1
      have h1 : bits 1 = 1 := rfl
      omega
    set M := q + maxForwardJumps + bits qep
    have hM_big : 25001 ≤ M := by dsimp [M, maxForwardJumps]; omega
    have hqM : q + 1 ≤ M := by dsimp [M, maxForwardJumps]; omega
    have hbqM : bits qep ≤ M := by dsimp [M]; omega
    have hhand :
        (spkLeakRedProg P ℓ Dh encPt encT decT s q (max (q + 1) (2 ^ 32)) qep).handle.cost +
          6 ≤ 510 * (q + 1) * M := by
      nlinarith
    have hmul := Nat.mul_le_mul_left q hhand
    have hB3 : 2 ^ 12 * (q + 1) ^ 2 * M = B3 := by
      dsimp [B3, M]; unfold ratchetCostBudget; ring
    nlinarith
  · have hs := spkLeakRedProg_size_le P ℓ Dh encPt encT decT s q (max (q + 1) (2 ^ 32)) qep
    have hq_cb : q ≤ B3 := by
      dsimp [B3]; unfold ratchetCostBudget maxForwardJumps; nlinarith
    have hqep_cb : qep ≤ B3 := by
      dsimp [B3]; unfold ratchetCostBudget maxForwardJumps; nlinarith
    have hbq : bits q ≤ bits B3 := ReductionDsl.bits_mono hq_cb
    have hbqp : bits qep ≤ bits B3 := ReductionDsl.bits_mono hqep_cb
    have hbq1 : bits (qep + 1) ≤ bits qep + 2 := by
      have hadd := ReductionDsl.bits_add qep 1
      have h1 : bits 1 = 1 := rfl
      omega
    unfold reductionSizeBudget
    omega
  · simp [CostedReduction.totalQueries, spkLeakRedProg, spkOracleImplC, spkDrawBool, spkDrawBv, spkDrawCoins,
      initAOracleC, deliverSpkC, injectSpkC, receiveSpkC, receiveB0C,
      Comp.queries, Comp.queries_liftL]
    omega

theorem hop2LookupE_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (L : ℕ) {Γ}
    (l : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.list hop2EntryTy))
    (tE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ .nat)
    (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)) :
    (hop2LookupE P ℓ Dh encPt encT decT s L l tE qE).cost ≤
      l.cost + tE.cost + qE.cost + 30 * (L + 1) + 50 := by
  simp [hop2LookupE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem hop2LazyC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).cost ≤ 10)
    {Γ}
    (auxE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2AuxTy)
    (tE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ .nat)
    (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)) :
    (hop2LazyC P ℓ Dh encPt encT decT s K drawBv auxE tE qE).cost ≤
      auxE.cost + tE.cost + qE.cost + 30 * (K + 1) + 150 := by
  have hlk := hop2LookupE_cost_le P ℓ Dh encPt encT decT s K
    (auxLazy (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
    (Γ := .prod hop2AuxTy (.prod .nat (.base .key)) :: Γ)
  have hb := hBv (Γ := .prod hop2AuxTy (.prod .nat (.base .key)) :: Γ)
  simp only [hop2LazyC, auxConsLazy, auxMk, auxLazy, auxMade, auxIdx, auxCoins, auxBad,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hlk hb ⊢
  omega

theorem hop2FinishNoneC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (B : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    {Γ}
    (aux1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2AuxTy)
    (gE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .st))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (rkckE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ
      (.prod (.base .rcoins) (.base .rcoins))) :
    (hop2FinishNoneC P ℓ Dh encPt encT decT s B (I := I) aux1E gE cE rcE rkckE).cost ≤
      aux1E.cost + gE.cost + cE.cost + rcE.cost + rkckE.cost + bits B + 250 := by
  simp only [hop2FinishNoneC, Comp.cost, Expr.cost, opSendHalfReal_cost, opFinishHop2DH_cost,
    Expr.v0, Expr.v1, Expr.v2]
  omega

theorem hop2SendHalfC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).cost ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).cost ≤ c1E.cost + qE.cost + 20)
    {Γ}
    (challE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2ChallTy)
    (idx1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.opt .nat))
    (rkME : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (q'E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)) :
    (hop2SendHalfC P ℓ Dh encPt encT decT s k drawBv stepC challE idx1E rkME cE rcE q'E).cost ≤
      challE.cost + idx1E.cost + rkME.cost + cE.cost + rcE.cost + q'E.cost +
        2 * bits k + 300 := by
  let G0 := .nat :: .prod hop2ChallTy (.prod (.opt .nat)
    (.prod (.base .rcoins) (.prod (.base .ct) (.prod (.base .rcoins) (.base .key))))) :: Γ
  have hb := hBv (Γ := G0)
  have hst := hStep (.fst (.fst .v1)) (.snd (.snd (.snd (.snd (.snd .v1))))) (Γ := G0)
  simp only [hop2SendHalfC, Comp.cost, Expr.cost, opSendHalfReal_cost,
    opZeroBv_cost, opIsZeroPt_cost, opRootExpand_cost,
    Expr.v0, Expr.v1, Expr.v2, bits_small] at hb hst ⊢
  omega

theorem hop2DHC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).cost ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).cost ≤ c1E.cost + qE.cost + 20)
    {Γ}
    (auxE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2AuxTy)
    (challE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2ChallTy)
    (tE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ .nat)
    (coinsE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (gE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .st))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins)) :
    (hop2DHC P ℓ Dh encPt encT decT s K B k drawBv stepC
      auxE challE tE coinsE gE cE rcE).cost ≤
      auxE.cost + challE.cost + tE.cost + coinsE.cost + gE.cost + cE.cost + rcE.cost +
        3 * bits k + bits B + 60 * (K + 1) + 950 := by
  let G0 := (.base .key) :: .prod hop2AuxTy (.prod hop2ChallTy (.prod .nat
    (.prod (.base .rcoins) (.prod (.base .st) (.prod (.base .ct) (.base .rcoins)))))) :: Γ
  let G_lz := (.prod (.base .rcoins) hop2AuxTy) :: G0
  let G_ck := (.base .rcoins) :: G0
  let G_st := (.base .rcoins) :: G0
  have hlk := hop2LookupE_cost_le P ℓ Dh encPt encT decT s (K + 1)
    (auxMade (.fst .v1)) (.fst (.snd (.snd .v1)))
    (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0) (Γ := G0)
  have hlz := hop2LazyC_cost_le P ℓ Dh encPt encT decT s K drawBv hBv
    (.fst .v1) (.fst (.snd (.snd .v1)))
    (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0) (Γ := G0)
  have hfn1 := hop2FinishNoneC_cost_le P ℓ Dh encPt encT decT s B (I := I)
    (.snd .v0) (.fst (.snd (.snd (.snd (.snd .v2)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
    (opRootExpand P ℓ Dh encPt encT decT s (.fst .v0)) (Γ := G_lz)
  have hsh := hop2SendHalfC_cost_le P ℓ Dh encPt encT decT s k drawBv hBv stepC hStep
    (.fst (.snd .v2)) (.some (.add (.fst (.snd (.snd .v2))) (.nat 1)))
    (opZeroBv P ℓ Dh encPt encT decT s)
    (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
    (opDh P ℓ Dh encPt encT decT s (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))) .v1)
    (Γ := G_ck)
  have hst := hStep (.fst (.fst (.snd .v1)))
    (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0) (Γ := G0)
  have hfn2 := hop2FinishNoneC_cost_le P ℓ Dh encPt encT decT s B (I := I)
    (.fst .v2) (.fst (.snd (.snd (.snd (.snd .v2)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
    (opRootExpand P ℓ Dh encPt encT decT s .v0) (Γ := G_st)
  simp only [hop2DHC, leN, auxMade, Comp.cost, Expr.cost, opDhTargetPt_cost, opIsZeroPt_cost,
    opRootExpand_cost, opZeroBv_cost, opFinishHop2DH_cost, opDh_cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, bits_small] at hlk hlz hfn1 hsh hst hfn2 ⊢
  omega

theorem hop2RecvC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).cost ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).cost ≤ c1E.cost + qE.cost + 20)
    {Γ}
    (auxE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2AuxTy)
    (challE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2ChallTy)
    (gE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .st))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins)) :
    (hop2RecvC P ℓ Dh encPt encT decT s K B k drawBv stepC auxE challE gE cE rcE).cost ≤
      auxE.cost + challE.cost + gE.cost + cE.cost + rcE.cost +
        3 * bits k + 3 * bits B + 60 * (K + 1) + 1200 := by
  let G0 := .nat :: .prod hop2AuxTy (.prod hop2ChallTy
    (.prod (.base .st) (.prod (.base .ct) (.base .rcoins)))) :: Γ
  have hdh := hop2DHC_cost_le P ℓ Dh encPt encT decT s K B k drawBv hBv stepC hStep
    (.fst .v1) (.fst (.snd .v1)) .v0
    (pGet (auxCoins (.fst .v1)) (opStParty P ℓ Dh encPt encT decT s (.fst (.snd (.snd .v1)))))
    (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
    (Γ := G0)
  simp only [hop2RecvC, Comp.cost, Expr.cost, opWireOk_cost, opNeedsDH_cost,
    opReceive_cost, opStParty_cost, pGet, auxIdx, auxCoins,
    Expr.v0, Expr.v1, Expr.v2] at hdh ⊢
  omega

theorem hop2DeliverC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).cost ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).cost ≤ c1E.cost + qE.cost + 20)
    {Γ}
    (stE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2StTy)
    (argE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.prod .bool (.base .ct))) :
    (hop2DeliverC P ℓ Dh encPt encT decT s K B k drawBv stepC stE argE).cost ≤
      stE.cost + argE.cost + 3 * bits k + 3 * bits B + 350 * (K + 1) + 3200 := by
  let G0 := .prod hop2StTy (.prod .bool (.base .ct)) :: Γ
  let G1 := (.base .rcoins) :: recTy :: G0
  let G2 := (.prod hop2RecvResTy (.opt hop2UpdTy)) :: (.prod hop2OutTy hop2AuxTy) :: G1
  have htr := inTransitE_e2e_cost_le P ℓ decT encT K (.fst (.fst .v0))
    (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) (Γ := G0)
  have hb := hBv (Γ := recTy :: G0)
  have hrec := hop2RecvC_cost_le P ℓ Dh encPt encT decT s K B k drawBv hBv stepC hStep
    (.fst (.snd (.fst .v2))) (.snd (.snd (.fst .v2)))
    (pGet (gsSt (.fst (.fst .v2))) (.fst (.snd .v2))) (.snd (.snd .v2)) .v0 (Γ := G1)
  have hacc := acceptE_cost_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst (.fst .v4)) (.fst (.snd .v4))
    (.fst (.fst .v0)) (recPos .v3) (Γ := G2)
  have hch := challContainsE_cost_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst (.fst .v4)) (recPos .v3) (Γ := G2)
  simp only [hop2DeliverC, hop2CommitE, auxSetBad, auxMk, auxLazy, auxMade, auxIdx,
    auxCoins, auxBad, orE, pGet, pSet, gsWin, gsSt, recPos, otherE,
    Comp.cost, Expr.cost, Expr.cost_liftL, opBadAt_cost, opSpkSc_cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at htr hb hrec hacc hch ⊢
  omega

theorem hop2InjectC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).cost ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).cost ≤ c1E.cost + qE.cost + 20)
    {Γ}
    (stE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2StTy)
    (argE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.prod .bool (.base .ct))) :
    (hop2InjectC P ℓ Dh encPt encT decT s K B qep k drawBv stepC stE argE).cost ≤
      stE.cost + argE.cost + 3 * bits k + 3 * bits B + bits (qep + 1) +
        400 * (K + 1) + 3700 := by
  let G0 := .prod hop2StTy (.prod .bool (.base .ct)) :: Γ
  let G1 := (.base .rcoins) :: G0
  let G2 := (.prod hop2RecvResTy (.opt hop2UpdTy)) :: (.prod hop2OutTy hop2AuxTy) :: G1
  have htr := inTransitE_e2e_cost_le P ℓ decT encT K (.fst (.fst .v0))
    (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) (Γ := G0)
  have hb := hBv (Γ := G0)
  have hrec := hop2RecvC_cost_le P ℓ Dh encPt encT decT s K B k drawBv hBv stepC hStep
    (.fst (.snd (.fst .v1))) (.snd (.snd (.fst .v1)))
    (pGet (gsSt (.fst (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) .v0 (Γ := G1)
  have htv := trivialE_three_cost_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst (.fst .v3))
    (.pair (otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))) (Γ := G2)
  have hacc := acceptE_cost_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst (.fst .v3)) (.fst (.snd .v3))
    (.fst (.fst .v0))
    (.pair (otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))) (Γ := G2)
  simp only [hop2InjectC, hop2CommitE, auxSetBad, auxMk, auxLazy, auxMade, auxIdx,
    auxCoins, auxBad, safeInjE, healedByE, minN, leN, pGet, pSet, otherE, gsSetWin, gsMk,
    gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs,
    orE, isSomeE, Comp.cost, Expr.cost, Expr.cost_liftL, opBadAt_cost,
    opSpkSc_cost, opInjOK_cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, bits_small] at htr hb hrec htv hacc ⊢
  omega

theorem hop2ImplC_cost_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawCoins : ∀ {Γ}, Comp (spkLeakSessionSmOps P ℓ decT encT) I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ}, (drawCoins (Γ := Γ)).cost ≤ 10)
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).cost ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).cost ≤ c1E.cost + qE.cost + 20) :
    (hop2ImplC P ℓ Dh encPt encT decT s K B qep k drawCoins drawBv stepC
      (Γ := [hop2StTy, (e2eCodec Pt ℓ PQC).Q]) .v0 .v1).cost ≤
      6 * bits k + 6 * bits B + 4 * bits qep + bits (qep + 1) +
        500 * ((K + 1) * (K + 1)) + 1200 * (K + 1) + 15000 := by
  let Q1 : Ty (spkLeakSessionSig Pt ℓ PQC) := .prod .bool (.prod (.base .msg) (.opt (.base .coins)))
  let Q2 : Ty (spkLeakSessionSig Pt ℓ PQC) :=
    .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))
  let Q3 : Ty (spkLeakSessionSig Pt ℓ PQC) := .prod .bool (.base .ct)
  let G0 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) :=
    .prod hop2StTy (e2eCodec Pt ℓ PQC).Q :: [hop2StTy, (e2eCodec Pt ℓ PQC).Q]
  let G1 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum (Ty.sum (Ty.sum Q1 Q2) Q3) Q3 :: G0
  let G2 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum (Ty.sum Q1 Q2) Q3 :: G1
  let G3 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum Q1 Q2 :: G2
  have htr := transmitRC_spkS_cost_le P ℓ decT encT (I := I)
    drawCoins hCoins qep (.fst (.fst .v4)) .v0 (Γ := Q1 :: G3)
  have hch := challRC_spkS_cost_le P ℓ decT encT (I := I)
    drawCoins hCoins qep (.fst (.fst .v4)) .v0 (Γ := Q2 :: G3)
  have hdl := hop2DeliverC_cost_le P ℓ Dh encPt encT decT s K B k drawBv hBv stepC hStep
    (.fst .v3) .v0 (Γ := Q3 :: G2)
  have hij := hop2InjectC_cost_le P ℓ Dh encPt encT decT s K B qep k drawBv hBv stepC hStep
    (.fst .v2) .v0 (Γ := Q3 :: G1)
  have hcr := corrRC_spkS_cost_le P ℓ decT encT (I := I)
    K (.fst (.fst .v1)) .v0 (Γ := .bool :: G0)
  simp only [hop2ImplC, Comp.cost_liftL, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at htr hch hdl hij hcr ⊢
  omega

private theorem hop2LookupE_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (L : ℕ) {Γ}
    (l : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.list hop2EntryTy))
    (tE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ .nat)
    (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)) :
    (hop2LookupE P ℓ Dh encPt encT decT s L l tE qE).size ≤
      l.size + tE.size + qE.size + bits L + 100 := by
  simp [hop2LookupE, opEqPt, spkLeakSessionOps, Ops.sum, spkLeakOps,
    Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem hop2LazyC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).size ≤ 10)
    {Γ}
    (auxE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2AuxTy)
    (tE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ .nat)
    (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)) :
    (hop2LazyC P ℓ Dh encPt encT decT s K drawBv auxE tE qE).size ≤
      auxE.size + tE.size + qE.size + bits K + 200 := by
  have hlk := hop2LookupE_size_le P ℓ Dh encPt encT decT s K
    (auxLazy (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
    (Γ := .prod hop2AuxTy (.prod .nat (.base .key)) :: Γ)
  have hb := hBv (Γ := .prod hop2AuxTy (.prod .nat (.base .key)) :: Γ)
  simp only [hop2LazyC, auxConsLazy, auxMk, auxLazy, auxMade, auxIdx, auxCoins, auxBad,
    Comp.size, Expr.size, Expr.v0, Expr.v1] at hlk hb ⊢
  omega

private theorem hop2FinishNoneC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (B : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    {Γ}
    (aux1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2AuxTy)
    (gE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .st))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (rkckE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ
      (.prod (.base .rcoins) (.base .rcoins))) :
    (hop2FinishNoneC P ℓ Dh encPt encT decT s B (I := I) aux1E gE cE rcE rkckE).size ≤
      aux1E.size + gE.size + cE.size + rcE.size + rkckE.size + 400 := by
  simp only [hop2FinishNoneC, opSendHalfReal, opFinishHop2DH, opParseSenderKey,
    opRootCreateChain, opHasSenderChain, opAdvancePrevCounter, opPushRecvChain,
    opSetSenderChain, opSetRootKey, opTryDecryptWhisper,
    Comp.size, Expr.size, spkLeakSessionOps, Ops.sum, spkLeakOps, Sum.elim_inr, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem hop2SendHalfC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).size ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).size ≤ c1E.size + qE.size + 20)
    {Γ}
    (challE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2ChallTy)
    (idx1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.opt .nat))
    (rkME : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (q'E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)) :
    (hop2SendHalfC P ℓ Dh encPt encT decT s k drawBv stepC challE idx1E rkME cE rcE q'E).size ≤
      challE.size + idx1E.size + rkME.size + cE.size + rcE.size + q'E.size +
        2 * bits k + 500 := by
  let G0 := .nat :: .prod hop2ChallTy (.prod (.opt .nat)
    (.prod (.base .rcoins) (.prod (.base .ct) (.prod (.base .rcoins) (.base .key))))) :: Γ
  have hb := hBv (Γ := G0)
  have hst := hStep (.fst (.fst .v1)) (.snd (.snd (.snd (.snd (.snd .v1))))) (Γ := G0)
  simp only [hop2SendHalfC, opSendHalfReal, opParseSenderKey, opRootCreateChain,
    opZeroBv, opIsZeroPt, opRootExpand,
    Comp.size, Expr.size, spkLeakSessionOps, Ops.sum, spkLeakOps, Sum.elim_inr,
    Expr.v0, Expr.v1, Expr.v2, bits_small] at hb hst ⊢
  omega

private theorem hop2DHC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).size ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).size ≤ c1E.size + qE.size + 20)
    {Γ}
    (auxE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2AuxTy)
    (challE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2ChallTy)
    (tE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ .nat)
    (coinsE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
    (gE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .st))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins)) :
    (hop2DHC P ℓ Dh encPt encT decT s K B k drawBv stepC
      auxE challE tE coinsE gE cE rcE).size ≤
      auxE.size + challE.size + tE.size + coinsE.size + gE.size + cE.size + rcE.size +
        3 * bits k + bits K + bits (K + 1) + 2500 := by
  let G0 := (.base .key) :: .prod hop2AuxTy (.prod hop2ChallTy (.prod .nat
    (.prod (.base .rcoins) (.prod (.base .st) (.prod (.base .ct) (.base .rcoins)))))) :: Γ
  let G_lz := (.prod (.base .rcoins) hop2AuxTy) :: G0
  let G_ck := (.base .rcoins) :: G0
  let G_st := (.base .rcoins) :: G0
  have hlk := hop2LookupE_size_le P ℓ Dh encPt encT decT s (K + 1)
    (auxMade (.fst .v1)) (.fst (.snd (.snd .v1)))
    (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0) (Γ := G0)
  have hlz := hop2LazyC_size_le P ℓ Dh encPt encT decT s K drawBv hBv
    (.fst .v1) (.fst (.snd (.snd .v1)))
    (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0) (Γ := G0)
  have hfn1 := hop2FinishNoneC_size_le P ℓ Dh encPt encT decT s B (I := I)
    (.snd .v0) (.fst (.snd (.snd (.snd (.snd .v2)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
    (opRootExpand P ℓ Dh encPt encT decT s (.fst .v0)) (Γ := G_lz)
  have hsh := hop2SendHalfC_size_le P ℓ Dh encPt encT decT s k drawBv hBv stepC hStep
    (.fst (.snd .v2)) (.some (.add (.fst (.snd (.snd .v2))) (.nat 1)))
    (opZeroBv P ℓ Dh encPt encT decT s)
    (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
    (opDh P ℓ Dh encPt encT decT s (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))) .v1)
    (Γ := G_ck)
  have hst := hStep (.fst (.fst (.snd .v1)))
    (opDh P ℓ Dh encPt encT decT s (.fst (.snd (.snd (.snd .v1)))) .v0) (Γ := G0)
  have hfn2 := hop2FinishNoneC_size_le P ℓ Dh encPt encT decT s B (I := I)
    (.fst .v2) (.fst (.snd (.snd (.snd (.snd .v2)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v2))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
    (opRootExpand P ℓ Dh encPt encT decT s .v0) (Γ := G_st)
  simp only [hop2DHC, leN, auxMade, opDhTargetPt, opSenderKeyPt, opHasSenderChain,
    opParseSenderKey, opDecT, opIsZeroPt, opEqBytes, opEncT, orE, opFinishHop2DH,
    opAdvancePrevCounter, opPushRecvChain, opSetSenderChain, opSetRootKey,
    opTryDecryptWhisper, opRootExpand, opZeroBv, opDh,
    Comp.size, Expr.size, spkLeakSessionOps, Ops.sum, spkLeakOps, Sum.elim_inr,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    bits_small] at hlk hlz hfn1 hsh hst hfn2 ⊢
  omega

private theorem hop2RecvC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).size ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).size ≤ c1E.size + qE.size + 20)
    {Γ}
    (auxE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2AuxTy)
    (challE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2ChallTy)
    (gE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .st))
    (cE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .ct))
    (rcE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins)) :
    (hop2RecvC P ℓ Dh encPt encT decT s K B k drawBv stepC auxE challE gE cE rcE).size ≤
      auxE.size + challE.size + gE.size + cE.size + rcE.size +
        3 * bits k + bits K + bits (K + 1) + 3000 := by
  let G0 := .nat :: .prod hop2AuxTy (.prod hop2ChallTy
    (.prod (.base .st) (.prod (.base .ct) (.base .rcoins)))) :: Γ
  have hdh := hop2DHC_size_le P ℓ Dh encPt encT decT s K B k drawBv hBv stepC hStep
    (.fst .v1) (.fst (.snd .v1)) .v0
    (pGet (auxCoins (.fst .v1)) (opStParty P ℓ Dh encPt encT decT s (.fst (.snd (.snd .v1)))))
    (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
    (Γ := G0)
  simp only [hop2RecvC, opWireOk, isSomeE, opNeedsDH, opParseSenderKey, opHasRecvChain,
    opReceive, opStParty, pGet, auxIdx, auxCoins,
    Comp.size, Expr.size, spkLeakSessionOps, Ops.sum, spkLeakSessionSmOps, smOps, spkLeakOps,
    Sum.elim_inl, Sum.elim_inr, Expr.v0, Expr.v1, Expr.v2] at hdh ⊢
  omega

private theorem hop2DeliverC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).size ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).size ≤ c1E.size + qE.size + 20)
    {Γ}
    (stE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2StTy)
    (argE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.prod .bool (.base .ct))) :
    (hop2DeliverC P ℓ Dh encPt encT decT s K B k drawBv stepC stE argE).size ≤
      stE.size + argE.size + 3 * bits k + 6 * bits K + bits (K + 1) + 5000 := by
  let G0 := .prod hop2StTy (.prod .bool (.base .ct)) :: Γ
  let G1 := (.base .rcoins) :: recTy :: G0
  let G2 := (.prod hop2RecvResTy (.opt hop2UpdTy)) :: (.prod hop2OutTy hop2AuxTy) :: G1
  have htr := inTransitE_e2e_size_le P ℓ decT encT K (.fst (.fst .v0))
    (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) (Γ := G0)
  have hb := hBv (Γ := recTy :: G0)
  have hrec := hop2RecvC_size_le P ℓ Dh encPt encT decT s K B k drawBv hBv stepC hStep
    (.fst (.snd (.fst .v2))) (.snd (.snd (.fst .v2)))
    (pGet (gsSt (.fst (.fst .v2))) (.fst (.snd .v2))) (.snd (.snd .v2)) .v0 (Γ := G1)
  have hacc := acceptE_size_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst (.fst .v4)) (.fst (.snd .v4))
    (.fst (.fst .v0)) (recPos .v3) (Γ := G2)
  have hch := challContainsE_size_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst (.fst .v4)) (recPos .v3) (Γ := G2)
  simp only [hop2DeliverC, Comp.size, expr_size_liftL]
  simp only [hop2CommitE, auxSetBad, auxMk, auxLazy, auxMade, auxIdx,
    auxCoins, auxBad, orE, pGet, pSet, gsWin, gsSt, recPos, otherE,
    opBadAt, opStParty, opHasEpoch0Chain, opParseSenderKey, opEqBytes, opGenPub, opSpkSc,
    Expr.size, spkLeakSessionOps, Ops.sum, spkLeakOps, Sum.elim_inr,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at htr hb hrec hacc hch ⊢
  omega

private theorem hop2InjectC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).size ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).size ≤ c1E.size + qE.size + 20)
    {Γ}
    (stE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ hop2StTy)
    (argE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.prod .bool (.base .ct))) :
    (hop2InjectC P ℓ Dh encPt encT decT s K B qep k drawBv stepC stE argE).size ≤
      stE.size + argE.size + 3 * bits k + 7 * bits K + bits (K + 1) + bits (qep + 1) + 6000 := by
  let G0 := .prod hop2StTy (.prod .bool (.base .ct)) :: Γ
  let G1 := (.base .rcoins) :: G0
  let G2 := (.prod hop2RecvResTy (.opt hop2UpdTy)) :: (.prod hop2OutTy hop2AuxTy) :: G1
  have htr := inTransitE_e2e_size_le P ℓ decT encT K (.fst (.fst .v0))
    (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) (Γ := G0)
  have hb := hBv (Γ := G0)
  have hrec := hop2RecvC_size_le P ℓ Dh encPt encT decT s K B k drawBv hBv stepC hStep
    (.fst (.snd (.fst .v1))) (.snd (.snd (.fst .v1)))
    (pGet (gsSt (.fst (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) .v0 (Γ := G1)
  have htv := trivialE_three_size_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst (.fst .v3))
    (.pair (otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))) (Γ := G2)
  have hacc := acceptE_size_le (O' := spkLeakSessionOps P ℓ Dh encPt encT decT s) K
    (.fst (.fst .v3)) (.fst (.snd .v3))
    (.fst (.fst .v0))
    (.pair (otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))) (Γ := G2)
  simp only [hop2InjectC, orE, isSomeE, Comp.size, Expr.size, expr_size_liftL]
  simp only [hop2CommitE, auxSetBad, auxMk, auxLazy, auxMade, auxIdx,
    auxCoins, auxBad, safeInjE, healedByE, minN, leN, pGet, pSet, otherE, gsSetWin, gsMk,
    gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs,
    opBadAt, opStParty, opHasEpoch0Chain, opParseSenderKey, opEqBytes, opGenPub,
    opSpkSc, opInjOK, Expr.size,
    spkLeakSessionOps, Ops.sum, spkLeakSessionSmOps, smOps, spkLeakOps,
    Sum.elim_inl, Sum.elim_inr,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, bits_small] at htr hb hrec htv hacc ⊢
  omega

theorem hop2ImplC_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    (drawCoins : ∀ {Γ}, Comp (spkLeakSessionSmOps P ℓ decT encT) I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ}, (drawCoins (Γ := Γ)).size ≤ 10)
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).size ≤ 10)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).size ≤ c1E.size + qE.size + 20) :
    (hop2ImplC P ℓ Dh encPt encT decT s K B qep k drawCoins drawBv stepC
      (Γ := [hop2StTy, (e2eCodec Pt ℓ PQC).Q]) .v0 .v1).size ≤
      6 * bits k + 50 * bits K + 2 * bits (K + 1) + 4 * bits qep + bits (qep + 1) + 25000 := by
  let Q1 : Ty (spkLeakSessionSig Pt ℓ PQC) := .prod .bool (.prod (.base .msg) (.opt (.base .coins)))
  let Q2 : Ty (spkLeakSessionSig Pt ℓ PQC) :=
    .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))
  let Q3 : Ty (spkLeakSessionSig Pt ℓ PQC) := .prod .bool (.base .ct)
  let G0 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) :=
    .prod hop2StTy (e2eCodec Pt ℓ PQC).Q :: [hop2StTy, (e2eCodec Pt ℓ PQC).Q]
  let G1 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum (Ty.sum (Ty.sum Q1 Q2) Q3) Q3 :: G0
  let G2 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum (Ty.sum Q1 Q2) Q3 :: G1
  let G3 : List (Ty (spkLeakSessionSig Pt ℓ PQC)) := Ty.sum Q1 Q2 :: G2
  have htr := transmitRC_spkS_size_le P ℓ decT encT (I := I)
    drawCoins hCoins qep (.fst (.fst .v4)) .v0 (Γ := Q1 :: G3)
  have hch := challRC_spkS_size_le P ℓ decT encT (I := I)
    drawCoins hCoins qep (.fst (.fst .v4)) .v0 (Γ := Q2 :: G3)
  have hdl := hop2DeliverC_size_le P ℓ Dh encPt encT decT s K B k drawBv hBv stepC hStep
    (.fst .v3) .v0 (Γ := Q3 :: G2)
  have hij := hop2InjectC_size_le P ℓ Dh encPt encT decT s K B qep k drawBv hBv stepC hStep
    (.fst .v2) .v0 (Γ := Q3 :: G1)
  have hcr := corrRC_spkS_size_le P ℓ decT encT (I := I)
    K (.fst (.fst .v1)) .v0 (Γ := .bool :: G0)
  simp only [hop2ImplC, comp_size_liftL, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at htr hch hdl hij hcr ⊢
  omega

theorem hop2GameRedProg_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (K B qep k : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface (spkLeakSessionSig Pt ℓ PQC) T}
    {rIn : Ty (spkLeakSessionSig Pt ℓ PQC)}
    (drawBool : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ .bool)
    (hBool : ∀ {Γ}, (drawBool (Γ := Γ)).size ≤ 10)
    (drawCoins : ∀ {Γ}, Comp (spkLeakSessionSmOps P ℓ decT encT) I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ}, (drawCoins (Γ := Γ)).size ≤ 10)
    (drawBv : ∀ {Γ}, Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hBv : ∀ {Γ}, (drawBv (Γ := Γ)).size ≤ 10)
    (initChall : Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I [rIn] hop2ChallTy)
    (hChall : initChall.size ≤ 30)
    (stepC : ∀ {Γ},
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins) →
      Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key) →
      Comp (spkLeakSessionOps P ℓ Dh encPt encT decT s) I Γ (.base .rcoins))
    (hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
      (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
      (stepC c1E qE).size ≤ c1E.size + qE.size + 20) :
    (hop2GameRedProg P ℓ Dh encPt encT decT s K B qep k
      drawBool drawCoins drawBv initChall stepC).size ≤
      8 * bits k + 50 * bits K + 2 * bits (K + 1) + 4 * bits qep + bits (qep + 1) + 26000 := by
  have hh := hop2ImplC_size_le P ℓ Dh encPt encT decT s K B qep k
    drawCoins hCoins drawBv hBv stepC hStep
  have hb0 := hBool (Γ := hop2ChallTy :: hop2ChallTy :: [rIn])
  have hbv1 := hBv (Γ := .bool :: hop2ChallTy :: hop2ChallTy :: [rIn])
  have hbv2 := hBv (Γ := .base .rcoins :: .bool :: hop2ChallTy :: hop2ChallTy :: [rIn])
  have hbv3 := hBv (Γ := .base .rcoins :: .base .rcoins :: .bool :: hop2ChallTy :: hop2ChallTy :: [rIn])
  have hbv4 := hBv (Γ := .base .rcoins :: .base .rcoins :: .base .rcoins :: .bool ::
    hop2ChallTy :: hop2ChallTy :: [rIn])
  have hbv5 := hBv (Γ := .base .rcoins :: .base .rcoins :: .base .rcoins :: .base .rcoins ::
    .bool :: hop2ChallTy :: hop2ChallTy :: [rIn])
  simp only [CostedReduction.size, hop2GameRedProg, hop2InitAfterChallC,
    opZeroBv, opBasePt, opDh, opInitA, opInitB, opSetPendingPreKey, opSetSenderChain,
    opAddRecvChain, opNewSession, opGenPub, gsMk, auxMk, auxBad,
    Comp.size, Expr.size, spkLeakSessionOps, Ops.sum, spkLeakOps, Sum.elim_inr,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
    bits_small] at hh hb0 hbv1 hbv2 hbv3 hbv4 hbv5 hChall ⊢
  omega

theorem hop2PrgRedKProg_gRedBounded {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (q qep k : ℕ) (hk : k ≤ qep + 9) (hqep : qep ≤ q + 10) :
    GRedBounded
      (hop2PrgRedKProg P ℓ Dh encPt encT decT s q (max (q + 1) (2 ^ 32)) qep k)
      Empty.elim (fun _ => 0) q 0
      (ratchetCostBudget q qep + 2 ^ 12 * (q + 1) ^ 2 * q) := by
  let B3 := ratchetCostBudget q qep + 2 ^ 12 * (q + 1) ^ 2 * q
  refine gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 B3
    ?_ ?_ ?_ (e2eFullOps_sizeHonest P ℓ Dh encPt encT decT s) (e2ePrgSamp_sizeHonest ℓ (PQC := PQC))
  · rw [hop2PrgRedKProg_totalCost]
    have hCoins : ∀ {Γ}, (prgDrawCoins ℓ (Pt := Pt) (PQC := PQC)
        (O' := spkLeakSessionSmOps P ℓ decT encT) (Γ := Γ)).cost ≤ 10 := by
      intro Γ
      simp [prgDrawCoins, e2ePrgIface, Samplers.sum, Iface.withSamp, prgIface, unifSamplers,
        Sum.elim_inr, Comp.cost, Expr.cost, Expr.v0]
    have hBv : ∀ {Γ}, (prgDrawBv P ℓ Dh encPt encT decT s (Γ := Γ)).cost ≤ 10 := by
      intro Γ
      simp [prgDrawBv, e2ePrgIface, Samplers.sum, Iface.withSamp, prgIface, unifSamplers,
        Sum.elim_inr, Comp.cost, Expr.cost]
    have hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
        (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
        (Comp.ret (I := e2ePrgIface Pt ℓ PQC)
          (opExtractTag P ℓ Dh encPt encT decT s c1E qE)).cost ≤ c1E.cost + qE.cost + 20 := by
      intro Γ c1E qE
      simp [Comp.cost]
    have hh := hop2ImplC_cost_le P ℓ Dh encPt encT decT s
      q (max (q + 1) (2 ^ 32)) qep k (prgDrawCoins ℓ (PQC := PQC)) hCoins
      (prgDrawBv P ℓ Dh encPt encT decT s) hBv
      (fun c1E qE => .ret (opExtractTag P ℓ Dh encPt encT decT s c1E qE)) hStep
    change (hop2PrgRedKProg P ℓ Dh encPt encT decT s
      q (max (q + 1) (2 ^ 32)) qep k).handle.cost ≤ _ at hh
    have hbB := bits_max_q_pow32 q
    have hb : 1 ≤ bits qep := ReductionDsl.one_le_bits qep
    have hbq1 : bits (qep + 1) ≤ bits qep + 1 := by
      have hadd := ReductionDsl.bits_add qep 1
      have h1 : bits 1 = 1 := rfl
      omega
    have hbk : bits k ≤ bits qep + 5 := by
      have hm := ReductionDsl.bits_mono hk
      have hadd := ReductionDsl.bits_add qep 9
      have h9 : bits 9 = 4 := by decide
      omega
    set M := q + maxForwardJumps + bits qep
    have hM_big : 25001 ≤ M := by dsimp [M, maxForwardJumps]; omega
    have hqM : q + 1 ≤ M := by dsimp [M, maxForwardJumps]; omega
    have hbqM : bits qep ≤ M := by dsimp [M]; omega
    have hhand :
        (hop2PrgRedKProg P ℓ Dh encPt encT decT s
          q (max (q + 1) (2 ^ 32)) qep k).handle.cost + 6 ≤ 510 * (q + 1) * M := by
      nlinarith
    have hmul := Nat.mul_le_mul_left q hhand
    have hB3 : 2 ^ 12 * (q + 1) ^ 2 * M = B3 := by
      dsimp [B3, M]; unfold ratchetCostBudget; ring
    have hinit : 2 * bits k + 136 +
        q * ((hop2PrgRedKProg P ℓ Dh encPt encT decT s
          q (max (q + 1) (2 ^ 32)) qep k).handle.cost + 6) ≤ 2 ^ 12 * (q + 1) ^ 2 * M := by
      nlinarith
    omega
  · have hs := hop2GameRedProg_size_le P ℓ Dh encPt encT decT s
      q (max (q + 1) (2 ^ 32)) qep k (I := e2ePrgIface Pt ℓ PQC)
      (rIn := .prod (.base .rcoins) (.base .rcoins))
      (prgDrawBool P ℓ Dh encPt encT decT s)
      (fun {Γ} => by simp [prgDrawBool, Comp.size, Expr.size])
      (prgDrawCoins ℓ (PQC := PQC))
      (fun {Γ} => by simp [prgDrawCoins, Comp.size, Expr.size, Expr.v0])
      (prgDrawBv P ℓ Dh encPt encT decT s)
      (fun {Γ} => by simp [prgDrawBv, Comp.size, Expr.size])
      (.ret .v0) (by simp [Comp.size, Expr.size, Expr.v0])
      (fun c1E qE => .ret (opExtractTag P ℓ Dh encPt encT decT s c1E qE))
      (fun c1E qE => by simp [opExtractTag, spkLeakSessionOps, Ops.sum, spkLeakOps,
        Comp.size, Expr.size])
    change (hop2PrgRedKProg P ℓ Dh encPt encT decT s
      q (max (q + 1) (2 ^ 32)) qep k).size ≤ _ at hs
    have hq_cb : q ≤ B3 := by
      dsimp [B3]; unfold ratchetCostBudget maxForwardJumps; nlinarith
    have hqep_cb : qep ≤ B3 := by
      dsimp [B3]; unfold ratchetCostBudget maxForwardJumps; nlinarith
    have hbq : bits q ≤ bits B3 := ReductionDsl.bits_mono hq_cb
    have hbqp : bits qep ≤ bits B3 := ReductionDsl.bits_mono hqep_cb
    have hbq1 : bits (q + 1) ≤ bits q + 2 := by
      have h1 := ReductionDsl.bits_add q 1; have h2 : bits 1 = 1 := rfl; omega
    have hbqp1 : bits (qep + 1) ≤ bits qep + 2 := by
      have h1 := ReductionDsl.bits_add qep 1; have h2 : bits 1 = 1 := rfl; omega
    have hbk : bits k ≤ bits qep + 6 := by
      have h1 := ReductionDsl.bits_mono hk; have h2 := ReductionDsl.bits_add qep 9
      have h3 : bits 9 = 4 := rfl; omega
    unfold reductionSizeBudget
    omega
  · simp [CostedReduction.totalQueries]

theorem hop2PrfRedKProg_gRedBounded {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {PQC : Type} [SampleableType PQC]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (q qep k : ℕ) (hk : k ≤ qep + 9) (hqep : qep ≤ q + 10) :
    GRedBounded
      (hop2PrfRedKProg P ℓ Dh encPt encT decT s q (max (q + 1) (2 ^ 32)) qep k)
      (fun _ => 1) (fun _ => 0) q q
      (ratchetCostBudget q qep + 2 ^ 12 * (q + 1) ^ 2 * q) := by
  let B3 := ratchetCostBudget q qep + 2 ^ 12 * (q + 1) ^ 2 * q
  refine gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q B3
    ?_ ?_ ?_ (e2eFullOps_sizeHonest P ℓ Dh encPt encT decT s) (e2ePrfSamp_sizeHonest ℓ (PQC := PQC))
  · rw [hop2PrfRedKProg_totalCost]
    have hCoins : ∀ {Γ}, (spkDrawCoins ℓ (Pt := Pt) (PQC := PQC)
        (O' := spkLeakSessionSmOps P ℓ decT encT) (Γ := Γ)).cost ≤ 10 := by
      intro Γ
      simp [spkDrawCoins, e2ePrfIface, Samplers.sum, Iface.withSamp, prfIface, unifSamplers,
        Sum.elim_inr, Comp.cost, Expr.cost, Expr.v0]
    have hBv : ∀ {Γ}, (spkDrawBv P ℓ Dh encPt encT decT s (Γ := Γ)).cost ≤ 10 := by
      intro Γ
      simp [spkDrawBv, e2ePrfIface, Samplers.sum, Iface.withSamp, prfIface, unifSamplers,
        Sum.elim_inr, Comp.cost, Expr.cost]
    have hStep : ∀ {Γ} (c1E : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .rcoins))
        (qE : Expr (spkLeakSessionOps P ℓ Dh encPt encT decT s) Γ (.base .key)),
        (Comp.query (I := e2ePrfIface Pt ℓ PQC) () qE).cost ≤ c1E.cost + qE.cost + 20 := by
      intro Γ c1E qE
      simp [e2ePrfIface, Iface.withSamp, prfIface, Comp.cost]
      omega
    have hh := hop2ImplC_cost_le P ℓ Dh encPt encT decT s
      q (max (q + 1) (2 ^ 32)) qep k (spkDrawCoins ℓ (PQC := PQC)) hCoins
      (spkDrawBv P ℓ Dh encPt encT decT s) hBv
      (fun _ qE => .query () qE) hStep
    change (hop2PrfRedKProg P ℓ Dh encPt encT decT s
      q (max (q + 1) (2 ^ 32)) qep k).handle.cost ≤ _ at hh
    have hbB := bits_max_q_pow32 q
    have hb : 1 ≤ bits qep := ReductionDsl.one_le_bits qep
    have hbq1 : bits (qep + 1) ≤ bits qep + 1 := by
      have hadd := ReductionDsl.bits_add qep 1
      have h1 : bits 1 = 1 := rfl
      omega
    have hbk : bits k ≤ bits qep + 5 := by
      have hm := ReductionDsl.bits_mono hk
      have hadd := ReductionDsl.bits_add qep 9
      have h9 : bits 9 = 4 := by decide
      omega
    set M := q + maxForwardJumps + bits qep
    have hM_big : 25001 ≤ M := by dsimp [M, maxForwardJumps]; omega
    have hqM : q + 1 ≤ M := by dsimp [M, maxForwardJumps]; omega
    have hbqM : bits qep ≤ M := by dsimp [M]; omega
    have hhand :
        (hop2PrfRedKProg P ℓ Dh encPt encT decT s
          q (max (q + 1) (2 ^ 32)) qep k).handle.cost + 6 ≤ 510 * (q + 1) * M := by
      nlinarith
    have hmul := Nat.mul_le_mul_left q hhand
    have hB3 : 2 ^ 12 * (q + 1) ^ 2 * M = B3 := by
      dsimp [B3, M]; unfold ratchetCostBudget; ring
    have hinit : 2 * bits k + 144 +
        q * ((hop2PrfRedKProg P ℓ Dh encPt encT decT s
          q (max (q + 1) (2 ^ 32)) qep k).handle.cost + 6) ≤ 2 ^ 12 * (q + 1) ^ 2 * M := by
      nlinarith
    omega
  · have hs := hop2GameRedProg_size_le P ℓ Dh encPt encT decT s
      q (max (q + 1) (2 ^ 32)) qep k (I := e2ePrfIface Pt ℓ PQC) (rIn := .unit)
      (spkDrawBool P ℓ Dh encPt encT decT s)
      (fun {Γ} => by simp [spkDrawBool, Comp.size, Expr.size])
      (spkDrawCoins ℓ (PQC := PQC))
      (fun {Γ} => by simp [spkDrawCoins, Comp.size, Expr.size, Expr.v0])
      (spkDrawBv P ℓ Dh encPt encT decT s)
      (fun {Γ} => by simp [spkDrawBv, Comp.size, Expr.size])
      (.bind (spkDrawBv P ℓ Dh encPt encT decT s)
        (.bind (spkDrawBv P ℓ Dh encPt encT decT s) (.ret (.pair .v1 .v0))))
      (by simp [spkDrawBv, Comp.size, Expr.size, Expr.v0, Expr.v1])
      (fun _ qE => .query () qE)
      (fun c1E qE => by simp [e2ePrfIface, Iface.withSamp, prfIface, Comp.size]; omega)
    change (hop2PrfRedKProg P ℓ Dh encPt encT decT s
      q (max (q + 1) (2 ^ 32)) qep k).size ≤ _ at hs
    have hq_cb : q ≤ B3 := by
      dsimp [B3]; unfold ratchetCostBudget maxForwardJumps; nlinarith
    have hqep_cb : qep ≤ B3 := by
      dsimp [B3]; unfold ratchetCostBudget maxForwardJumps; nlinarith
    have hbq : bits q ≤ bits B3 := ReductionDsl.bits_mono hq_cb
    have hbqp : bits qep ≤ bits B3 := ReductionDsl.bits_mono hqep_cb
    have hbq1 : bits (q + 1) ≤ bits q + 2 := by
      have h1 := ReductionDsl.bits_add q 1; have h2 : bits 1 = 1 := rfl; omega
    have hbqp1 : bits (qep + 1) ≤ bits qep + 2 := by
      have h1 := ReductionDsl.bits_add qep 1; have h2 : bits 1 = 1 := rfl; omega
    have hbk : bits k ≤ bits qep + 6 := by
      have h1 := ReductionDsl.bits_mono hk; have h2 := ReductionDsl.bits_add qep 9
      have h3 : bits 9 = 4 := rfl; omega
    unfold reductionSizeBudget
    omega
  · simp [CostedReduction.totalQueries, hop2PrfRedKProg, hop2GameRedProg, hop2InitAfterChallC,
      hop2ImplC, hop2DeliverC, hop2InjectC, hop2RecvC, hop2DHC, hop2FinishNoneC, hop2SendHalfC,
      hop2LazyC, spkDrawBool, spkDrawBv, spkDrawCoins, Comp.queries, Comp.queries_liftL]

end GRedBoundedE2E

end CryptoVerification.E2E.Costed
