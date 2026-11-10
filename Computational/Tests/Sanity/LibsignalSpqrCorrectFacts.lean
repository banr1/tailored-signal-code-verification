/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrCorrect
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip

/-!
# Sanity Properties of the SPQR Window and `SpqrHonestCorrect`

**Checked by Lean.** Sanity checks for `Spqr.withLog`, `spqrWindowOk`, and `SpqrHonestCorrect`:
projection of `Spqr.withLog S` onto `S`, kernel-decided inclusion of in-order and reordered honest
schedules in `spqrWindowOk` alongside exclusion of the epoch-retention, `KeyJump`, and `KeyTrimmed`
boundary cases, satisfiability of `SpqrHonestCorrect` via `SpqrOffCorrect` (`idealSpqr`), and win
characterizations for `spqrDeliverStep`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped OracleSpec.PrimitiveQuery

namespace CryptoGames
namespace LibsignalSpqrCorrectFacts

open LibsignalSession LibsignalSM.Corr HKDF

variable {PQ PQC : Type}

theorem withLog_init_fst (S : Spqr PQ PQC) (dir : SpqrDirection) (k : BitVec 256) :
    (S.withLog.init dir k).1 = S.init dir k := rfl

theorem withLog_init_snd (S : Spqr PQ PQC) (dir : SpqrDirection) (k : BitVec 256) :
    (S.withLog.init dir k).2 = default := rfl

theorem withLog_send_map (S : Spqr PQ PQC) (st : PQ × SpqrLog) (r : PQC) :
    (S.withLog.send st r).map (fun x => (x.1.1, x.2.1, x.2.2)) = S.send st.1 r := by
  simp only [Spqr.withLog, Option.map_map]
  cases S.send st.1 r <;> rfl

theorem withLog_send_isSome (S : Spqr PQ PQC) (st : PQ × SpqrLog) (r : PQC) :
    (S.withLog.send st r).isSome = (S.send st.1 r).isSome := by
  simp only [Spqr.withLog, Option.isSome_map]

theorem withLog_send_eq_some (S : Spqr PQ PQC) (st : PQ × SpqrLog) (r : PQC) (st' : PQ)
    (salt : Salt) (msg : List (BitVec 8)) (h : S.send st.1 r = some (st', salt, msg)) :
    S.withLog.send st r = some ((st', { st.2 with sent := msg :: st.2.sent }), salt, msg) := by
  simp only [Spqr.withLog, h, Option.map_some]

theorem withLog_recv_map (S : Spqr PQ PQC) (st : PQ × SpqrLog) (msg : List (BitVec 8)) :
    (S.withLog.recv st msg).map (fun x => (x.1.1, x.2)) = S.recv st.1 msg := by
  simp only [Spqr.withLog]
  cases S.recv st.1 msg <;> rfl

theorem withLog_recv_eq_ok (S : Spqr PQ PQC) (st : PQ × SpqrLog) (msg : List (BitVec 8)) (st' : PQ)
    (salt : Salt) (h : S.recv st.1 msg = .ok (st', salt)) :
    S.withLog.recv st msg = .ok ((st', { st.2 with recvd := msg :: st.2.recvd }), salt) := by
  simp only [Spqr.withLog, h]
  rfl

theorem withLog_recv_eq_error (S : Spqr PQ PQC) (st : PQ × SpqrLog) (msg : List (BitVec 8))
    (e : Bool) (h : S.recv st.1 msg = .error e) : S.withLog.recv st msg = .error e := by
  simp only [Spqr.withLog, h]
  rfl

theorem withSpqrLog_eq (P : LibsignalSession.Params PQ PQC) :
    P.withSpqrLog = ⟨P.C, P.codec, P.spqr.withLog, P.idA, P.idB, P.addrAB, P.addrBA⟩ := rfl

theorem default_fst [Inhabited PQ] : (default : PQ × SpqrLog).1 = (default : PQ) := rfl

/-- Unsigned LEB128 encoding bounded by `fuel` bytes, inverse to SPQR's `decode_varint` on small
naturals. -/
 def varint : ℕ → ℕ → List (BitVec 8)
  | 0, _ => []
  | fuel + 1, n => if n < 128 then [BitVec.ofNat 8 n]
      else BitVec.ofNat 8 (n % 128 + 128) :: varint fuel (n / 128)

/-- Minimal SPQR V1 message with header `(E, i)` and a 1-byte dummy payload. -/
 def spqrMsg (E i : ℕ) : List (BitVec 8) := 1#8 :: (varint 5 E ++ varint 5 i ++ [0#8])

/-- Spot-checks `spqrPos` on 1-, 2-, and 3-byte varint headers. -/
theorem spqrPos_spqrMsg :
    spqrPos (spqrMsg 1 1) = some (1, 1) ∧ spqrPos (spqrMsg 3 300) = some (3, 300) ∧
      spqrPos (spqrMsg 1 40000) = some (1, 40000) ∧ spqrPos (spqrMsg 2 3000) = some (2, 3000) := by
  decide +kernel

/-- Checks that every message in `msgs` satisfies `spqrWindowOk` upon arrival while logging each
delivery to `recvd`. -/
 def deliverAll (log : SpqrLog) : List (List (BitVec 8)) → Bool
  | [] => true
  | m :: ms => spqrWindowOk log m && deliverAll { log with recvd := m :: log.recvd } ms

/-- In-window checks for in-order delivery, out-of-order delivery, epoch-2 arrival after the
receiver has sent in header epoch 3 (`maxSendEpoch = 3 ≤ 2 + 1`), and a jump of `25000`. -/
theorem honest_schedules_in_window :
    deliverAll default ((List.range 5).map fun k => spqrMsg 1 (k + 1)) = true ∧
      deliverAll default [spqrMsg 1 3, spqrMsg 1 1, spqrMsg 1 5, spqrMsg 1 2, spqrMsg 1 4] = true ∧
      deliverAll ⟨[spqrMsg 3 1, spqrMsg 2 1], [spqrMsg 1 2, spqrMsg 1 1]⟩
        [spqrMsg 2 1, spqrMsg 2 2] = true ∧
      deliverAll default [spqrMsg 1 25000] = true := by
  decide +kernel

/-- Simulates alternating bursts `(as, bs)` of `(E, i)` headers between `A` and `B`, logging newest
entries first as in `Spqr.withLog`, and returns `true` iff every delivery satisfies `spqrWindowOk`. -/
 def alternate (logA logB : SpqrLog) :
    List (List (ℕ × ℕ) × List (ℕ × ℕ)) → Bool
  | [] => true
  | (as, bs) :: rest =>
    let ma := as.map fun p => spqrMsg p.1 p.2
    let mb := bs.map fun p => spqrMsg p.1 p.2
    let logA := { logA with sent := ma.reverse ++ logA.sent }
    deliverAll logB ma &&
      let logB := { logB with recvd := ma.reverse ++ logB.recvd, sent := mb.reverse ++ logB.sent }
      deliverAll logA mb &&
        alternate { logA with recvd := mb.reverse ++ logA.recvd } logB rest

/-- Alternating two-party burst schedule across five epochs exercising the retention boundary
(`maxSendEpoch = 4 = 3 + 1` when `B`'s epoch-3 messages arrive at `A`). -/
theorem honest_alternating_schedule_in_window :
    alternate default default
      [([(1, 1)], [(1, 1)]),
       ([(1, 2), (1, 3)], [(1, 2)]),
       ([(2, 1)], [(1, 3), (2, 1)]),
       ([(2, 2), (2, 3), (2, 4)], [(2, 2)]),
       ([(3, 1)], [(3, 1)]),
       ([(3, 2)], [(3, 2), (3, 3)]),
       ([(4, 1)], [(3, 4)]),
       ([(4, 2)], [(4, 1)]),
       ([(5, 1), (5, 2)], [(4, 2), (5, 1)])] = true := by
  decide +kernel

theorem replay_not_in_window :
    spqrWindowOk ⟨[], [spqrMsg 1 2, spqrMsg 1 3]⟩ (spqrMsg 1 2) = false ∧
      spqrWindowOk ⟨[], [spqrMsg 1 2, spqrMsg 1 3]⟩ (spqrMsg 1 3) = false := by
  decide +kernel

/-- Epoch retention (`EpochOutOfRange(0)`): once the receiver has sent in header epoch `3`, a
withheld header-epoch-`1` message falls outside `spqrWindowOk`, whereas header epoch `2` stays inside. -/
theorem cex_epoch_retention :
    spqrWindowOk ⟨[spqrMsg 3 1, spqrMsg 2 50], [spqrMsg 1 50]⟩ (spqrMsg 1 1) = false ∧
      spqrWindowOk ⟨[spqrMsg 2 50], [spqrMsg 1 50]⟩ (spqrMsg 1 1) = true := by
  decide +kernel

/-- Forward jump bound (`KeyJump`): from accepted index `1`, index `25001` (jump `25000`) is inside
`spqrWindowOk`, while `25002` and `40000` are outside. -/
theorem cex_key_jump :
    spqrWindowOk ⟨[spqrMsg 2 1], [spqrMsg 1 1]⟩ (spqrMsg 1 40000) = false ∧
      spqrWindowOk ⟨[spqrMsg 2 1], [spqrMsg 1 1]⟩ (spqrMsg 1 25001) = true ∧
      spqrWindowOk ⟨[spqrMsg 2 1], [spqrMsg 1 1]⟩ (spqrMsg 1 25002) = false := by
  decide +kernel

/-- Backward trim bound (`KeyTrimmed`): at frontier index `3000`, index `1000` (`2000` behind) is
inside `spqrWindowOk`, while `999` and `1` are outside. -/
theorem cex_key_trimmed :
    spqrWindowOk ⟨[spqrMsg 2 1], [spqrMsg 1 3000, spqrMsg 1 1500]⟩ (spqrMsg 1 1) = false ∧
      spqrWindowOk ⟨[spqrMsg 2 1], [spqrMsg 1 3000, spqrMsg 1 1500]⟩ (spqrMsg 1 1000) = true ∧
      spqrWindowOk ⟨[spqrMsg 2 1], [spqrMsg 1 3000, spqrMsg 1 1500]⟩ (spqrMsg 1 999) = false := by
  decide +kernel

/-- Malformed preambles without a valid position `E ≥ 1` satisfy `spqrWindowOk` (fail-closed: the
game still requires correctness on them). -/
theorem window_fail_closed (log : SpqrLog) :
    spqrWindowOk log [] = true ∧ spqrWindowOk log [1#8, 0#8, 1#8] = true := by
  constructor <;> rfl

def SpqrNoPanic (S : Spqr PQ PQC) : Prop :=
  (∀ st r, S.sendPanics st r = false) ∧ (∀ st msg, S.recvPanics st msg = false)

theorem spqrNoPanic_of_spqrOffCorrect {S : Spqr PQ PQC} (hS : SpqrOffCorrect S) : SpqrNoPanic S :=
  hS.2.2

/-- Invariant for `SpqrOffCorrect`: `win = false` and every entry in `s.sent` arises from `S.send`. -/
private def HonestInv (S : Spqr PQ PQC) (s : SpqrGameState PQ) : Prop :=
  s.win = false ∧ ∀ e ∈ s.sent, ∃ st r st', S.send st r = some (st', e.2.2, e.2.1)

private theorem sendStep_inv (S : Spqr PQ PQC) (hS : SpqrOffCorrect S) (hNP : SpqrNoPanic S)
    (s : SpqrGameState PQ) (hs : HonestInv S s) (P : Party) (r : PQC) :
    HonestInv S (spqrSendStep S s P r).2 := by
  obtain ⟨hw, hsent⟩ := hs
  obtain ⟨⟨st', salt, msg⟩, hsome⟩ := Option.isSome_iff_exists.mp (hS.1 (s.st P).1 r)
  have hlog := withLog_send_eq_some S (s.st P) r st' salt msg hsome
  have hnp : S.withLog.sendPanics (s.st P) r = false := hNP.1 _ _
  simp only [spqrSendStep, hw, hnp, hlog, Bool.false_eq_true, ↓reduceIte]
  refine ⟨rfl, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hsent e he
  · rw [List.mem_singleton.mp he]
    exact ⟨_, _, _, hsome⟩

private theorem deliverStep_inv (S : Spqr PQ PQC) (hS : SpqrOffCorrect S) (hNP : SpqrNoPanic S)
    (s : SpqrGameState PQ) (hs : HonestInv S s) (P : Party) (j : ℕ) (commit : Bool) :
    HonestInv S (spqrDeliverStep S s P j commit).2 := by
  obtain ⟨hw, hsent⟩ := hs
  have hnp : ∀ msg, S.withLog.recvPanics (s.st P) msg = false := fun _ => hNP.2 _ _
  unfold spqrDeliverStep
  simp only [hw, hnp, Bool.false_eq_true, ↓reduceIte]
  cases hj : s.sent[j]? with
  | none => exact ⟨hw, hsent⟩
  | some e =>
    obtain ⟨Q, msg, salt⟩ := e
    have hmem : (Q, msg, salt) ∈ s.sent := List.mem_of_getElem? hj
    obtain ⟨st, r, st', hsend⟩ := hsent _ hmem
    obtain ⟨st₂', hrecv⟩ := hS.2.1 st r st' salt msg hsend (s.st P).1
    have hlog := withLog_recv_eq_ok S (s.st P) msg st₂' salt hrecv
    simp only [hlog]
    split
    · exact ⟨hw, hsent⟩
    · split <;> exact ⟨by simp, hsent⟩

private def StepInv {ι σ : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) : Prop :=
  ∀ t σ0, Inv σ0 → ∀ z ∈ support ((impl t).run σ0), Inv z.2

private theorem simulateQ_run_inv {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop) (himpl : StepInv impl Inv) :
    ∀ oa : OracleComp spec α, ∀ σ0, Inv σ0 → ∀ z ∈ support ((simulateQ impl oa).run σ0), Inv z.2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro σ0 hσ0 z hz
      simp_all
  | query_bind t oa ih =>
      intro σ0 hσ0 z hz
      have hz' : z ∈ support
          (((simulateQ impl (OracleSpec.query t : OracleComp spec (spec.Range t))).run σ0) >>=
            fun us => (simulateQ impl (oa us.1)).run us.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using hz
      rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
      have hus' : us ∈ support ((impl t).run σ0) := by
        simpa [simulateQ_spec_query] using hus
      exact ih us.1 us.2 (himpl t σ0 hσ0 us hus') z hzcont

private theorem impl_inv [SampleableType PQC] (S : Spqr PQ PQC) (hS : SpqrOffCorrect S)
    (hNP : SpqrNoPanic S) :
    StepInv ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SpqrGameState PQ) ProbComp) + spqrImpl S) (HonestInv S) := by
  rintro (t | ((P | ⟨P, j, commit⟩) | P)) σ0 h0 z hz
  · simp at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact h0
  · simp [spqrImpl, spqrSendImpl] at hz
    obtain ⟨r, -, rfl⟩ := hz
    exact sendStep_inv S hS hNP σ0 h0 P r
  · simp [spqrImpl, spqrDeliverImpl] at hz
    subst hz
    exact deliverStep_inv S hS hNP σ0 h0 P j commit
  · simp [spqrImpl, spqrCorrImpl] at hz
    subst hz
    exact h0

/-- Under `SpqrOffCorrect`, `spqrGame` maintains `win = false` on all reachable states, giving
`SpqrHonestCorrect S q 0`. -/
theorem spqrHonestCorrect_of_spqrOffCorrect [SampleableType PQC] (S : Spqr PQ PQC)
    (hS : SpqrOffCorrect S) (q : ℕ) : SpqrHonestCorrect S q 0 := by
  have hNP := spqrNoPanic_of_spqrOffCorrect hS
  intro A _
  have hinv := simulateQ_run_inv _ (HonestInv S) (impl_inv S hS hNP) A
  have hnot : true ∉ support (spqrGame S A) := by
    simp only [spqrGame, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      not_exists]
    intro k _ z hz hwin
    have := (hinv _ ⟨rfl, by simp⟩ z hz).1
    rw [this] at hwin
    exact absurd hwin (by decide)
  have h0 : 𝒟[spqrGame S A] {true} = 0 := by
    by_contra hne
    exact hnot ((mem_support_iff_evalDist_singleton_pos _ _).mpr (pos_iff_ne_zero.mpr hne))
  rw [h0]

/-- Trivial one-state `Spqr` instance whose `send` and `recv` always succeed with empty messages
and `none` salt. -/
def idealSpqr : Spqr Unit Unit where
  init _ _ := ()
  send _ _ := some ((), none, [])
  recv _ _ := .ok ((), none)
  sendPanics _ _ := false
  recvPanics _ _ := false

theorem idealSpqr_spqrOffCorrect : SpqrOffCorrect idealSpqr := by
  refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  rintro _ _ _ salt msg h st₂
  simp only [idealSpqr, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  exact ⟨(), rfl⟩

theorem idealSpqr_spqrNoPanic : SpqrNoPanic idealSpqr :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem idealSpqr_spqrHonestCorrect (q : ℕ) : SpqrHonestCorrect idealSpqr q 0 :=
  spqrHonestCorrect_of_spqrOffCorrect idealSpqr idealSpqr_spqrOffCorrect q

/-- `BitVec 512` has a `SampleableType` instance, matching the uniform coin type of
`spqrV1SessionUniformCoins`. -/
example : SampleableType (BitVec 512) := inferInstance

/-- Accepting an honest message in `spqrDeliverStep` with `salt' ≠ salt` sets `win = true`
regardless of `spqrWindowOk` and `commit`. -/
theorem deliverStep_wrongSalt_wins (S : Spqr PQ PQC) (s : SpqrGameState PQ) (P : Party) (j : ℕ)
    (commit : Bool) (msg : List (BitVec 8)) (salt salt' : Salt) (st' : PQ)
    (hw : s.win = false) (hj : s.sent[j]? = some (P.other, msg, salt))
    (hrecv : S.recv (s.st P).1 msg = .ok (st', salt')) (hne : salt' ≠ salt) :
    (spqrDeliverStep S s P j commit).2.win = true := by
  have hlog := withLog_recv_eq_ok S (s.st P) msg st' salt' hrecv
  unfold spqrDeliverStep
  cases hp : S.withLog.recvPanics (s.st P) msg
  · simp only [hw, hj, hp, hlog, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    cases commit <;> simpa using hne
  · simp [hw, hj, hp]

theorem deliverStep_reject_outOfWindow (S : Spqr PQ PQC) (s : SpqrGameState PQ) (P : Party)
    (j : ℕ) (commit : Bool) (msg : List (BitVec 8)) (salt : Salt) (e : Bool)
    (hw : s.win = false) (hj : s.sent[j]? = some (P.other, msg, salt))
    (hnp : S.recvPanics (s.st P).1 msg = false)
    (hrecv : S.recv (s.st P).1 msg = .error e) (hout : spqrWindowOk (s.st P).2 msg = false) :
    (spqrDeliverStep S s P j commit).2.win = false := by
  have hlog := withLog_recv_eq_error S (s.st P) msg e hrecv
  have hnp' : S.withLog.recvPanics (s.st P) msg = false := hnp
  unfold spqrDeliverStep
  simp only [hw, hj, hnp', hlog, hout, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]

theorem deliverStep_rightSalt_noWin (S : Spqr PQ PQC) (s : SpqrGameState PQ) (P : Party) (j : ℕ)
    (commit : Bool) (msg : List (BitVec 8)) (salt : Salt) (st' : PQ)
    (hw : s.win = false) (hj : s.sent[j]? = some (P.other, msg, salt))
    (hnp : S.recvPanics (s.st P).1 msg = false)
    (hrecv : S.recv (s.st P).1 msg = .ok (st', salt)) :
    (spqrDeliverStep S s P j commit).2.win = false := by
  have hlog := withLog_recv_eq_ok S (s.st P) msg st' salt hrecv
  have hnp' : S.withLog.recvPanics (s.st P) msg = false := hnp
  unfold spqrDeliverStep
  simp only [hw, hj, hnp', hlog, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  cases commit <;> simp

theorem deliverStep_panic_wins (S : Spqr PQ PQC) (s : SpqrGameState PQ) (P : Party) (j : ℕ)
    (commit : Bool) (msg : List (BitVec 8)) (salt : Salt)
    (hw : s.win = false) (hj : s.sent[j]? = some (P.other, msg, salt))
    (hp : S.recvPanics (s.st P).1 msg = true) :
    (spqrDeliverStep S s P j commit).2.win = true := by
  have hp' : S.withLog.recvPanics (s.st P) msg = true := hp
  unfold spqrDeliverStep
  simp [hw, hj, hp']

end LibsignalSpqrCorrectFacts
end CryptoGames
