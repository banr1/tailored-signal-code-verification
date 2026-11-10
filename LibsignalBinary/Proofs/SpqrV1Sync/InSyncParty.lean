/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncEpoch
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncCalib
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16

/-!
# Two-Party Braid Synchronization and Honest Runs (`InSync`, `Run`)

Lifts the EK/CT-oriented `InSyncE` transitions of `InSyncEpoch` to fixed protocol parties `A` and `B`
via `ekSide e`:
* `inSync_sendA` / `inSync_sendB` and deterministic-coin variants `inSync_sendA_det` /
  `inSync_sendB_det` (computing updated ghost coins via `nextCoins`).
* `inSync_recvA` / `inSync_recvB`: receiving any `m` from the monotone in-flight history `toA` /
  `toB` succeeds, either staying at epoch `e` (emitting `RecvKey`) or advancing to `e + 1` on
  `noneMsg (e + 1)` when `e.toNat + 2 < 2 ^ 64`.
* `Run` and `run_inSync`: inductive honest braid executions maintain `InSync` and `inSync_codec`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Braid

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.Erasure
open CryptoVerification.SpqrV1Sync.InSync
open CryptoGames.LibsignalSession (ShaCompress)
theorem ekSide_succ_of_a (e : Epoch) (he : e.toNat + 1 < 2 ^ 64) (h : ekSide e = .a) :
    ekSide (e + 1#64) = .b := by
  have hne := ekSide_succ e he
  rw [h] at hne
  cases hs : ekSide (e + 1#64) with
  | a => exact absurd hs hne
  | b => rfl

theorem ekSide_succ_of_b (e : Epoch) (he : e.toNat + 1 < 2 ^ 64) (h : ekSide e = .b) :
    ekSide (e + 1#64) = .a := by
  have hne := ekSide_succ e he
  rw [h] at hne
  cases hs : ekSide (e + 1#64) with
  | a => rfl
  | b => exact absurd hs hne

theorem inSync_of_a {F : ShaCompress} {K : MlKem} {e : Epoch} {auth : Authenticator} {c : Coins}
    {stA stB : St F} {toA toB : List Msg} (hs : ekSide e = .a) :
    InSync F K e auth c stA stB toA toB ↔ InSyncE F K e auth c stA stB toB toA := by
  simp [InSync, hs]

theorem inSync_of_b {F : ShaCompress} {K : MlKem} {e : Epoch} {auth : Authenticator} {c : Coins}
    {stA stB : St F} {toA toB : List Msg} (hs : ekSide e = .b) :
    InSync F K e auth c stA stB toA toB ↔ InSyncE F K e auth c stB stA toA toB := by
  simp [InSync, hs]

theorem inSync_hepoch {F : ShaCompress} {K : MlKem} {e : Epoch} {auth : Authenticator}
    {c : Coins} {stA stB : St F} {toA toB : List Msg} (h : InSync F K e auth c stA stB toA toB) :
    e.toNat + 1 < 2 ^ 64 := by
  cases hs : ekSide e
  · exact ((inSync_of_a hs).mp h).hepoch
  · exact ((inSync_of_b hs).mp h).hepoch

/-- `noneMsg (e + 1)` never appears in `toX`, since messages toward `X_e` have epoch `≤ e`. -/
theorem noneNext_not_mem_toX {F : ShaCompress} {K : MlKem} {e : Epoch} {auth : Authenticator}
    {c : Coins} {x y : St F} {toY toX : List Msg} (h : InSyncE F K e auth c x y toY toX) :
    noneMsg (e + 1#64) ∉ toX := by
  intro hm
  have he_add : (e + 1#64).toNat = e.toNat + 1 := by
    have := h.hepoch
    simp [BitVec.toNat_add]
    omega
  have hne_ep : e + 1#64 ≠ e := by
    intro hEq
    have := congrArg BitVec.toNat hEq
    omega
  rcases h.htoX _ hm with hlt | hEq | ⟨_, _, _, hch⟩
  · simp only [noneMsg, BitVec.lt_def] at hlt
    omega
  · exact hne_ep (congrArg Message.epoch hEq)
  · rcases hch with ⟨_, hEq⟩ | ⟨_, hEq⟩
    · exact hne_ep (congrArg Message.epoch hEq)
    · exact hne_ep (congrArg Message.epoch hEq)

/-- Relational coin transition and optional `EpochSecret` output of a single braid send. -/
def CoinStep (F : ShaCompress) (K : MlKem) (e : Epoch) (tape : Bytes) (c c' : Coins)
    (key : Option EpochSecret) : Prop :=
  (c' = c ∧ key = none) ∨
  (c = .init ∧ key = none ∧ ∃ s : Seed, s.toList = tape.take 64 ∧ c' = .seed s) ∨
  (∃ s r, c = .seed s ∧ r.toList = tape.take 32 ∧ c' = .both s r ∧
    key = some { epoch := e, secret := secOf F K e s r })

/-- Possible key outputs of a braid receive at epoch `e`: `none` or `some (e, secOf F K e s r)`. -/
def RecvKey (F : ShaCompress) (K : MlKem) (e : Epoch) (c : Coins) (key : Option EpochSecret) :
    Prop :=
  key = none ∨ ∃ s r, c = .both s r ∧ key = some { epoch := e, secret := secOf F K e s r }

theorem coinStep_of_x {F : ShaCompress} {K : MlKem} {e : Epoch} {tape : Bytes} {c c' : Coins}
    (h : c' = c ∨ (c = .init ∧ ∃ s : Seed, s.toList = tape.take 64 ∧ c' = .seed s)) :
    CoinStep F K e tape c c' none := by
  rcases h with hEq | ⟨hc, hs⟩
  · exact Or.inl ⟨hEq, rfl⟩
  · exact Or.inr (Or.inl ⟨hc, rfl, hs⟩)

theorem coinStep_of_y {F : ShaCompress} {K : MlKem} {e : Epoch} {tape : Bytes} {c c' : Coins}
    {key : Option EpochSecret}
    (h : (c' = c ∧ key = none) ∨
      ∃ s r, c = .seed s ∧ r.toList = tape.take 32 ∧ c' = .both s r ∧
        key = some { epoch := e, secret := secOf F K e s r }) :
    CoinStep F K e tape c c' key := by
  rcases h with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inr h2)

/-- Party `A` send step preserving `InSync`. -/
theorem inSync_sendA (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (c : Coins)
    (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (tape : Bytes) (htape : 64 ≤ tape.length)
    (hkem : ekSide e = .b → ∀ (s : Seed) (r : EncRand), c = .seed s → r.toList = tape.take 32 →
      KemOk K s r) :
    ∃ (c' : Coins) (m : Msg) (key : Option EpochSecret) (stA' : St F) (tape' : Bytes),
      stA.send K tape = .ok ({ msg := m, key := key, state := stA' }, tape') ∧
      CoinStep F K e tape c c' key ∧
      InSync F K e auth c' stA' stB toA (toB ++ [m]) := by
  cases hs : ekSide e
  · have hE := (inSync_of_a hs).mp h
    rcases inSyncE_sendX F K e auth c stA stB toB toA hE tape htape with
      ⟨c', m, stA', tape', hsend, hcs, hE'⟩
    exact ⟨c', m, none, stA', tape', hsend, coinStep_of_x hcs, (inSync_of_a hs).mpr hE'⟩
  · have hE := (inSync_of_b hs).mp h
    rcases inSyncE_sendY F K e auth c stB stA toA toB hE tape (by omega) (hkem hs) with
      ⟨c', m, key, stA', tape', hsend, hcs, hE'⟩
    exact ⟨c', m, key, stA', tape', hsend, coinStep_of_y hcs, (inSync_of_b hs).mpr hE'⟩

/-- Party `B` send step preserving `InSync`. -/
theorem inSync_sendB (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (c : Coins)
    (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (tape : Bytes) (htape : 64 ≤ tape.length)
    (hkem : ekSide e = .a → ∀ (s : Seed) (r : EncRand), c = .seed s → r.toList = tape.take 32 →
      KemOk K s r) :
    ∃ (c' : Coins) (m : Msg) (key : Option EpochSecret) (stB' : St F) (tape' : Bytes),
      stB.send K tape = .ok ({ msg := m, key := key, state := stB' }, tape') ∧
      CoinStep F K e tape c c' key ∧
      InSync F K e auth c' stA stB' (toA ++ [m]) toB := by
  cases hs : ekSide e
  · have hE := (inSync_of_a hs).mp h
    rcases inSyncE_sendY F K e auth c stA stB toB toA hE tape (by omega) (hkem hs) with
      ⟨c', m, key, stB', tape', hsend, hcs, hE'⟩
    exact ⟨c', m, key, stB', tape', hsend, coinStep_of_y hcs, (inSync_of_a hs).mpr hE'⟩
  · have hE := (inSync_of_b hs).mp h
    rcases inSyncE_sendX F K e auth c stB stA toA toB hE tape htape with
      ⟨c', m, stB', tape', hsend, hcs, hE'⟩
    exact ⟨c', m, none, stB', tape', hsend, coinStep_of_x hcs, (inSync_of_b hs).mpr hE'⟩

/-- Party `A` receive of any `m ∈ toA` with `m ≠ noneMsg (e + 1)` preserves `InSync` at epoch `e`. -/
theorem inSync_recvA_stay (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (m : Msg) (hm : m ∈ toA) (hne : m ≠ noneMsg (e + 1#64)) :
    ∃ (key : Option EpochSecret) (stA' : St F), stA.recv K m = .ok { key := key, state := stA' } ∧
      RecvKey F K e c key ∧ InSync F K e auth c stA' stB toA toB := by
  cases hs : ekSide e
  · have hE := (inSync_of_a hs).mp h
    rcases inSyncE_recvX F K e auth c stA stB toB toA hE m hm with ⟨key, stA', hrecv, hkey, hE'⟩
    exact ⟨key, stA', hrecv, hkey, (inSync_of_a hs).mpr hE'⟩
  · have hE := (inSync_of_b hs).mp h
    rcases inSyncE_recvY F K e auth c stB stA toA toB hE m hm hne with ⟨stA', hrecv, hE'⟩
    exact ⟨none, stA', hrecv, Or.inl rfl, (inSync_of_b hs).mpr hE'⟩

/-- Party `B` receive of any `m ∈ toB` with `m ≠ noneMsg (e + 1)` preserves `InSync` at epoch `e`. -/
theorem inSync_recvB_stay (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (m : Msg) (hm : m ∈ toB) (hne : m ≠ noneMsg (e + 1#64)) :
    ∃ (key : Option EpochSecret) (stB' : St F), stB.recv K m = .ok { key := key, state := stB' } ∧
      RecvKey F K e c key ∧ InSync F K e auth c stA stB' toA toB := by
  cases hs : ekSide e
  · have hE := (inSync_of_a hs).mp h
    rcases inSyncE_recvY F K e auth c stA stB toB toA hE m hm hne with ⟨stB', hrecv, hE'⟩
    exact ⟨none, stB', hrecv, Or.inl rfl, (inSync_of_a hs).mpr hE'⟩
  · have hE := (inSync_of_b hs).mp h
    rcases inSyncE_recvX F K e auth c stB stA toA toB hE m hm with ⟨key, stB', hrecv, hkey, hE'⟩
    exact ⟨key, stB', hrecv, hkey, (inSync_of_b hs).mpr hE'⟩

/-- Party `A` receiving `noneMsg (e + 1)` advances `InSync` to epoch `e + 1` with `authNext`. -/
theorem inSync_advanceA (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (hm : noneMsg (e + 1#64) ∈ toA) (hnext : e.toNat + 2 < 2 ^ 64) :
    ∃ s r, c = .both s r ∧ ∃ stA' : St F,
      stA.recv K (noneMsg (e + 1#64)) = .ok { key := none, state := stA' } ∧
      InSync F K (e + 1#64) (authNext F K e auth s r) .init stA' stB toA toB := by
  cases hs : ekSide e
  · have hE := (inSync_of_a hs).mp h
    exact absurd hm (noneNext_not_mem_toX hE)
  · have hE := (inSync_of_b hs).mp h
    rcases inSyncE_next F K e auth c stB stA toA toB hE hm hnext with ⟨s, r, hc, stA', hrecv, hE'⟩
    have hs' := ekSide_succ_of_b e hE.hepoch hs
    exact ⟨s, r, hc, stA', hrecv, (inSync_of_a hs').mpr hE'⟩

/-- Party `B` receiving `noneMsg (e + 1)` advances `InSync` to epoch `e + 1` with `authNext`. -/
theorem inSync_advanceB (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (hm : noneMsg (e + 1#64) ∈ toB) (hnext : e.toNat + 2 < 2 ^ 64) :
    ∃ s r, c = .both s r ∧ ∃ stB' : St F,
      stB.recv K (noneMsg (e + 1#64)) = .ok { key := none, state := stB' } ∧
      InSync F K (e + 1#64) (authNext F K e auth s r) .init stA stB' toA toB := by
  cases hs : ekSide e
  · have hE := (inSync_of_a hs).mp h
    rcases inSyncE_next F K e auth c stA stB toB toA hE hm hnext with ⟨s, r, hc, stB', hrecv, hE'⟩
    have hs' := ekSide_succ_of_a e hE.hepoch hs
    exact ⟨s, r, hc, stB', hrecv, (inSync_of_b hs').mpr hE'⟩
  · have hE := (inSync_of_b hs).mp h
    exact absurd hm (noneNext_not_mem_toX hE)

/-- Party `A` receive of any `m ∈ toA`: either stays at `e` or advances to `e + 1`. -/
theorem inSync_recvA (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (m : Msg) (hm : m ∈ toA) (hnext : e.toNat + 2 < 2 ^ 64) :
    ∃ (key : Option EpochSecret) (stA' : St F), stA.recv K m = .ok { key := key, state := stA' } ∧
      ((RecvKey F K e c key ∧ InSync F K e auth c stA' stB toA toB) ∨
        (key = none ∧ ∃ s r, c = .both s r ∧
          InSync F K (e + 1#64) (authNext F K e auth s r) .init stA' stB toA toB)) := by
  by_cases hne : m = noneMsg (e + 1#64)
  · subst hne
    rcases inSync_advanceA F K e auth c stA stB toA toB h hm hnext with
      ⟨s, r, hc, stA', hrecv, hIn⟩
    exact ⟨none, stA', hrecv, Or.inr ⟨rfl, s, r, hc, hIn⟩⟩
  · rcases inSync_recvA_stay F K e auth c stA stB toA toB h m hm hne with
      ⟨key, stA', hrecv, hkey, hIn⟩
    exact ⟨key, stA', hrecv, Or.inl ⟨hkey, hIn⟩⟩

/-- Party `B` receive of any `m ∈ toB`: either stays at `e` or advances to `e + 1`. -/
theorem inSync_recvB (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (m : Msg) (hm : m ∈ toB) (hnext : e.toNat + 2 < 2 ^ 64) :
    ∃ (key : Option EpochSecret) (stB' : St F), stB.recv K m = .ok { key := key, state := stB' } ∧
      ((RecvKey F K e c key ∧ InSync F K e auth c stA stB' toA toB) ∨
        (key = none ∧ ∃ s r, c = .both s r ∧
          InSync F K (e + 1#64) (authNext F K e auth s r) .init stA stB' toA toB)) := by
  by_cases hne : m = noneMsg (e + 1#64)
  · subst hne
    rcases inSync_advanceB F K e auth c stA stB toA toB h hm hnext with
      ⟨s, r, hc, stB', hrecv, hIn⟩
    exact ⟨none, stB', hrecv, Or.inr ⟨rfl, s, r, hc, hIn⟩⟩
  · rcases inSync_recvB_stay F K e auth c stA stB toA toB h m hm hne with
      ⟨key, stB', hrecv, hkey, hIn⟩
    exact ⟨key, stB', hrecv, Or.inl ⟨hkey, hIn⟩⟩

/-- Both parties' states in `InSync` round-trip through `States.from_pb ∘ States.into_pb`. -/
theorem inSync_codec (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB) :
    States.from_pb spqrPolyApi (spqrAuthApi F) stA.into_pb = .ok stA ∧
      States.from_pb spqrPolyApi (spqrAuthApi F) stB.into_pb = .ok stB := by
  cases hs : ekSide e
  · exact inSyncE_codec F K e auth c stA stB toB toA ((inSync_of_a hs).mp h)
  · exact (inSyncE_codec F K e auth c stB stA toA toB ((inSync_of_b hs).mp h)).symm

/-- Deterministic ghost-coin transition of a braid send from state `st` on `tape`. -/
def nextCoins (F : ShaCompress) (c : Coins) (st : St F) (tape : Bytes) : Coins :=
  match c, st with
  | .init, .keysUnsampled _ =>
    if h : (tape.take 64).length = 64 then .seed ⟨tape.take 64, h⟩ else .init
  | .seed s, .headerReceived _ =>
    if h : (tape.take 32).length = 32 then .both s ⟨tape.take 32, h⟩ else .seed s
  | c, _ => c

/-- EK-side send updates the ghost coins deterministically to `nextCoins F c x tape`. -/
theorem inSyncE_sendX_det (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX)
    (tape : Bytes) (htape : 64 ≤ tape.length) :
    ∃ (m : Msg) (x' : St F) (tape' : Bytes),
      x.send K tape = .ok ({ msg := m, key := none, state := x' }, tape') ∧
      CoinStep F K e tape c (nextCoins F c x tape) none ∧
      InSyncE F K e auth (nextCoins F c x tape) x' y (toY ++ [m]) toX := by
  rcases inSyncE_sendX F K e auth c x y toY toX h tape htape with
    ⟨c', m, x', tape', hsend, hcs, hE'⟩
  have hc' : c' = nextCoins F c x tape := by
    cases c with
    | init =>
      have hx0 : x = .keysUnsampled { uc := { epoch := e, auth := auth } } := h.hx
      have h64 : (tape.take 64).length = 64 := by simp; omega
      have hnc : nextCoins F .init x tape = .seed ⟨tape.take 64, h64⟩ := by
        subst hx0; simp [nextCoins, h64]
      rw [hnc]
      rcases hcs with rfl | ⟨_, s, hs, rfl⟩
      · rcases InSync.xSend_unsampled F K e auth h.hauth x h.hx tape htape with
          ⟨_, _, x0, hsend0, hx0'⟩
        rw [hsend] at hsend0
        injection hsend0 with hp
        injection hp with ho _
        have hxEq : x' = x0 := congrArg (fun o => o.state) ho
        rcases hx0' with ⟨_, _, hx0Eq⟩
        have hx'Eq : x' = .keysUnsampled { uc := { epoch := e, auth := auth } } := hE'.hx
        rw [hxEq, hx0Eq] at hx'Eq
        nomatch hx'Eq
      · exact congrArg Coins.seed (Subtype.ext hs)
    | seed s =>
      rcases h.hx with ⟨_, _, hxEq⟩
      have hnc : nextCoins F (.seed s) x tape = .seed s := by subst hxEq; rfl
      rw [hnc]
      rcases hcs with hEq | ⟨hbad, _⟩
      · exact hEq
      · nomatch hbad
    | both s r =>
      have hnc : nextCoins F (.both s r) x tape = .both s r := by cases x <;> rfl
      rw [hnc]
      rcases hcs with hEq | ⟨hbad, _⟩
      · exact hEq
      · nomatch hbad
  subst hc'
  exact ⟨m, x', tape', hsend, coinStep_of_x hcs, hE'⟩

/-- CT-side send updates the ghost coins deterministically to `nextCoins F c y tape`. -/
theorem inSyncE_sendY_det (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX)
    (tape : Bytes) (htape : 32 ≤ tape.length)
    (hkem : ∀ (s : Seed) (r : EncRand), c = .seed s → r.toList = tape.take 32 → KemOk K s r) :
    ∃ (m : Msg) (key : Option EpochSecret) (y' : St F) (tape' : Bytes),
      y.send K tape = .ok ({ msg := m, key := key, state := y' }, tape') ∧
      CoinStep F K e tape c (nextCoins F c y tape) key ∧
      InSyncE F K e auth (nextCoins F c y tape) x y' toY (toX ++ [m]) := by
  rcases inSyncE_sendY F K e auth c x y toY toX h tape htape hkem with
    ⟨c', m, key, y', tape', hsend, hcs, hE'⟩
  have hc' : c' = nextCoins F c y tape := by
    cases c with
    | init =>
      have hy0 : y = .noHeaderReceived { uc := { epoch := e, auth := auth }, receiving_hdr := freshDec 96 } := h.hy
      have hnc : nextCoins F .init y tape = .init := by subst hy0; rfl
      rw [hnc]
      rcases hcs with ⟨hEq, _⟩ | ⟨_, _, hbad, _⟩
      · exact hEq
      · nomatch hbad
    | seed s =>
      rcases h.hy with ⟨_, _, _, _, hyEq⟩ | hyEq
      · have hnc : nextCoins F (.seed s) y tape = .seed s := by subst hyEq; rfl
        rw [hnc]
        have hnhr : ∀ hr, y ≠ .headerReceived hr := by
          subst hyEq; intro _ hbad; nomatch hbad
        have hsend0 := InSync.ySend_noHeader F K e auth (some s) y h.hy hnhr tape
        rw [hsend] at hsend0
        injection hsend0 with hp
        injection hp with ho _
        have hkey0 : key = none := congrArg (fun o => o.key) ho
        rcases hcs with ⟨hEq, _⟩ | ⟨_, _, _, _, _, hkSome⟩
        · exact hEq
        · rw [hkey0] at hkSome
          nomatch hkSome
      · have h32 : (tape.take 32).length = 32 := by simp; omega
        let r0 : EncRand := ⟨tape.take 32, h32⟩
        have hnc : nextCoins F (.seed s) y tape = .both s r0 := by
          subst hyEq; simp [nextCoins, h32, r0]
        rw [hnc]
        have hk0 : KemOk K s r0 := hkem s r0 rfl rfl
        rcases ySend_hr F K e auth s r0 hk0 tape rfl with ⟨y0, hsend0, _⟩
        rw [← hyEq, hsend] at hsend0
        injection hsend0 with hp
        injection hp with ho _
        have hkeySome : key = some { epoch := e, secret := secOf F K e s r0 } :=
          congrArg (fun o => o.key) ho
        rcases hcs with ⟨_, hkNone⟩ | ⟨s', r', hsEq, hrList, rfl, _⟩
        · rw [hkeySome] at hkNone
          nomatch hkNone
        · injection hsEq with hs'
          subst hs'
          exact congrArg (Coins.both s) (Subtype.ext hrList)
    | both s r =>
      have hnc : nextCoins F (.both s r) y tape = .both s r := by cases y <;> rfl
      rw [hnc]
      rcases hcs with ⟨hEq, _⟩ | ⟨_, _, hbad, _⟩
      · exact hEq
      · nomatch hbad
  subst hc'
  exact ⟨m, key, y', tape', hsend, coinStep_of_y hcs, hE'⟩

/-- Party `A` send with deterministic updated coins `nextCoins F c stA tape`. -/
theorem inSync_sendA_det (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (tape : Bytes) (htape : 64 ≤ tape.length)
    (hkem : ekSide e = .b → ∀ (s : Seed) (r : EncRand), c = .seed s → r.toList = tape.take 32 →
      KemOk K s r) :
    ∃ (m : Msg) (key : Option EpochSecret) (stA' : St F) (tape' : Bytes),
      stA.send K tape = .ok ({ msg := m, key := key, state := stA' }, tape') ∧
      CoinStep F K e tape c (nextCoins F c stA tape) key ∧
      InSync F K e auth (nextCoins F c stA tape) stA' stB toA (toB ++ [m]) := by
  cases hs : ekSide e
  · have hE := (inSync_of_a hs).mp h
    rcases inSyncE_sendX_det F K e auth c stA stB toB toA hE tape htape with
      ⟨m, stA', tape', hsend, hcs, hE'⟩
    exact ⟨m, none, stA', tape', hsend, hcs, (inSync_of_a hs).mpr hE'⟩
  · have hE := (inSync_of_b hs).mp h
    rcases inSyncE_sendY_det F K e auth c stB stA toA toB hE tape (by omega) (hkem hs) with
      ⟨m, key, stA', tape', hsend, hcs, hE'⟩
    exact ⟨m, key, stA', tape', hsend, hcs, (inSync_of_b hs).mpr hE'⟩

/-- Party `B` send with deterministic updated coins `nextCoins F c stB tape`. -/
theorem inSync_sendB_det (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (tape : Bytes) (htape : 64 ≤ tape.length)
    (hkem : ekSide e = .a → ∀ (s : Seed) (r : EncRand), c = .seed s → r.toList = tape.take 32 →
      KemOk K s r) :
    ∃ (m : Msg) (key : Option EpochSecret) (stB' : St F) (tape' : Bytes),
      stB.send K tape = .ok ({ msg := m, key := key, state := stB' }, tape') ∧
      CoinStep F K e tape c (nextCoins F c stB tape) key ∧
      InSync F K e auth (nextCoins F c stB tape) stA stB' (toA ++ [m]) toB := by
  cases hs : ekSide e
  · have hE := (inSync_of_a hs).mp h
    rcases inSyncE_sendY_det F K e auth c stA stB toB toA hE tape (by omega) (hkem hs) with
      ⟨m, key, stB', tape', hsend, hcs, hE'⟩
    exact ⟨m, key, stB', tape', hsend, hcs, (inSync_of_a hs).mpr hE'⟩
  · have hE := (inSync_of_b hs).mp h
    rcases inSyncE_sendX_det F K e auth c stB stA toA toB hE tape htape with
      ⟨m, stB', tape', hsend, hcs, hE'⟩
    exact ⟨m, none, stB', tape', hsend, hcs, (inSync_of_b hs).mpr hE'⟩

/-- Inductive trace of honest two-party braid executions from `init_a` and `init_b`. -/
inductive Run (F : ShaCompress) (K : MlKem) (authKey : Bytes) :
    Epoch → Authenticator → Coins → St F → St F → List Msg → List Msg → Prop
  | init (stA stB : St F)
      (hA : States.init_a spqrPolyApi (spqrAuthApi F) authKey = .ok stA)
      (hB : States.init_b spqrPolyApi (spqrAuthApi F) authKey = .ok stB) :
      Run F K authKey 1#64 (Authenticator.new F authKey 1#64) .init stA stB [] []
  | sendA {e : Epoch} {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
      (hr : Run F K authKey e auth c stA stB toA toB) (tape : Bytes) (htape : 64 ≤ tape.length)
      (hkem : ekSide e = .b → ∀ (s : Seed) (r : EncRand), c = .seed s →
        r.toList = tape.take 32 → KemOk K s r)
      (m : Msg) (key : Option EpochSecret) (stA' : St F) (tape' : Bytes)
      (hsend : stA.send K tape = .ok ({ msg := m, key := key, state := stA' }, tape')) :
      Run F K authKey e auth (nextCoins F c stA tape) stA' stB toA (toB ++ [m])
  | sendB {e : Epoch} {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
      (hr : Run F K authKey e auth c stA stB toA toB) (tape : Bytes) (htape : 64 ≤ tape.length)
      (hkem : ekSide e = .a → ∀ (s : Seed) (r : EncRand), c = .seed s →
        r.toList = tape.take 32 → KemOk K s r)
      (m : Msg) (key : Option EpochSecret) (stB' : St F) (tape' : Bytes)
      (hsend : stB.send K tape = .ok ({ msg := m, key := key, state := stB' }, tape')) :
      Run F K authKey e auth (nextCoins F c stB tape) stA stB' (toA ++ [m]) toB
  | recvA {e : Epoch} {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
      (hr : Run F K authKey e auth c stA stB toA toB) (m : Msg) (hm : m ∈ toA)
      (hne : m ≠ noneMsg (e + 1#64)) (key : Option EpochSecret) (stA' : St F)
      (hrecv : stA.recv K m = .ok { key := key, state := stA' }) :
      Run F K authKey e auth c stA' stB toA toB
  | recvB {e : Epoch} {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
      (hr : Run F K authKey e auth c stA stB toA toB) (m : Msg) (hm : m ∈ toB)
      (hne : m ≠ noneMsg (e + 1#64)) (key : Option EpochSecret) (stB' : St F)
      (hrecv : stB.recv K m = .ok { key := key, state := stB' }) :
      Run F K authKey e auth c stA stB' toA toB
  | advanceA {e : Epoch} {auth : Authenticator} {s : Seed} {r : EncRand} {stA stB : St F}
      {toA toB : List Msg} (hr : Run F K authKey e auth (.both s r) stA stB toA toB)
      (hm : noneMsg (e + 1#64) ∈ toA) (hnext : e.toNat + 2 < 2 ^ 64) (stA' : St F)
      (hrecv : stA.recv K (noneMsg (e + 1#64)) = .ok { key := none, state := stA' }) :
      Run F K authKey (e + 1#64) (authNext F K e auth s r) .init stA' stB toA toB
  | advanceB {e : Epoch} {auth : Authenticator} {s : Seed} {r : EncRand} {stA stB : St F}
      {toA toB : List Msg} (hr : Run F K authKey e auth (.both s r) stA stB toA toB)
      (hm : noneMsg (e + 1#64) ∈ toB) (hnext : e.toNat + 2 < 2 ^ 64) (stB' : St F)
      (hrecv : stB.recv K (noneMsg (e + 1#64)) = .ok { key := none, state := stB' }) :
      Run F K authKey (e + 1#64) (authNext F K e auth s r) .init stA stB' toA toB

private theorem ok_eq_imp {ε α : Type} {a b : α} (h : (Except.ok a : Except ε α) = Except.ok b) :
    a = b := by
  cases h; rfl

private theorem coins_both_inj {s s0 : Seed} {r r0 : EncRand}
    (h : Coins.both s r = Coins.both s0 r0) : s = s0 ∧ r = r0 := by
  cases h; exact ⟨rfl, rfl⟩

/-- Every reachable `Run` trace satisfies `InSync`. -/
theorem run_inSync (F : ShaCompress) (K : MlKem) (authKey : Bytes) {e : Epoch}
    {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
    (hr : Run F K authKey e auth c stA stB toA toB) : InSync F K e auth c stA stB toA toB := by
  induction hr with
  | init stA stB hA hB =>
    rcases inSync_init F K authKey with ⟨stA0, stB0, hA0, hB0, hIn⟩
    have hEqA : stA = stA0 := ok_eq_imp (hA.symm.trans hA0)
    have hEqB : stB = stB0 := ok_eq_imp (hB.symm.trans hB0)
    rw [← hEqA, ← hEqB] at hIn
    exact hIn
  | sendA _ tape htape hkem m key stA' tape' hsend ih =>
    rcases inSync_sendA_det F K _ _ _ _ _ _ _ ih tape htape hkem with
      ⟨m0, key0, stA0, tape0, hsend0, _, hIn⟩
    have ho := congrArg Prod.fst (ok_eq_imp (hsend.symm.trans hsend0))
    have hmEq : m = m0 := congrArg (fun o => o.msg) ho
    have hstEq : stA' = stA0 := congrArg (fun o => o.state) ho
    rw [← hmEq, ← hstEq] at hIn
    exact hIn
  | sendB _ tape htape hkem m key stB' tape' hsend ih =>
    rcases inSync_sendB_det F K _ _ _ _ _ _ _ ih tape htape hkem with
      ⟨m0, key0, stB0, tape0, hsend0, _, hIn⟩
    have ho := congrArg Prod.fst (ok_eq_imp (hsend.symm.trans hsend0))
    have hmEq : m = m0 := congrArg (fun o => o.msg) ho
    have hstEq : stB' = stB0 := congrArg (fun o => o.state) ho
    rw [← hmEq, ← hstEq] at hIn
    exact hIn
  | recvA _ m hm hne key stA' hrecv ih =>
    rcases inSync_recvA_stay F K _ _ _ _ _ _ _ ih m hm hne with ⟨key0, stA0, hrecv0, _, hIn⟩
    have ho := ok_eq_imp (hrecv.symm.trans hrecv0)
    have hstEq : stA' = stA0 := congrArg (fun o => o.state) ho
    rw [← hstEq] at hIn
    exact hIn
  | recvB _ m hm hne key stB' hrecv ih =>
    rcases inSync_recvB_stay F K _ _ _ _ _ _ _ ih m hm hne with ⟨key0, stB0, hrecv0, _, hIn⟩
    have ho := ok_eq_imp (hrecv.symm.trans hrecv0)
    have hstEq : stB' = stB0 := congrArg (fun o => o.state) ho
    rw [← hstEq] at hIn
    exact hIn
  | advanceA _ hm hnext stA' hrecv ih =>
    rcases inSync_advanceA F K _ _ _ _ _ _ _ ih hm hnext with ⟨s0, r0, hc, stA0, hrecv0, hIn⟩
    rcases coins_both_inj hc with ⟨hsEq, hrEq⟩
    have ho := ok_eq_imp (hrecv.symm.trans hrecv0)
    have hstEq : stA' = stA0 := congrArg (fun o => o.state) ho
    rw [← hsEq, ← hrEq, ← hstEq] at hIn
    exact hIn
  | advanceB _ hm hnext stB' hrecv ih =>
    rcases inSync_advanceB F K _ _ _ _ _ _ _ ih hm hnext with ⟨s0, r0, hc, stB0, hrecv0, hIn⟩
    rcases coins_both_inj hc with ⟨hsEq, hrEq⟩
    have ho := ok_eq_imp (hrecv.symm.trans hrecv0)
    have hstEq : stB' = stB0 := congrArg (fun o => o.state) ho
    rw [← hsEq, ← hrEq, ← hstEq] at hIn
    exact hIn

end CryptoVerification.SpqrV1Sync.Braid
