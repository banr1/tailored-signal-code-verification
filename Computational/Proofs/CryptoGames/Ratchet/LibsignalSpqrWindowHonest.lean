/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrCorrect

/-!
# Honest FIFO schedules stay in SPQR's window

Proves that every two-party FIFO schedule without drops whose header epochs respect SPQR braid
causality and `< 2^32` total sends delivers only messages inside `spqrWindowOk`
(`honest_fifo_in_window`).
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSpqrWindowHonest

open LibsignalSession

/-- Bounded LEB128 varint encoding of `n`. -/
def varint : ℕ → ℕ → List (BitVec 8)
  | 0, _ => []
  | fuel + 1, n => if n < 128 then [BitVec.ofNat 8 n]
      else BitVec.ofNat 8 (n % 128 + 128) :: varint fuel (n / 128)

/-- Synthetic SPQR V1 message with header `(E, i)`. -/
def honestMsg (E i : ℕ) : List (BitVec 8) := 1#8 :: (varint 10 E ++ varint 10 i ++ [0#8])

private theorem wv_byte_lt_mask80 (r : Fin 128) :
    BitVec.ofNat 8 r.val &&& 0x80#8 = 0#8 := by
  revert r; decide +kernel

private theorem wv_byte_lt_mask7f (r : Fin 128) :
    (BitVec.ofNat 8 r.val &&& 0x7F#8).zeroExtend 64 = BitVec.ofNat 64 r.val := by
  revert r; decide +kernel

private theorem wv_byte_ge_mask80 (r : Fin 128) :
    BitVec.ofNat 8 (r.val + 128) &&& 0x80#8 = 0x80#8 := by
  revert r; decide +kernel

private theorem wv_byte_ge_mask7f (r : Fin 128) :
    (BitVec.ofNat 8 (r.val + 128) &&& 0x7F#8).zeroExtend 64 = BitVec.ofNat 64 r.val := by
  revert r; decide +kernel

private theorem wv_or_div_mod (n i : ℕ) :
    (BitVec.ofNat 64 (n % 128) <<< (7 * i)) ||| (BitVec.ofNat 64 (n / 128) <<< (7 * (i + 1))) =
      BitVec.ofNat 64 n <<< (7 * i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hj, decide_true,
    Bool.true_and]
  have h128 : 128 = 2 ^ 7 := by decide
  rw [h128, Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
  by_cases h1 : j < 7 * i
  · have h2 : j < 7 * (i + 1) := by omega
    simp [h1, h2]
  · by_cases h2 : j < 7 * (i + 1)
    · have h3 : j - 7 * i < 7 := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ (j - 7 * i < 7) := by omega
      have h4 : 7 + (j - 7 * (i + 1)) = j - 7 * i := by omega
      have h5 : j - 7 * (i + 1) < 64 := by omega
      have h6 : j - 7 * i < 64 := by omega
      simp [h1, h2, h3, h4, h5, h6]

private theorem wv_spqrVarintAux_varint (k : ℕ) :
    ∀ (i n : ℕ) (out : BitVec 64) (rest : List (BitVec 8)),
      1 ≤ k → i + k ≤ 10 → n < 2 ^ (7 * k) →
      CryptoVerification.LibsignalSpqr.spqrVarintAux i out (varint k n ++ rest) =
        some (out ||| (BitVec.ofNat 64 n <<< (7 * i)), rest) := by
  induction k with
  | zero => intro i n out rest hk; omega
  | succ fuel ih =>
    intro i n out rest _ hik hn
    unfold varint
    split_ifs with hlt
    · simp only [List.singleton_append, CryptoVerification.LibsignalSpqr.spqrVarintAux]
      have h80 : BitVec.ofNat 8 n &&& 0x80#8 = 0#8 := wv_byte_lt_mask80 ⟨n, hlt⟩
      have h7f : (BitVec.ofNat 8 n &&& 0x7F#8).zeroExtend 64 = BitVec.ofNat 64 n :=
        wv_byte_lt_mask7f ⟨n, hlt⟩
      simp only [h80, h7f, ↓reduceIte]
    · simp only [List.cons_append, CryptoVerification.LibsignalSpqr.spqrVarintAux]
      have hmod : n % 128 < 128 := Nat.mod_lt n (by decide)
      have h80 : BitVec.ofNat 8 (n % 128 + 128) &&& 0x80#8 = 0x80#8 :=
        wv_byte_ge_mask80 ⟨n % 128, hmod⟩
      have h7f : (BitVec.ofNat 8 (n % 128 + 128) &&& 0x7F#8).zeroExtend 64 =
          BitVec.ofNat 64 (n % 128) := wv_byte_ge_mask7f ⟨n % 128, hmod⟩
      have hne0 : (0x80#8 : BitVec 8) ≠ 0#8 := by decide
      have hfuel : 1 ≤ fuel := by
        by_contra h0
        have hf0 : fuel = 0 := by omega
        subst hf0
        omega
      have hi10 : i + 1 ≠ CryptoVerification.LibsignalSpqr.maxVarintBytes := by
        unfold CryptoVerification.LibsignalSpqr.maxVarintBytes
        omega
      have hdiv : n / 128 < 2 ^ (7 * fuel) := by
        have hpow : 2 ^ (7 * (fuel + 1)) = 2 ^ (7 * fuel) * 128 := by
          rw [Nat.mul_add, Nat.pow_add]
        omega
      simp only [h80, h7f, hne0, ↓reduceIte, hi10]
      rw [ih (i + 1) (n / 128) _ rest hfuel (by omega) hdiv]
      rw [BitVec.or_assoc, wv_or_div_mod]

private theorem wv_spqrDecodeVarint_varint {n : ℕ} (hn : n < 2 ^ 64) (rest : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqr.spqrDecodeVarint (varint 10 n ++ rest) =
      some (BitVec.ofNat 64 n, rest) := by
  unfold CryptoVerification.LibsignalSpqr.spqrDecodeVarint
  rw [wv_spqrVarintAux_varint 10 0 n 0#64 rest (by decide) (by decide) (by omega)]
  simp

/-- The preamble of an honest message reads back `(E, i)`. -/
theorem spqrPos_honestMsg {E i : ℕ} (hE1 : 1 ≤ E) (hE : E < 2 ^ 64) (hi : i < 2 ^ 32) :
    spqrPos (honestMsg E i) = some (E, i) := by
  have hE0 : BitVec.ofNat 64 E ≠ 0#64 := by
    intro h0
    have hto := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hE] at hto
    omega
  simp only [spqrPos, honestMsg, CryptoVerification.LibsignalSpqr.msgPreamble?, List.append_assoc,
    wv_spqrDecodeVarint_varint hE, wv_spqrDecodeVarint_varint (by omega : i < 2 ^ 64),
    hE0, ↓reduceIte, hi, Option.map_some, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hE, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt hi]

/-- Schedule event: `send P E` at header epoch `E`, or FIFO `deliver P`. -/
inductive Ev
  | send (P : Party) (E : ℕ)
  | deliver (P : Party)

def Ev.isSend : Ev → Bool
  | .send _ _ => true
  | .deliver _ => false

/-- Simulator state tracking per-party SPQR logs, FIFO queues, and honesty/window flags. -/
structure SimState where
  log : Party → SpqrLog
  inFlight : Party → List (ℕ × ℕ)
  last : Party → ℕ × ℕ
  maxRecv : Party → ℕ
  honest : Bool
  inWindow : Bool

def SimState.init : SimState :=
  ⟨fun _ => default, fun _ => [], fun _ => (0, 0), fun _ => 0, true, true⟩

def SimState.step (s : SimState) : Ev → SimState
  | .send P E =>
    let i := if (s.last P).1 = E then (s.last P).2 + 1 else 1
    { s with
      log := Function.update s.log P { s.log P with sent := honestMsg E i :: (s.log P).sent }
      inFlight := Function.update s.inFlight P (s.inFlight P ++ [(E, i)])
      last := Function.update s.last P (E, i)
      honest := s.honest && decide (1 ≤ E) && decide ((s.last P).1 ≤ E)
        && decide (E ≤ s.maxRecv P + 1) }
  | .deliver P =>
    match s.inFlight P.other with
    | [] => s
    | (E, i) :: rest =>
      let m := honestMsg E i
      { s with
        inWindow := s.inWindow && spqrWindowOk (s.log P) m
        log := Function.update s.log P { s.log P with recvd := m :: (s.log P).recvd }
        inFlight := Function.update s.inFlight P.other rest
        maxRecv := Function.update s.maxRecv P (max (s.maxRecv P) E) }

def run (evs : List Ev) : SimState := evs.foldl SimState.step SimState.init

example :
    let s := run [.send .A 1, .send .A 1, .send .B 1, .send .A 1, .send .B 1,
      .deliver .B, .deliver .A, .send .A 2, .deliver .B, .deliver .A, .deliver .B, .deliver .B,
      .send .B 3, .deliver .A, .send .A 2, .send .A 3, .deliver .B, .deliver .B]
    s.honest = true ∧ s.inWindow = true := by
  decide +kernel

example : (run [.send .A 2]).honest = false ∧
    (run [.send .A 1, .send .B 1, .deliver .A, .send .A 2, .send .A 1]).honest = false := by
  decide +kernel

example :
    let s := run [.send .B 1, .deliver .A, .send .A 2, .send .A 3, .send .B 1, .deliver .A]
    s.honest = false ∧ s.inWindow = false := by
  decide +kernel

private theorem wf_other_inj {P Q : Party} : P.other = Q.other ↔ P = Q := by
  cases P <;> cases Q <;> decide

private theorem wf_foldl_max_init {α : Type} (f : α → ℕ) (xs : List α) (a : ℕ) :
    xs.foldl (fun m p => max m (f p)) a = max a (xs.foldl (fun m p => max m (f p)) 0) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_max]
    rw [ih (max a (f x)), ih (f x), Nat.max_assoc]

private theorem wf_foldl_max_cons {α : Type} (f : α → ℕ) (x : α) (xs : List α) :
    (x :: xs).foldl (fun m p => max m (f p)) 0 =
      max (f x) (xs.foldl (fun m p => max m (f p)) 0) := by
  simp only [List.foldl_cons, Nat.zero_max, wf_foldl_max_init f xs (f x)]

private theorem wf_le_foldl_max {α : Type} (f : α → ℕ) {x : α} {xs : List α} (hx : x ∈ xs) :
    f x ≤ xs.foldl (fun m p => max m (f p)) 0 := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [wf_foldl_max_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · omega
    · have := ih hmem; omega

private theorem wf_maxSendEpoch_cons (log : SpqrLog) (m : List (BitVec 8)) (E i : ℕ)
    (hpos : spqrPos m = some (E, i)) :
    ({ log with sent := m :: log.sent } : SpqrLog).maxSendEpoch = max E log.maxSendEpoch := by
  simp [SpqrLog.maxSendEpoch, hpos, wf_foldl_max_cons (fun p : ℕ × ℕ => p.1)]

private theorem wf_recvCtr_cons (log : SpqrLog) (m : List (BitVec 8)) (E i : ℕ)
    (hpos : spqrPos m = some (E, i)) (hi : i = log.recvCtr E + 1) :
    ({ log with recvd := m :: log.recvd } : SpqrLog).recvCtr =
      Function.update log.recvCtr E i := by
  funext e
  by_cases he : e = E
  · subst he
    simp [Function.update_self, SpqrLog.recvCtr, hpos, wf_foldl_max_cons (fun p : ℕ × ℕ => p.2)] at hi ⊢
    omega
  · simp [Function.update_of_ne he, SpqrLog.recvCtr, hpos, Ne.symm he]

private theorem wf_not_mem_recvd_of_gt (log : SpqrLog) (E i : ℕ) (hi : log.recvCtr E < i) :
    (E, i) ∉ log.recvd.filterMap spqrPos := by
  intro hmem
  have hfilt : (E, i) ∈ (log.recvd.filterMap spqrPos).filter (·.1 = E) :=
    List.mem_filter.mpr ⟨hmem, by simp⟩
  have hle : i ≤ log.recvCtr E := wf_le_foldl_max (fun p : ℕ × ℕ => p.2) hfilt
  omega

private theorem wf_windowOk_of_recvCtr (log : SpqrLog) (m : List (BitVec 8)) (E i : ℕ)
    (hpos : spqrPos m = some (E, i)) (hE1 : 1 ≤ E) (hmax : log.maxSendEpoch ≤ E + 1)
    (hi : i = log.recvCtr E + 1) : spqrWindowOk log m = true := by
  have hnot := wf_not_mem_recvd_of_gt log E i (by omega)
  have hE0 : E ≠ 0 := by omega
  simp only [spqrWindowOk, hpos, hE0, ↓reduceIte, List.contains_eq_mem, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hmax, by omega⟩, by omega⟩, by omega⟩, by omega⟩, hnot⟩

private def wf_queueOk (m : ℕ) (c : ℕ → ℕ) : List (ℕ × ℕ) → ℕ × ℕ → Prop
  | [], L => L.1 = m ∧ L.2 = c m
  | (E, i) :: rest, L => 1 ≤ E ∧ m ≤ E ∧ i = c E + 1 ∧
      wf_queueOk E (Function.update c E i) rest L

private theorem wf_queueOk_snoc {m : ℕ} {c : ℕ → ℕ} {F : List (ℕ × ℕ)} {L : ℕ × ℕ}
    (hq : wf_queueOk m c F L) (hc : ∀ e, m < e → c e = 0) {E : ℕ} (hE1 : 1 ≤ E) (hLE : L.1 ≤ E) :
    let i := if L.1 = E then L.2 + 1 else 1
    wf_queueOk m c (F ++ [(E, i)]) (E, i) := by
  intro i
  induction F generalizing m c with
  | nil =>
    obtain ⟨h1, h2⟩ := hq
    refine ⟨hE1, by omega, ?_, rfl, (Function.update_self E i c).symm⟩
    by_cases h : L.1 = E
    · subst h; subst h1; simp [i, h2]
    · have hmE : m < E := by omega
      simp [i, h, hc E hmE]
  | cons hd rest ih =>
    obtain ⟨E0, i0⟩ := hd
    obtain ⟨hE0, hm0, hi0, hrest⟩ := hq
    refine ⟨hE0, hm0, hi0, ih hrest fun e he => ?_⟩
    rw [Function.update_of_ne (by omega)]
    exact hc e (by omega)

private structure Inv (k : ℕ) (s : SimState) : Prop where
  inWindow : s.inWindow = true
  maxSend : ∀ P, (s.log P).maxSendEpoch ≤ s.maxRecv P + 1
  queue : ∀ P, wf_queueOk (s.maxRecv P) (s.log P).recvCtr (s.inFlight P.other) (s.last P.other)
  ctrZero : ∀ P e, s.maxRecv P < e → (s.log P).recvCtr e = 0
  maxRecvLe : ∀ P, s.maxRecv P ≤ k + 1
  lastLe : ∀ P, (s.last P).1 ≤ k + 1 ∧ (s.last P).2 ≤ k
  inFlightLe : ∀ P p, p ∈ s.inFlight P → p.1 ≤ k + 1 ∧ p.2 ≤ k

private theorem wf_init_inv : Inv 0 SimState.init := by
  refine ⟨rfl, fun _ => Nat.zero_le _, fun _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl,
    fun _ => Nat.zero_le _, fun _ => ⟨Nat.zero_le _, Nat.le_refl 0⟩, fun _ _ h => by cases h⟩

private theorem wf_step_send {k : ℕ} {s : SimState} (hs : Inv k s) (hk : k + 1 < 2 ^ 32)
    (Q : Party) (E : ℕ) (hh : (s.step (.send Q E)).honest = true) :
    Inv (k + 1) (s.step (.send Q E)) := by
  simp only [SimState.step, Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨⟨⟨-, hE1⟩, hLE⟩, hEm⟩ := hh
  let i := if (s.last Q).1 = E then (s.last Q).2 + 1 else 1
  have hQm := hs.maxRecvLe Q
  have hQl := hs.lastLe Q
  have hEk : E ≤ k + 2 := by omega
  have hik : i ≤ k + 1 := by dsimp [i]; split_ifs <;> omega
  have hpos : spqrPos (honestMsg E i) = some (E, i) :=
    spqrPos_honestMsg hE1 (by omega) (by omega)
  refine ⟨hs.inWindow, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    simp only [SimState.step]
    by_cases hPQ : P = Q
    · subst hPQ
      rw [Function.update_self, wf_maxSendEpoch_cons _ _ E i hpos]
      have := hs.maxSend P
      omega
    · rw [Function.update_of_ne hPQ]
      exact hs.maxSend P
  · intro P
    simp only [SimState.step]
    have hctr : ((Function.update s.log Q { s.log Q with sent := honestMsg E i :: (s.log Q).sent })
        P).recvCtr = (s.log P).recvCtr := by
      by_cases hPQ : P = Q
      · subst hPQ; rw [Function.update_self]; rfl
      · rw [Function.update_of_ne hPQ]
    rw [hctr]
    by_cases hPO : P.other = Q
    · rw [hPO, Function.update_self, Function.update_self]
      have hqP := hs.queue P
      rw [hPO] at hqP
      exact wf_queueOk_snoc hqP (hs.ctrZero P) hE1 hLE
    · rw [Function.update_of_ne hPO, Function.update_of_ne hPO]
      exact hs.queue P
  · intro P e he
    simp only [SimState.step]
    by_cases hPQ : P = Q
    · subst hPQ; rw [Function.update_self]; exact hs.ctrZero P e he
    · rw [Function.update_of_ne hPQ]; exact hs.ctrZero P e he
  · intro P
    have := hs.maxRecvLe P; simp only [SimState.step]; omega
  · intro P
    simp only [SimState.step]
    by_cases hPQ : P = Q
    · subst hPQ; rw [Function.update_self]; exact ⟨hEk, hik⟩
    · rw [Function.update_of_ne hPQ]
      have := hs.lastLe P; omega
  · intro P p hp
    simp only [SimState.step] at hp
    by_cases hPQ : P = Q
    · subst hPQ
      rw [Function.update_self, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · have := hs.inFlightLe P p hp; omega
      · exact ⟨hEk, hik⟩
    · rw [Function.update_of_ne hPQ] at hp
      have := hs.inFlightLe P p hp; omega

private theorem wf_step_deliver {k : ℕ} {s : SimState} (hs : Inv k s) (hk : k < 2 ^ 32)
    (Q : Party) : Inv k (s.step (.deliver Q)) := by
  simp only [SimState.step]
  cases hF : s.inFlight Q.other with
  | nil => exact hs
  | cons hd rest =>
    obtain ⟨E, i⟩ := hd
    dsimp only
    have hqQ := hs.queue Q
    rw [hF] at hqQ
    obtain ⟨hE1, hmE, hi, hrest⟩ := hqQ
    have hmem : (E, i) ∈ s.inFlight Q.other := by rw [hF]; exact List.Mem.head _
    have hEk := hs.inFlightLe Q.other (E, i) hmem
    have hpos : spqrPos (honestMsg E i) = some (E, i) :=
      spqrPos_honestMsg hE1 (by omega) (by omega)
    have hmaxQ := hs.maxSend Q
    have hwin : spqrWindowOk (s.log Q) (honestMsg E i) = true :=
      wf_windowOk_of_recvCtr (s.log Q) (honestMsg E i) E i hpos hE1 (by omega) hi
    have hmaxEq : max (s.maxRecv Q) E = E := Nat.max_eq_right hmE
    refine ⟨by simp [hs.inWindow, hwin], ?_, ?_, ?_, ?_, hs.lastLe, ?_⟩
    · intro P
      dsimp only
      by_cases hPQ : P = Q
      · subst hPQ
        rw [Function.update_self, Function.update_self]
        change (s.log P).maxSendEpoch ≤ max (s.maxRecv P) E + 1
        omega
      · rw [Function.update_of_ne hPQ, Function.update_of_ne hPQ]
        exact hs.maxSend P
    · intro P
      dsimp only
      by_cases hPQ : P = Q
      · subst hPQ
        rw [Function.update_self, Function.update_self, Function.update_self, hmaxEq,
          wf_recvCtr_cons (s.log P) (honestMsg E i) E i hpos hi]
        exact hrest
      · have hPO : P.other ≠ Q.other := mt wf_other_inj.mp hPQ
        rw [Function.update_of_ne hPQ, Function.update_of_ne hPQ, Function.update_of_ne hPO]
        exact hs.queue P
    · intro P e he
      dsimp only at he ⊢
      by_cases hPQ : P = Q
      · subst hPQ
        rw [Function.update_self, hmaxEq] at he
        rw [Function.update_self, wf_recvCtr_cons (s.log P) (honestMsg E i) E i hpos hi,
          Function.update_of_ne (by omega)]
        exact hs.ctrZero P e (by omega)
      · rw [Function.update_of_ne hPQ] at he ⊢
        exact hs.ctrZero P e he
    · intro P
      dsimp only
      by_cases hPQ : P = Q
      · subst hPQ
        rw [Function.update_self, hmaxEq]; exact hEk.1
      · rw [Function.update_of_ne hPQ]; exact hs.maxRecvLe P
    · intro P p hp
      dsimp only at hp
      by_cases hPO : P = Q.other
      · subst hPO
        rw [Function.update_self] at hp
        exact hs.inFlightLe Q.other p (by rw [hF]; exact List.Mem.tail _ hp)
      · rw [Function.update_of_ne hPO] at hp
        exact hs.inFlightLe P p hp

private theorem wf_step_honest_false (s : SimState) (ev : Ev) (h : s.honest = false) :
    (s.step ev).honest = false := by
  cases ev with
  | send P E => simp [SimState.step, h]
  | deliver P =>
    simp only [SimState.step]
    split <;> simp [h]

private theorem wf_foldl_honest_false (evs : List Ev) (s : SimState) (h : s.honest = false) :
    (evs.foldl SimState.step s).honest = false := by
  induction evs generalizing s with
  | nil => exact h
  | cons ev evs ih => exact ih (s.step ev) (wf_step_honest_false s ev h)

private theorem wf_honest_of_foldl (evs : List Ev) (s : SimState)
    (h : (evs.foldl SimState.step s).honest = true) : s.honest = true := by
  cases hs : s.honest
  · rw [wf_foldl_honest_false evs s hs] at h; cases h
  · rfl

private theorem wf_foldl_inv (evs : List Ev) (k : ℕ) (s : SimState) (hs : Inv k s)
    (hq : k + (evs.filter Ev.isSend).length < 2 ^ 32)
    (hh : (evs.foldl SimState.step s).honest = true) :
    Inv (k + (evs.filter Ev.isSend).length) (evs.foldl SimState.step s) := by
  induction evs generalizing k s with
  | nil => simpa using hs
  | cons ev evs ih =>
    simp only [List.foldl_cons] at hh ⊢
    have hstep_h : (s.step ev).honest = true := wf_honest_of_foldl evs (s.step ev) hh
    cases ev with
    | send Q E =>
      have ht : Ev.isSend (.send Q E) = true := rfl
      simp only [List.filter_cons_of_pos ht, List.length_cons] at hq ⊢
      have hs' := wf_step_send hs (by omega) Q E hstep_h
      have h' := ih (k + 1) (s.step (.send Q E)) hs' (by omega) hh
      have heq : k + 1 + (evs.filter Ev.isSend).length =
          k + ((evs.filter Ev.isSend).length + 1) := by omega
      rwa [heq] at h'
    | deliver Q =>
      have hf : ¬ Ev.isSend (.deliver Q) = true := by simp [Ev.isSend]
      simp only [List.filter_cons_of_neg hf] at hq ⊢
      exact ih k (s.step (.deliver Q)) (wf_step_deliver hs (by omega) Q) hq hh

/-- Every honest FIFO schedule with `< 2 ^ 32` sends satisfies `inWindow = true`. -/
theorem honest_fifo_in_window (evs : List Ev) (hq : (evs.filter Ev.isSend).length < 2 ^ 32)
    (hh : (run evs).honest = true) : (run evs).inWindow = true := by
  exact (wf_foldl_inv evs 0 SimState.init wf_init_inv (by omega) hh).inWindow

end LibsignalSpqrWindowHonest
end CryptoGames
