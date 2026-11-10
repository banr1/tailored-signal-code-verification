/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ChainSyncBase
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import ProofLib.Lemmas
import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble

/-!
# SPQR V1 Symmetric Chain under Honest Traffic

Ghost-state invariants and step specifications for `LibsignalSpqrV1.Chain` over
`spqrHkdfWith F` and `ChainParams.default` (`max_jump = 25000`, `max_ooo_keys = 2000`):

* Key schedule: `genAt F authKey secret e` derives the 96-byte epoch generator for chain epoch `e`,
  `seedOf dir` selects the 32-byte directional seed (matching peer send/receive via `Direction.switch`),
  and `nextAt` / `keyAt` step the per-message HKDF chain.
* Invariants: `SendDirOk`, `RecvDirOk` (tracking accepted indices `R`, high-water counter `R.sup id`,
  and in-window skipped keys in `KeyHistory`), and `ChainOk`.
* Step theorems: `chainNew_ok`, `chainFromVN_ok`, `addEpoch_ok`, `sendKey_ok`, `recvKey_ok`, and
  out-of-window rejection `recvKey_err`, subject to 32-bit counter non-overflow bounds.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.ChainSync

open CryptoVerification.LibsignalSpqrV1
open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)

/-! ## Parameters -/

theorem dparams_maxOoo : dparams.maxOooKeysOrDefault = 2000#32 := by decide +kernel

theorem dparams_maxJump : dparams.maxJumpOrDefault = 25000#32 := by decide +kernel

theorem dparams_trimSize : dparams.trimSize = 2201 := by decide +kernel

/-! ## One epoch direction: the key schedule -/

@[simp] theorem length_stepGen (F : ShaCompress) (next : Bytes) (i : ℕ) :
    (stepGen F next i).length = 64 := by
  simp [stepGen]

theorem length_nextAt (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32) :
    ∀ n, (nextAt F seed n).length = 32
  | 0 => hseed
  | n + 1 => by simp [nextAt]

@[simp] theorem length_keyAt (F : ShaCompress) (seed : Bytes) (n : ℕ) :
    (keyAt F seed n).length = 32 := by
  simp [keyAt]

/-! ## The epoch key schedule -/

@[simp] theorem length_genAt (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes) (e : ℕ) :
    (genAt F authKey secret e).length = 96 := by
  cases e <;> simp [genAt]

theorem length_seedOf (dir : Direction) (g : Bytes) (hg : g.length = 96) :
    (seedOf dir g).length = 32 := by
  cases dir <;> simp [seedOf, hg]

@[simp] theorem length_seedAt (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes)
    (dir : Direction) (e : ℕ) : (seedAt F authKey secret dir e).length = 32 :=
  length_seedOf dir _ (length_genAt F authKey secret e)

theorem cedForDirection_eq (g : Bytes) (dir : Direction) :
    Chain.cedForDirection g dir = ChainEpochDirection.new (seedOf dir g) := by
  cases dir <;> rfl

@[simp] theorem switch_switch (dir : Direction) : dir.switch.switch = dir := by
  cases dir <;> rfl

/-- Peer directional seeds agree: sending on `dir` and receiving on `dir.switch` read the same
32-byte epoch seed (`dir.switch.switch = dir`). -/
theorem seedAt_send_recv (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes)
    (dir : Direction) (e : ℕ) :
    seedAt F authKey secret dir.switch.switch e = seedAt F authKey secret dir e := by
  rw [switch_switch]

/-! ## The send direction -/

theorem sendDirOk_new (F : ShaCompress) (seed : Bytes) :
    SendDirOk F seed 0 (ChainEpochDirection.new seed) :=
  ⟨rfl, rfl⟩

/-- Advancing an honest send direction with `n + 1 < 2 ^ 32` produces key `keyAt F seed n` at
index `n + 1` and updates `next` to `nextAt F seed (n + 1)`. -/
theorem sendDir_nextKey (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32) (n : ℕ)
    (d : ChainEpochDirection) (h : SendDirOk F seed n d) (hn : n + 1 < 2 ^ 32) :
    d.nextKey (spqrHkdfWith F) =
      .ok ({ d with next := nextAt F seed (n + 1), ctr := BitVec.ofNat 32 (n + 1) },
        (BitVec.ofNat 32 (n + 1), keyAt F seed n)) := by
  have hlen : (d.next.length != 32) = false := by
    rw [h.hnext, length_nextAt F seed hseed n]
    rfl
  have hne : (d.ctr == 0xffffffff#32) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have hval : d.ctr.toNat = 4294967295 := congrArg BitVec.toNat heq
    have := h.hctr
    omega
  have hctr' : d.ctr + 1#32 = BitVec.ofNat 32 (n + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, h.hctr]
  unfold ChainEpochDirection.nextKey ChainEpochDirection.nextKeyInternal
  rw [hlen, hne]
  simp only [Bool.false_eq_true, ↓reduceIte, hctr', h.hnext]
  rfl

theorem sendDir_nextKey_ok (F : ShaCompress) (seed : Bytes) (n : ℕ) (d : ChainEpochDirection)
    (hn : n + 1 < 2 ^ 32) :
    SendDirOk F seed (n + 1) { d with next := nextAt F seed (n + 1), ctr := BitVec.ofNat 32 (n + 1) } :=
  ⟨by simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn, rfl⟩

/-! ## The receive direction -/

theorem histRepr_empty (F : ShaCompress) (seed : Bytes) : HistRepr F seed ∅ KeyHistory.new :=
  ⟨[], List.nodup_nil, rfl, rfl⟩

theorem recvDirOk_new (F : ShaCompress) (seed : Bytes) :
    RecvDirOk F seed ∅ (ChainEpochDirection.new seed) where
  hpos := by simp
  hctr := rfl
  hnext := rfl
  hprev := ⟨∅, histRepr_empty F seed, by simp, fun j h1 h2 => by simp [ChainEpochDirection.new] at h2⟩

/-! ### Helpers for `recvDir_key` -/

private theorem chb_toBEBytes4_eq (x : BitVec 32) :
    toBEBytes 4 x =
      [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] :=
  rfl

/-- Lexicographic comparison on 4-byte big-endian encodings agrees with `<` on `BitVec 32`. -/
theorem bytesLt_toBEBytes4 (a b : BitVec 32) :
    bytesLt (toBEBytes 4 a) (toBEBytes 4 b) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [chb_toBEBytes4_eq a, chb_toBEBytes4_eq b]
  simp only [bytesLt, BitVec.lt_def, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split_ifs <;> simp_all <;> omega

/-- 4-byte big-endian encoding is injective on `BitVec 32`. -/
theorem toBEBytes4_injective : Function.Injective (fun x : BitVec 32 => toBEBytes 4 x) := by
  intro a b h
  dsimp only at h
  have h1 := bytesLt_toBEBytes4 a b
  have h2 := bytesLt_toBEBytes4 b a
  have h3 := bytesLt_toBEBytes4 b b
  rw [h, h3] at h1 h2
  simp only [lt_irrefl, decide_false, Bool.false_eq, decide_eq_false_iff_not] at h1 h2
  exact BitVec.eq_of_toNat_eq (by omega)

private abbrev chg_entry (F : ShaCompress) (seed : Bytes) (j : ℕ) : Bytes :=
  histEntry j (keyAt F seed (j - 1))

private theorem chg_length_toBEBytes4 (x : BitVec 32) : (toBEBytes 4 x).length = 4 := by
  simp [toBEBytes]

private theorem chg_length_entry (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (chg_entry F seed j).length = 36 := by
  simp [chg_entry, histEntry, chg_length_toBEBytes4]

private theorem chg_flatten_length_mod (F : ShaCompress) (seed : Bytes) :
    ∀ L : List ℕ, ((L.map (chg_entry F seed)).flatten).length % KeyHistory.KEY_SIZE = 0
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, chg_length_entry,
      KeyHistory.KEY_SIZE]
    have ih := chg_flatten_length_mod F seed xs
    simp only [KeyHistory.KEY_SIZE] at ih
    omega

private theorem chg_entry_take4 (F : ShaCompress) (seed : Bytes) (x : ℕ) (rest : Bytes) :
    ((chg_entry F seed x ++ rest).take 4) = toBEBytes 4 (BitVec.ofNat 32 x) := by
  rw [chg_entry, histEntry, List.append_assoc]
  exact List.take_left' (chg_length_toBEBytes4 _)

private theorem chg_entry_drop4_take32 (F : ShaCompress) (seed : Bytes) (x : ℕ) (rest : Bytes) :
    (((chg_entry F seed x ++ rest).drop 4).take 32) = keyAt F seed (x - 1) := by
  rw [chg_entry, histEntry, List.append_assoc, List.drop_left' (chg_length_toBEBytes4 _)]
  exact List.take_left' (length_keyAt F seed (x - 1))

private theorem chg_toBEBytes4_ne {x j : ℕ} (hx : x < 2 ^ 32) (hj : j < 2 ^ 32) (hne : x ≠ j) :
    (toBEBytes 4 (BitVec.ofNat 32 x) == toBEBytes 4 (BitVec.ofNat 32 j)) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have hbv := toBEBytes4_injective heq
  have hnat := congrArg BitVec.toNat hbv
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hj] at hnat
  exact hne hnat

private theorem chg_getLoop (F : ShaCompress) (seed : Bytes) (j : ℕ) (hj : j < 2 ^ 32)
    (L₂ : List ℕ) :
    ∀ (L₁ P : List ℕ) (self : KeyHistory),
      self.data = ((P ++ L₁ ++ j :: L₂).map (chg_entry F seed)).flatten →
      (∀ x ∈ L₁, x < 2 ^ 32 ∧ x ≠ j) →
      self.getLoop (BitVec.ofNat 32 j) (toBEBytes 4 (BitVec.ofNat 32 j)) dparams
        ((P.map (chg_entry F seed)).flatten).length =
        .ok (self.remove (((P ++ L₁).map (chg_entry F seed)).flatten).length dparams,
          keyAt F seed (j - 1))
  | [], P, self, hdata, _ => by
    simp only [List.append_nil] at hdata ⊢
    let pre := (P.map (chg_entry F seed)).flatten
    let suf := (L₂.map (chg_entry F seed)).flatten
    have hdata' : self.data = pre ++ (chg_entry F seed j ++ suf) := by
      simpa [pre, suf, List.append_assoc] using hdata
    have hlt : pre.length < self.data.length := by
      rw [hdata', List.length_append, List.length_append, chg_length_entry]; omega
    have hdrop : self.data.drop pre.length = chg_entry F seed j ++ suf := by
      rw [hdata', List.drop_left]
    have htake4 : (self.data.drop pre.length).take 4 = toBEBytes 4 (BitVec.ofNat 32 j) := by
      rw [hdrop, chg_entry_take4]
    have hout : (self.data.drop (pre.length + 4)).take 32 = keyAt F seed (j - 1) := by
      rw [← List.drop_drop, hdrop, chg_entry_drop4_take32]
    rw [KeyHistory.getLoop]
    simp only [pre, hlt, ↓reduceDIte, htake4, beq_self_eq_true, ↓reduceIte, hout]
  | x :: L₁', P, self, hdata, hL₁ => by
    let pre := (P.map (chg_entry F seed)).flatten
    let rest := ((L₁' ++ j :: L₂).map (chg_entry F seed)).flatten
    have hdata' : self.data = pre ++ (chg_entry F seed x ++ rest) := by
      simpa [pre, rest, List.append_assoc] using hdata
    have hlt : pre.length < self.data.length := by
      rw [hdata', List.length_append, List.length_append, chg_length_entry]; omega
    have hdrop : self.data.drop pre.length = chg_entry F seed x ++ rest := by
      rw [hdata', List.drop_left]
    have htake4 : (self.data.drop pre.length).take 4 = toBEBytes 4 (BitVec.ofNat 32 x) := by
      rw [hdrop, chg_entry_take4]
    obtain ⟨hxlt, hxne⟩ := hL₁ x List.mem_cons_self
    have hbeq : ((self.data.drop pre.length).take 4 == toBEBytes 4 (BitVec.ofNat 32 j)) = false := by
      rw [htake4, chg_toBEBytes4_ne hxlt hj hxne]
    have hstep : pre.length + KeyHistory.KEY_SIZE =
        (((P ++ [x]).map (chg_entry F seed)).flatten).length := by
      rw [List.map_append, List.flatten_append, List.length_append]
      simp only [pre, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, chg_length_entry, KeyHistory.KEY_SIZE]
    have hassoc : (P ++ [x]) ++ L₁' = P ++ x :: L₁' := by simp [List.append_assoc]
    have ih := chg_getLoop F seed j hj L₂ L₁' (P ++ [x]) self
      (by rw [hassoc]; exact hdata)
      (fun y hy => hL₁ y (List.mem_cons_of_mem x hy))
    rw [KeyHistory.getLoop]
    simp only [pre, hlt, ↓reduceDIte, hbeq, Bool.false_eq_true, ↓reduceIte, hstep, ih, hassoc]

private theorem chg_remove_perm (F : ShaCompress) (seed : Bytes) (j : ℕ) (L₁ L₂ : List ℕ)
    (self : KeyHistory) (hdata : self.data = ((L₁ ++ j :: L₂).map (chg_entry F seed)).flatten) :
    ∃ L' : List ℕ, (j :: L').Perm (L₁ ++ j :: L₂) ∧
      (self.remove ((L₁.map (chg_entry F seed)).flatten).length dparams).data =
        (L'.map (chg_entry F seed)).flatten := by
  let pre := (L₁.map (chg_entry F seed)).flatten
  let ej := chg_entry F seed j
  rcases L₂.eq_nil_or_concat with rfl | ⟨L₃, last, rfl⟩
  · refine ⟨L₁, (List.perm_append_singleton j L₁).symm, ?_⟩
    have hdata' : self.data = pre ++ ej := by simpa [pre, ej] using hdata
    have hlen : ¬ (pre.length + KeyHistory.KEY_SIZE < self.data.length) := by
      rw [hdata', List.length_append, chg_length_entry, KeyHistory.KEY_SIZE]; omega
    simp only [KeyHistory.remove, pre, hlen, ↓reduceIte]
    rw [hdata', List.take_left]
  · rw [List.concat_eq_append] at hdata ⊢
    refine ⟨L₁ ++ last :: L₃, ?_, ?_⟩
    · refine List.Perm.trans List.perm_middle.symm (List.Perm.append_left L₁ (List.Perm.cons j ?_))
      exact (List.perm_append_singleton last L₃).symm
    · let mid := (L₃.map (chg_entry F seed)).flatten
      let elast := chg_entry F seed last
      have hdata1 : self.data = pre ++ (ej ++ mid ++ elast) := by
        simpa [pre, ej, mid, elast, List.append_assoc] using hdata
      have hdata2 : self.data = ((pre ++ ej) ++ mid) ++ elast := by
        simpa [List.append_assoc] using hdata1
      have hlt : pre.length + KeyHistory.KEY_SIZE < self.data.length := by
        rw [hdata2, List.length_append, List.length_append, List.length_append]
        simp only [ej, elast, chg_length_entry, KeyHistory.KEY_SIZE]; omega
      have hnewEnd : self.data.length - KeyHistory.KEY_SIZE = ((pre ++ ej) ++ mid).length := by
        rw [hdata2, List.length_append]
        simp only [elast, chg_length_entry, KeyHistory.KEY_SIZE]; omega
      have hmoved : self.data.drop (self.data.length - KeyHistory.KEY_SIZE) = elast := by
        rw [hnewEnd, hdata2, List.drop_left]
      have hprefix : self.data.take pre.length = pre := by
        rw [hdata1, List.take_left]
      have htakeEnd : self.data.take (self.data.length - KeyHistory.KEY_SIZE) = (pre ++ ej) ++ mid := by
        rw [hnewEnd, hdata2, List.take_left]
      have hpej : pre.length + KeyHistory.KEY_SIZE = (pre ++ ej).length := by
        rw [List.length_append]; simp [ej, chg_length_entry, KeyHistory.KEY_SIZE]
      have hrest : (self.data.take (self.data.length - KeyHistory.KEY_SIZE)).drop
          (pre.length + KeyHistory.KEY_SIZE) = mid := by
        rw [htakeEnd, hpej, List.drop_left]
      simp only [KeyHistory.remove, pre, hlt, ↓reduceIte, hmoved, hprefix, hrest]
      have hlen_eq : (pre ++ elast ++ mid).length = self.data.length - KeyHistory.KEY_SIZE := by
        rw [hnewEnd]
        simp only [ej, elast, chg_length_entry, List.length_append]
      rw [← hlen_eq, List.take_length]
      simp [pre, elast, mid, List.append_assoc]

/-- `KeyHistory.get` retrieves and removes `keyAt F seed (j - 1)` for a stored in-window index
`j ∈ S` when `j + 2000 < 2 ^ 32`, preserving `HistRepr` on `S.erase j`. -/
theorem histRepr_get (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory)
    (hS : HistRepr F seed S h) (hlt : ∀ i ∈ S, i < 2 ^ 32) (j : ℕ) (hj : j ∈ S)
    (ctr : BitVec 32) (hjb : j + 2000 < 2 ^ 32) (hctr : ctr.toNat ≤ j + 2000) :
    ∃ h', h.get (BitVec.ofNat 32 j) ctr dparams = .ok (h', keyAt F seed (j - 1)) ∧
      HistRepr F seed (S.erase j) h' := by
  obtain ⟨L, hnd, hfin, hdata⟩ := hS
  have hjL : j ∈ L := List.mem_toFinset.1 (hfin ▸ hj)
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hjL
  have halign : (h.data.length % KeyHistory.KEY_SIZE != 0) = false := by
    rw [bne_eq_false_iff_eq, hdata]
    exact chg_flatten_length_mod F seed (L₁ ++ j :: L₂)
  have hj32 : j < 2 ^ 32 := by omega
  have hj_toNat : (BitVec.ofNat 32 j).toNat = j := by
    simp only [BitVec.toNat_ofNat]; omega
  have hooo_toNat : dparams.maxOooKeysOrDefault.toNat = 2000 := by
    rw [dparams_maxOoo]; rfl
  have hovf : ¬ ((BitVec.ofNat 32 j).toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) := by
    rw [hj_toNat, hooo_toNat]; omega
  have htrim : ¬ (BitVec.ofNat 32 j + dparams.maxOooKeysOrDefault < ctr) := by
    rw [dparams_maxOoo, BitVec.lt_def, BitVec.toNat_add, hj_toNat]
    change ¬ ((j + 2000) % 2 ^ 32 < ctr.toNat)
    rw [Nat.mod_eq_of_lt hjb]; omega
  have hL₁ : ∀ x ∈ L₁, x < 2 ^ 32 ∧ x ≠ j := by
    intro x hx
    refine ⟨hlt x (hfin ▸ List.mem_toFinset.2 (by simp [hx])), ?_⟩
    rintro rfl
    have hnd' := (List.nodup_append.1 hnd).2.2 x hx x List.mem_cons_self rfl
    exact hnd'
  have hloop := chg_getLoop F seed j hj32 L₂ L₁ [] h (by simpa using hdata) hL₁
  simp only [List.map_nil, List.flatten_nil, List.length_nil, List.nil_append] at hloop
  obtain ⟨L', hperm, hrem⟩ := chg_remove_perm F seed j L₁ L₂ h hdata
  have hnd_cons : (j :: L').Nodup := hperm.nodup_iff.2 hnd
  have hndL' : L'.Nodup := (List.nodup_cons.1 hnd_cons).2
  have hj_not_mem : j ∉ L'.toFinset := by
    rw [List.mem_toFinset]
    exact (List.nodup_cons.1 hnd_cons).1
  have hperm_fin : (j :: L').toFinset = (L₁ ++ j :: L₂).toFinset := by
    ext x; simp only [List.mem_toFinset]; exact hperm.mem_iff
  have hfin' : L'.toFinset = S.erase j := by
    rw [← hfin, ← hperm_fin, List.toFinset_cons, Finset.erase_insert hj_not_mem]
  refine ⟨h.remove ((L₁.map (chg_entry F seed)).flatten).length dparams, ?_, L', hndL', hfin', hrem⟩
  simp only [KeyHistory.get, halign, Bool.false_eq_true, ↓reduceIte, hovf, htrim]
  exact hloop

private def chc_entry (F : ShaCompress) (seed : Bytes) (j : ℕ) : Bytes :=
  histEntry j (keyAt F seed (j - 1))

private def chc_data (F : ShaCompress) (seed : Bytes) (L : List ℕ) : Bytes :=
  (L.map (chc_entry F seed)).flatten

private theorem chc_entry_length (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (chc_entry F seed j).length = 36 := by
  simp [chc_entry, histEntry, toBEBytes]

private theorem chc_entry_take4 (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (chc_entry F seed j).take 4 = toBEBytes 4 (BitVec.ofNat 32 j) := by
  have h4 : (toBEBytes 4 (BitVec.ofNat 32 j)).length = 4 := by simp [toBEBytes]
  rw [chc_entry, histEntry, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

private theorem chc_data_cons (F : ShaCompress) (seed : Bytes) (x : ℕ) (xs : List ℕ) :
    chc_data F seed (x :: xs) = chc_entry F seed x ++ chc_data F seed xs := rfl

private theorem chc_data_append (F : ShaCompress) (seed : Bytes) (L₁ L₂ : List ℕ) :
    chc_data F seed (L₁ ++ L₂) = chc_data F seed L₁ ++ chc_data F seed L₂ := by
  simp [chc_data, List.flatten_append]

private theorem chc_data_length (F : ShaCompress) (seed : Bytes) :
    ∀ L : List ℕ, (chc_data F seed L).length = L.length * 36
  | [] => rfl
  | x :: xs => by
    rw [chc_data_cons, List.length_append, chc_entry_length, chc_data_length F seed xs]
    simp [Nat.succ_mul, Nat.add_comm]

private theorem chc_data_take (F : ShaCompress) (seed : Bytes) :
    ∀ (L : List ℕ) (k : ℕ), (chc_data F seed L).take (k * 36) = chc_data F seed (L.take k)
  | [], _ => by simp [chc_data]
  | _ :: _, 0 => by simp [chc_data]
  | x :: xs, k + 1 => by
    have hlen : (k + 1) * 36 = (chc_entry F seed x).length + k * 36 := by
      rw [chc_entry_length]; omega
    rw [chc_data_cons, hlen, List.take_append]
    simp only [Nat.add_sub_cancel_left, List.take_of_length_le (Nat.le_add_right _ _),
      chc_data_take F seed xs k]
    rfl

private theorem chc_data_drop (F : ShaCompress) (seed : Bytes) :
    ∀ (L : List ℕ) (k : ℕ), (chc_data F seed L).drop (k * 36) = chc_data F seed (L.drop k)
  | [], _ => by simp [chc_data]
  | _ :: _, 0 => by simp [chc_data]
  | x :: xs, k + 1 => by
    have hlen : (k + 1) * 36 = (chc_entry F seed x).length + k * 36 := by
      rw [chc_entry_length]; omega
    rw [chc_data_cons, hlen, List.drop_append]
    simp only [Nat.add_sub_cancel_left, List.drop_eq_nil_of_le (Nat.le_add_right _ _),
      List.nil_append, chc_data_drop F seed xs k]
    rfl

private theorem chc_data_entryKey (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) :
    ((chc_data F seed L).drop (k * 36)).take 4 = toBEBytes 4 (BitVec.ofNat 32 L[k]) := by
  rw [chc_data_drop, List.drop_eq_getElem_cons hk, chc_data_cons,
    List.take_append_of_le_length (by rw [chc_entry_length]; omega), chc_entry_take4]

private def chc_removeIdx (L : List ℕ) (k : ℕ) : List ℕ :=
  if k + 1 < L.length then
    L.take k ++ L.drop (L.length - 1) ++ (L.take (L.length - 1)).drop (k + 1)
  else
    L.take k

private theorem chc_removeIdx_length (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (chc_removeIdx L k).length = L.length - 1 := by
  unfold chc_removeIdx
  split <;> simp <;> omega

private theorem chc_remove_eq (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) (params : ChainParamsPB) :
    KeyHistory.remove { data := chc_data F seed L } (k * 36) params =
      { data := chc_data F seed (chc_removeIdx L k) } := by
  unfold KeyHistory.remove KeyHistory.KEY_SIZE
  congr 1
  dsimp only
  rw [chc_data_length]
  by_cases hlt : k + 1 < L.length
  · have hlt36 : k * 36 + (4 + 32) < L.length * 36 := by omega
    have hsub : L.length * 36 - (4 + 32) = (L.length - 1) * 36 := by omega
    have hadd : k * 36 + (4 + 32) = (k + 1) * 36 := by omega
    have hrem : L.take k ++ L.drop (L.length - 1) ++ (L.take (L.length - 1)).drop (k + 1) =
        chc_removeIdx L k := by
      unfold chc_removeIdx
      simp only [hlt, ↓reduceIte]
    simp only [hlt36, ↓reduceIte]
    rw [hsub, hadd, chc_data_drop, chc_data_take, chc_data_take, chc_data_drop,
      ← chc_data_append, ← chc_data_append, hrem,
      List.take_of_length_le (by rw [chc_data_length, chc_removeIdx_length L k hk])]
  · have hlt36 : ¬ (k * 36 + (4 + 32) < L.length * 36) := by omega
    unfold chc_removeIdx
    simp only [hlt36, hlt, ↓reduceIte, chc_data_take]

private theorem chc_perm_rearrange (A B C : List ℕ) (x : ℕ) :
    (A ++ (x :: B) ++ C).Perm (x :: (A ++ C ++ B)) := by
  rw [List.append_assoc, List.cons_append]
  refine List.perm_middle.trans (List.Perm.cons x ?_)
  rw [List.append_assoc]
  exact List.Perm.append_left A List.perm_append_comm

private theorem chc_removeIdx_perm (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    L.Perm (L[k] :: chc_removeIdx L k) := by
  unfold chc_removeIdx
  split_ifs with hlt
  · let M := L.take (L.length - 1)
    have hMlen : k < M.length := by simp [M]; omega
    have hMtake : M.take k = L.take k := by
      simp [M, List.take_take, Nat.min_eq_left (by omega : k ≤ L.length - 1)]
    have hMget : M[k] = L[k] := List.getElem_take
    have hMdecomp : M = L.take k ++ (L[k] :: M.drop (k + 1)) := by
      calc M = M.take k ++ M.drop k := (List.take_append_drop k M).symm
        _ = L.take k ++ (L[k] :: M.drop (k + 1)) := by
          rw [hMtake, List.drop_eq_getElem_cons hMlen, hMget]
    have hLdecomp : L = L.take k ++ (L[k] :: M.drop (k + 1)) ++ L.drop (L.length - 1) := by
      calc L = M ++ L.drop (L.length - 1) := (List.take_append_drop (L.length - 1) L).symm
        _ = L.take k ++ (L[k] :: M.drop (k + 1)) ++ L.drop (L.length - 1) := by
          rw [← hMdecomp]
    conv_lhs => rw [hLdecomp]
    exact chc_perm_rearrange (L.take k) (M.drop (k + 1)) (L.drop (L.length - 1)) L[k]
  · have hdrop : L.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have hLdecomp : L = L.take k ++ [L[k]] := by
      calc L = L.take k ++ L.drop k := (List.take_append_drop k L).symm
        _ = L.take k ++ [L[k]] := by rw [List.drop_eq_getElem_cons hk, hdrop]
    conv_lhs => rw [hLdecomp]
    exact List.perm_append_singleton L[k] (L.take k)

private theorem chc_entry_not_in_window (ctr : BitVec 32) (hctr : 2000 ≤ ctr.toNat) (j : ℕ)
    (hjlt : j < ctr.toNat)
    (hlt : bytesLt (toBEBytes 4 (BitVec.ofNat 32 j)) (toBEBytes 4 (ctr - 2000#32)) = true) :
    ¬ (ctr.toNat ≤ j + 2000) := by
  rw [bytesLt_toBEBytes4, decide_eq_true_eq] at hlt
  have hj32 : (BitVec.ofNat 32 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := ctr.isLt; omega)]
  have hsub32 : (ctr - 2000#32).toNat = ctr.toNat - 2000 := by
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · show (2000#32).toNat ≤ ctr.toNat
      exact hctr
  omega

private theorem chc_gcLoop_ok (F : ShaCompress) (seed : Bytes) (ctr : BitVec 32)
    (hctr : 2000 ≤ ctr.toNat) :
    ∀ (n : ℕ) (L : List ℕ) (k : ℕ), L.length - k = n → k ≤ L.length →
      L.Nodup → (∀ i ∈ L, 1 ≤ i ∧ i < ctr.toNat) →
      ∃ L' : List ℕ,
        KeyHistory.gcLoop { data := chc_data F seed L } (toBEBytes 4 (ctr - 2000#32)) dparams (k * 36) =
          .ok { data := chc_data F seed L' } ∧
        L'.Nodup ∧
        (∀ x ∈ L', x ∈ L) ∧
        (∀ j ∈ L, ctr.toNat ≤ j + 2000 → j ∈ L')
  | 0, L, k, hn, hk, hnd, hL => by
    have hkeq : k = L.length := by omega
    subst hkeq
    rw [KeyHistory.gcLoop.eq_1]
    have hnotlt : ¬ (L.length * 36 < (chc_data F seed L).length) := by
      rw [chc_data_length]; omega
    simp only [hnotlt, ↓reduceDIte]
    exact ⟨L, rfl, hnd, fun _ hx => hx, fun _ hj _ => hj⟩
  | n + 1, L, k, hn, hk, hnd, hL => by
    have hklt : k < L.length := by omega
    rw [KeyHistory.gcLoop.eq_1]
    have hlt36 : k * 36 < (chc_data F seed L).length := by
      rw [chc_data_length]; omega
    have hbounds : ¬ ((chc_data F seed L).length < k * 36 + 4) := by
      rw [chc_data_length]; omega
    simp only [hlt36, ↓reduceDIte, hbounds, ↓reduceIte]
    rw [chc_data_entryKey F seed L k hklt]
    by_cases hlt : bytesLt (toBEBytes 4 (BitVec.ofNat 32 L[k])) (toBEBytes 4 (ctr - 2000#32)) = true
    · simp only [hlt, ↓reduceIte, chc_remove_eq F seed L k hklt dparams]
      have hperm := chc_removeIdx_perm L k hklt
      have hrem_len : (chc_removeIdx L k).length = L.length - 1 := chc_removeIdx_length L k hklt
      have hnd_cons : (L[k] :: chc_removeIdx L k).Nodup := hperm.nodup_iff.mp hnd
      have hnd' : (chc_removeIdx L k).Nodup := (List.nodup_cons.mp hnd_cons).2
      have hsub : ∀ x ∈ chc_removeIdx L k, x ∈ L := fun x hx =>
        hperm.mem_iff.mpr (List.mem_cons_of_mem L[k] hx)
      have hL' : ∀ i ∈ chc_removeIdx L k, 1 ≤ i ∧ i < ctr.toNat := fun i hi => hL i (hsub i hi)
      obtain ⟨L', hgc, hnd'', hsub', hwin⟩ :=
        chc_gcLoop_ok F seed ctr hctr n (chc_removeIdx L k) k (by omega) (by omega) hnd' hL'
      refine ⟨L', hgc, hnd'', fun x hx => hsub x (hsub' x hx), fun j hj hjwin => ?_⟩
      rcases List.mem_cons.mp (hperm.mem_iff.mp hj) with rfl | hj'
      · exfalso
        have hk_mem : L[k] ∈ L := List.getElem_mem hklt
        exact chc_entry_not_in_window ctr hctr L[k] (hL L[k] hk_mem).2 hlt hjwin
      · exact hwin j hj' hjwin
    · simp only [hlt, Bool.false_eq_true, ↓reduceIte]
      have hstep : k * 36 + KeyHistory.KEY_SIZE = (k + 1) * 36 := by
        unfold KeyHistory.KEY_SIZE; omega
      rw [hstep]
      exact chc_gcLoop_ok F seed ctr hctr n L (k + 1) (by omega) (by omega) hnd hL

/-- `KeyHistory.gc` preserves `HistRepr` on a subset of `S` retaining every entry within the
2000-key out-of-order window (`ctr.toNat ≤ j + 2000`). -/
theorem histRepr_gc (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory)
    (hS : HistRepr F seed S h) (ctr : BitVec 32) (hS' : ∀ i ∈ S, 1 ≤ i ∧ i < ctr.toNat) :
    ∃ h' S', h.gc ctr dparams = .ok h' ∧ HistRepr F seed S' h' ∧ S' ⊆ S ∧
      ∀ j ∈ S, ctr.toNat ≤ j + 2000 → j ∈ S' := by
  unfold KeyHistory.gc
  by_cases htrim : h.data.length ≥ dparams.trimSize * KeyHistory.KEY_SIZE
  · simp only [htrim, ↓reduceIte]
    rcases hS with ⟨L, hnd, rfl, hdata⟩
    have hdata' : h = { data := chc_data F seed L } := by
      cases h; congr
    have hlen : h.data.length = L.length * 36 := by
      rw [hdata]; exact chc_data_length F seed L
    have htrim_val : dparams.trimSize * KeyHistory.KEY_SIZE = 2201 * 36 := by
      rw [dparams_trimSize]; rfl
    have hL2201 : 2201 ≤ L.length := by omega
    have hsub_ico : L.toFinset ⊆ Finset.Ico 1 ctr.toNat := by
      intro i hi
      rw [Finset.mem_Ico]
      exact hS' i hi
    have hcard := Finset.card_le_card hsub_ico
    rw [List.card_toFinset, List.dedup_eq_self.mpr hnd, Nat.card_Ico] at hcard
    have hctr2000 : 2000 ≤ ctr.toNat := by omega
    have hnot_underflow : ¬ (ctr < 2000#32) := by
      rw [BitVec.lt_def]
      change ¬ (ctr.toNat < 2000)
      omega
    rw [dparams_maxOoo]
    simp only [hnot_underflow, ↓reduceIte, hdata']
    have hL_bound : ∀ i ∈ L, 1 ≤ i ∧ i < ctr.toNat := fun i hi =>
      hS' i (List.mem_toFinset.mpr hi)
    obtain ⟨L', hgc, hnd', hsub', hwin⟩ :=
      chc_gcLoop_ok F seed ctr hctr2000 L.length L 0 (by omega) (by omega) hnd hL_bound
    have h0 : 0 * 36 = 0 := rfl
    rw [h0] at hgc
    refine ⟨{ data := chc_data F seed L' }, L'.toFinset, hgc, ⟨L', hnd', rfl, rfl⟩, ?_, ?_⟩
    · intro x hx
      exact List.mem_toFinset.mpr (hsub' x (List.mem_toFinset.mp hx))
    · intro j hj hjwin
      exact List.mem_toFinset.mpr (hwin j (List.mem_toFinset.mp hj) hjwin)
  · simp only [htrim, ↓reduceIte]
    exact ⟨h, S, rfl, hS, Finset.Subset.refl S, fun _ hj _ => hj⟩

private theorem chk_bv32_toNat_of_lt {n : ℕ} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem chk_ctr_ne_max {ctr : BitVec 32} (h : ctr.toNat + 1 < 2 ^ 32) :
    (ctr == 0xffffffff#32) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  subst heq
  change 4294967295 + 1 < 2 ^ 32 at h
  omega

private theorem chk_ctr_add_one {ctr : BitVec 32} {c : ℕ}
    (hctr : ctr.toNat = c) (hc : c + 1 < 2 ^ 32) :
    ctr + 1#32 = BitVec.ofNat 32 (c + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hctr,
    Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 32), Nat.mod_eq_of_lt hc]

private theorem chk_nextKeyInternal_ok (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32)
    (c : ℕ) (next : Bytes) (ctr : BitVec 32)
    (hctr : ctr.toNat = c) (hnext : next = nextAt F seed c) (hc : c + 1 < 2 ^ 32) :
    ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) next ctr =
      .ok (nextAt F seed (c + 1), BitVec.ofNat 32 (c + 1),
        (BitVec.ofNat 32 (c + 1), keyAt F seed c)) := by
  unfold ChainEpochDirection.nextKeyInternal
  have hlen : (next.length != 32) = false := by
    rw [bne_eq_false_iff_eq, hnext, length_nextAt F seed hseed c]
  have hmax : (ctr == 0xffffffff#32) = false := chk_ctr_ne_max (hctr ▸ hc)
  have hadd : ctr + 1#32 = BitVec.ofNat 32 (c + 1) := chk_ctr_add_one hctr hc
  rw [hlen, hmax]
  simp only [Bool.false_eq_true, ↓reduceIte, hadd, hnext, nextAt, keyAt, stepGen, zeros32]

private theorem chk_histRepr_add (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory)
    (hS : HistRepr F seed S h) (c : ℕ) (hnot : c + 1 ∉ S) :
    HistRepr F seed (S ∪ {c + 1})
      (h.add (BitVec.ofNat 32 (c + 1), keyAt F seed c) dparams) := by
  rcases hS with ⟨L, hnodup, htoFin, hdata⟩
  refine ⟨L ++ [c + 1], ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnodup, List.nodup_singleton _, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    subst hy hxy
    exact hnot (htoFin ▸ List.mem_toFinset.mpr hx)
  · ext x
    simp [← htoFin]
  · simp only [KeyHistory.add, hdata, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      Nat.add_sub_cancel, histEntry, List.append_assoc]

private theorem chk_ioo_filter_eq_empty {c atN : ℕ} (h1 : c < atN) (h2 : ¬ c + 1 < atN) :
    ((Finset.Ioo c atN).filter fun j => atN ≤ j + 2000) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro x hx
  rw [Finset.mem_Ioo] at hx
  omega

private theorem chk_ioo_step_true {S : Finset ℕ} {c atN : ℕ}
    (hc : c + 1 < atN) (hw : atN ≤ c + 1 + 2000) :
    (S ∪ {c + 1}) ∪ ((Finset.Ioo (c + 1) atN).filter fun j => atN ≤ j + 2000) =
      S ∪ ((Finset.Ioo c atN).filter fun j => atN ≤ j + 2000) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Ioo]
  by_cases hx : x ∈ S <;> simp only [hx, true_or, false_or]; omega

private theorem chk_ioo_step_false {S : Finset ℕ} {c atN : ℕ}
    (hw : ¬ atN ≤ c + 1 + 2000) :
    S ∪ ((Finset.Ioo (c + 1) atN).filter fun j => atN ≤ j + 2000) =
      S ∪ ((Finset.Ioo c atN).filter fun j => atN ≤ j + 2000) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioo]
  by_cases hx : x ∈ S <;> simp only [hx, true_or, false_or]; omega

/-- `keyAdvanceLoop` derives skipped keys up to `atIdx - 1`, storing every skipped index within
the 2000-key window into `prev`. -/
theorem keyAdvanceLoop_ok (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32)
    (d : ChainEpochDirection) (S : Finset ℕ) (hS : HistRepr F seed S d.prev)
    (hS' : ∀ i ∈ S, i ≤ d.ctr.toNat) (hnext : d.next = nextAt F seed d.ctr.toNat)
    (atN : ℕ) (hc : d.ctr.toNat < atN) (hat : atN + 2000 ≤ 2 ^ 32) :
    ∃ d', d.keyAdvanceLoop (spqrHkdfWith F) (BitVec.ofNat 32 atN) dparams = .ok d' ∧
      d'.ctr.toNat = atN - 1 ∧ d'.next = nextAt F seed (atN - 1) ∧
      HistRepr F seed
        (S ∪ (Finset.Ioo d.ctr.toNat atN).filter fun j => atN ≤ j + 2000) d'.prev := by
  suffices ∀ (fuel : ℕ) (d : ChainEpochDirection) (S : Finset ℕ),
      atN - d.ctr.toNat ≤ fuel →
      HistRepr F seed S d.prev →
      (∀ i ∈ S, i ≤ d.ctr.toNat) →
      d.next = nextAt F seed d.ctr.toNat →
      d.ctr.toNat < atN →
      ∃ d', d.keyAdvanceLoop (spqrHkdfWith F) (BitVec.ofNat 32 atN) dparams = .ok d' ∧
        d'.ctr.toNat = atN - 1 ∧ d'.next = nextAt F seed (atN - 1) ∧
        HistRepr F seed
          (S ∪ (Finset.Ioo d.ctr.toNat atN).filter fun j => atN ≤ j + 2000) d'.prev from
    this (atN - d.ctr.toNat) d S le_rfl hS hS' hnext hc
  intro fuel
  induction fuel with
  | zero =>
    intro d S hfuel _ _ _ hc
    omega
  | succ fuel ih =>
    intro d S hfuel hS hS' hnext hc
    have hat32 : (BitVec.ofNat 32 atN).toNat = atN := chk_bv32_toNat_of_lt (by omega)
    rw [ChainEpochDirection.keyAdvanceLoop]
    by_cases hstep : d.ctr.toNat + 1 < (BitVec.ofNat 32 atN).toNat
    · have hstep' : d.ctr.toNat + 1 < atN := by omega
      simp only [hstep, ↓reduceDIte]
      have hnk_eq := chk_nextKeyInternal_ok F seed hseed d.ctr.toNat d.next d.ctr rfl hnext (by omega)
      split
      · rename_i p hnk
        rw [hnk_eq] at hnk
        contradiction
      · rename_i next' ctr' k hnk
        rw [hnk_eq] at hnk
        injection hnk with h1
        injection h1 with hnext' h2
        injection h2 with hctr' hk
        subst hnext' hctr' hk
        simp only [dparams_maxOoo]
        have hctr'_toNat : (BitVec.ofNat 32 (d.ctr.toNat + 1)).toNat = d.ctr.toNat + 1 :=
          chk_bv32_toNat_of_lt (by omega)
        have hno_ovf : ¬ (BitVec.ofNat 32 (d.ctr.toNat + 1)).toNat + (2000#32 : BitVec 32).toNat ≥ 2 ^ 32 := by
          rw [hctr'_toNat]
          change ¬ (d.ctr.toNat + 1 + 2000 ≥ 2 ^ 32)
          omega
        simp only [hno_ovf, ↓reduceIte]
        have hge_iff : (BitVec.ofNat 32 (d.ctr.toNat + 1) + 2000#32 ≥ BitVec.ofNat 32 atN) ↔
            atN ≤ d.ctr.toNat + 1 + 2000 := by
          change (BitVec.ofNat 32 atN).toNat ≤ (BitVec.ofNat 32 (d.ctr.toNat + 1) + 2000#32).toNat ↔ _
          rw [hat32, BitVec.toNat_add, hctr'_toNat]
          change atN ≤ (d.ctr.toNat + 1 + 2000) % 2 ^ 32 ↔ _
          rw [Nat.mod_eq_of_lt (by omega)]
        by_cases hw : atN ≤ d.ctr.toNat + 1 + 2000
        · have hge : BitVec.ofNat 32 (d.ctr.toNat + 1) + 2000#32 ≥ BitVec.ofNat 32 atN :=
            hge_iff.mpr hw
          simp only [hge, ↓reduceIte]
          have hnot : d.ctr.toNat + 1 ∉ S := fun hm => by have := hS' _ hm; omega
          have hS1 : HistRepr F seed (S ∪ {d.ctr.toNat + 1})
              (d.prev.add (BitVec.ofNat 32 (d.ctr.toNat + 1), keyAt F seed d.ctr.toNat) dparams) :=
            chk_histRepr_add F seed S d.prev hS d.ctr.toNat hnot
          have hS1' : ∀ i ∈ S ∪ {d.ctr.toNat + 1}, i ≤ (BitVec.ofNat 32 (d.ctr.toNat + 1)).toNat := by
            intro i hi
            rw [hctr'_toNat]
            rcases Finset.mem_union.mp hi with hi | hi
            · have := hS' i hi; omega
            · simp only [Finset.mem_singleton] at hi; omega
          obtain ⟨d', hd', hctr_d', hnext_d', hprev_d'⟩ :=
            ih { ctr := BitVec.ofNat 32 (d.ctr.toNat + 1),
                 next := nextAt F seed (d.ctr.toNat + 1),
                 prev := d.prev.add (BitVec.ofNat 32 (d.ctr.toNat + 1), keyAt F seed d.ctr.toNat) dparams }
              (S ∪ {d.ctr.toNat + 1})
              (by dsimp only; omega)
              hS1 hS1'
              (by dsimp only; rw [hctr'_toNat])
              (by dsimp only; omega)
          dsimp only at hprev_d'
          rw [hctr'_toNat, chk_ioo_step_true hstep' hw] at hprev_d'
          exact ⟨d', hd', hctr_d', hnext_d', hprev_d'⟩
        · have hnge : ¬ (BitVec.ofNat 32 (d.ctr.toNat + 1) + 2000#32 ≥ BitVec.ofNat 32 atN) :=
            fun h => hw (hge_iff.mp h)
          simp only [hnge, ↓reduceIte]
          have hS1' : ∀ i ∈ S, i ≤ (BitVec.ofNat 32 (d.ctr.toNat + 1)).toNat := by
            intro i hi; rw [hctr'_toNat]; have := hS' i hi; omega
          obtain ⟨d', hd', hctr_d', hnext_d', hprev_d'⟩ :=
            ih { ctr := BitVec.ofNat 32 (d.ctr.toNat + 1),
                 next := nextAt F seed (d.ctr.toNat + 1),
                 prev := d.prev }
              S
              (by dsimp only; omega)
              hS hS1'
              (by dsimp only; rw [hctr'_toNat])
              (by dsimp only; omega)
          dsimp only at hprev_d'
          rw [hctr'_toNat, chk_ioo_step_false hw] at hprev_d'
          exact ⟨d', hd', hctr_d', hnext_d', hprev_d'⟩
    · have hstep' : ¬ d.ctr.toNat + 1 < atN := by omega
      have hmax : (d.ctr == 0xffffffff#32) = false := chk_ctr_ne_max (by omega)
      simp only [hstep, ↓reduceDIte, hmax, Bool.false_eq_true, ↓reduceIte]
      have heq : d.ctr.toNat = atN - 1 := by omega
      refine ⟨d, rfl, heq, heq ▸ hnext, ?_⟩
      rw [chk_ioo_filter_eq_empty hc hstep', Finset.union_empty]
      exact hS

private def chr_entry (F : ShaCompress) (seed : Bytes) (j : ℕ) : Bytes :=
  histEntry j (keyAt F seed (j - 1))

private def chr_data (F : ShaCompress) (seed : Bytes) (L : List ℕ) : Bytes :=
  (L.map (chr_entry F seed)).flatten

@[simp] private theorem chr_length_toBEBytes (n : ℕ) {w : ℕ} (x : BitVec w) :
    (toBEBytes n x).length = n := by
  simp [toBEBytes]

@[simp] private theorem chr_entry_length (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (chr_entry F seed j).length = 36 := by
  simp [chr_entry, histEntry, length_keyAt]

private theorem chr_entry_take4 (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (chr_entry F seed j).take 4 = toBEBytes 4 (BitVec.ofNat 32 j) := by
  simp [chr_entry, histEntry]

@[simp] private theorem chr_data_nil (F : ShaCompress) (seed : Bytes) :
    chr_data F seed [] = [] := rfl

@[simp] private theorem chr_data_cons (F : ShaCompress) (seed : Bytes) (x : ℕ) (xs : List ℕ) :
    chr_data F seed (x :: xs) = chr_entry F seed x ++ chr_data F seed xs := rfl

private theorem chr_data_append (F : ShaCompress) (seed : Bytes) (A B : List ℕ) :
    chr_data F seed (A ++ B) = chr_data F seed A ++ chr_data F seed B := by
  simp [chr_data, List.map_append, List.flatten_append]

@[simp] private theorem chr_data_length (F : ShaCompress) (seed : Bytes) (L : List ℕ) :
    (chr_data F seed L).length = 36 * L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [chr_data_cons, List.length_append, chr_entry_length, ih, List.length_cons]
    omega

private theorem chr_data_drop (F : ShaCompress) (seed : Bytes) :
    ∀ (k : ℕ) (L : List ℕ), (chr_data F seed L).drop (36 * k) = chr_data F seed (L.drop k)
  | 0, L => by simp
  | k + 1, [] => by simp
  | k + 1, x :: xs => by
    have h1 : 36 * (k + 1) = (chr_entry F seed x).length + 36 * k := by
      rw [chr_entry_length]; omega
    rw [chr_data_cons, h1, List.drop_append, List.drop_of_length_le (by omega),
      List.nil_append, Nat.add_sub_cancel_left, List.drop_succ_cons]
    exact chr_data_drop F seed k xs

private theorem chr_data_take (F : ShaCompress) (seed : Bytes) :
    ∀ (k : ℕ) (L : List ℕ), (chr_data F seed L).take (36 * k) = chr_data F seed (L.take k)
  | 0, L => by simp
  | k + 1, [] => by simp
  | k + 1, x :: xs => by
    have h1 : 36 * (k + 1) = (chr_entry F seed x).length + 36 * k := by
      rw [chr_entry_length]; omega
    rw [chr_data_cons, h1, List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, List.take_succ_cons, chr_data_cons, chr_data_take F seed k xs]

private theorem chr_data_drop_take4 (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) :
    ((chr_data F seed L).drop (36 * k)).take 4 = toBEBytes 4 (BitVec.ofNat 32 L[k]) := by
  rw [chr_data_drop, List.drop_eq_getElem_cons hk, chr_data_cons,
    List.take_append_of_le_length (by rw [chr_entry_length]; omega), chr_entry_take4]

private def chr_swapRemove (L : List ℕ) (k : ℕ) : List ℕ :=
  if k + 1 < L.length then
    L.take k ++ L.drop (L.length - 1) ++ (L.take (L.length - 1)).drop (k + 1)
  else
    L.take k

private theorem chr_swapRemove_length (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (chr_swapRemove L k).length = L.length - 1 := by
  unfold chr_swapRemove
  split_ifs with hlt <;> simp <;> omega

private theorem chr_remove_data (F : ShaCompress) (seed : Bytes) (self : KeyHistory)
    (L : List ℕ) (hdata : self.data = chr_data F seed L) (k : ℕ) (hk : k < L.length) :
    (self.remove (36 * k) dparams).data = chr_data F seed (chr_swapRemove L k) := by
  unfold KeyHistory.remove chr_swapRemove
  simp only [KeyHistory.KEY_SIZE, hdata, chr_data_length]
  by_cases hlt : k + 1 < L.length
  · have hlt36 : 36 * k + (4 + 32) < 36 * L.length := by omega
    have hsub : 36 * L.length - (4 + 32) = 36 * (L.length - 1) := by omega
    have hadd : 36 * k + (4 + 32) = 36 * (k + 1) := by omega
    simp only [hlt36, hlt, ↓reduceIte]
    simp only [hsub, hadd, chr_data_drop, chr_data_take, ← chr_data_append]
    congr 1
    apply List.take_of_length_le
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · have hlt36 : ¬ (36 * k + (4 + 32) < 36 * L.length) := by omega
    simp only [hlt36, hlt, ↓reduceIte, chr_data_take]

private theorem chr_perm_swapRemove (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    L.Perm (L[k] :: chr_swapRemove L k) := by
  unfold chr_swapRemove
  by_cases hlt : k + 1 < L.length
  · simp only [hlt, ↓reduceIte]
    have hk1 : k < (L.take (L.length - 1)).length := by simp; omega
    have hsplit1 : L = L.take (L.length - 1) ++ L.drop (L.length - 1) :=
      (List.take_append_drop (L.length - 1) L).symm
    have hsplit2 : L.take (L.length - 1) =
        L.take k ++ (L[k] :: (L.take (L.length - 1)).drop (k + 1)) := by
      have htd := (List.take_append_drop k (L.take (L.length - 1))).symm
      rw [List.take_take, Nat.min_eq_left (by omega),
        List.drop_eq_getElem_cons hk1, List.getElem_take] at htd
      exact htd
    conv_lhs => rw [hsplit1, hsplit2, List.append_assoc]
    have hmid : (L.take k ++ L[k] :: ((L.take (L.length - 1)).drop (k + 1) ++ L.drop (L.length - 1))).Perm
        (L[k] :: (L.take k ++ ((L.take (L.length - 1)).drop (k + 1) ++ L.drop (L.length - 1)))) :=
      List.perm_middle
    refine hmid.trans (List.Perm.cons L[k] ?_)
    rw [List.append_assoc]
    exact List.Perm.append_left (L.take k) List.perm_append_comm
  · simp only [hlt, ↓reduceIte]
    have hdrop : L.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have htd := (List.take_append_drop k L).symm
    rw [List.drop_eq_getElem_cons hk, hdrop] at htd
    conv_lhs => rw [htd]
    exact List.perm_append_singleton L[k] (L.take k)

private theorem chr_swapRemove_nodup_toFinset (L : List ℕ) (hNodup : L.Nodup) (k : ℕ)
    (hk : k < L.length) :
    (chr_swapRemove L k).Nodup ∧ (chr_swapRemove L k).toFinset = L.toFinset.erase L[k] := by
  have hPerm := chr_perm_swapRemove L k hk
  have hNodupCons : (L[k] :: chr_swapRemove L k).Nodup := hPerm.nodup_iff.mp hNodup
  rw [List.nodup_cons] at hNodupCons
  refine ⟨hNodupCons.2, ?_⟩
  have hFinEq : L.toFinset = (L[k] :: chr_swapRemove L k).toFinset := by
    ext x; simp [hPerm.mem_iff]
  rw [hFinEq, List.toFinset_cons, Finset.erase_insert (by simp [hNodupCons.1])]

private theorem chr_gcLoop_ok (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (ctr : BitVec 32)
    (hbound : ∀ i ∈ S, i < 2 ^ 32) (hctr : 2000 ≤ ctr.toNat) :
    ∀ (n : ℕ) (self : KeyHistory) (L : List ℕ) (k : ℕ),
      L.length - k = n →
      L.Nodup →
      self.data = chr_data F seed L →
      L.toFinset ⊆ S →
      (∀ j ∈ S, ctr.toNat ≤ j + 2000 → j ∈ L.toFinset) →
      ∃ h' S',
        KeyHistory.gcLoop self (toBEBytes 4 (ctr - dparams.maxOooKeysOrDefault)) dparams (36 * k) =
          .ok h' ∧
        HistRepr F seed S' h' ∧ S' ⊆ S ∧
        ∀ j ∈ S, ctr.toNat ≤ j + 2000 → j ∈ S'
  | 0, self, L, k, hn, hNodup, hdata, hsub, hkeep => by
    have hnotlt : ¬ (36 * k < self.data.length) := by rw [hdata, chr_data_length]; omega
    rw [KeyHistory.gcLoop]
    simp only [hnotlt, ↓reduceDIte]
    exact ⟨self, L.toFinset, rfl, ⟨L, hNodup, rfl, hdata⟩, hsub, hkeep⟩
  | n + 1, self, L, k, hn, hNodup, hdata, hsub, hkeep => by
    have hk : k < L.length := by omega
    have hlt : 36 * k < self.data.length := by rw [hdata, chr_data_length]; omega
    have hnot4 : ¬ (self.data.length < 36 * k + 4) := by rw [hdata, chr_data_length]; omega
    have htake4 : (self.data.drop (36 * k)).take 4 = toBEBytes 4 (BitVec.ofNat 32 L[k]) := by
      rw [hdata, chr_data_drop_take4 F seed L k hk]
    rw [KeyHistory.gcLoop]
    simp only [hlt, ↓reduceDIte, hnot4, ↓reduceIte, htake4]
    by_cases hb : bytesLt (toBEBytes 4 (BitVec.ofNat 32 L[k]))
        (toBEBytes 4 (ctr - dparams.maxOooKeysOrDefault)) = true
    · simp only [hb, ↓reduceIte]
      rw [bytesLt_toBEBytes4, decide_eq_true_eq] at hb
      have hLkMemS : L[k] ∈ S := hsub (List.mem_toFinset.mpr (List.getElem_mem hk))
      have hLk32 : L[k] < 2 ^ 32 := hbound L[k] hLkMemS
      have hLkVal : (BitVec.ofNat 32 L[k]).toNat = L[k] := Nat.mod_eq_of_lt hLk32
      have hSubVal : (ctr - dparams.maxOooKeysOrDefault).toNat = ctr.toNat - 2000 := by
        rw [dparams_maxOoo, BitVec.toNat_sub_of_le]
        · rfl
        · change (2000#32 : BitVec 32).toNat ≤ ctr.toNat; exact hctr
      rw [hLkVal, hSubVal] at hb
      rcases chr_swapRemove_nodup_toFinset L hNodup k hk with ⟨hNodup', hFin'⟩
      have hlen' : (chr_swapRemove L k).length - k = n := by
        rw [chr_swapRemove_length L k hk]; omega
      exact chr_gcLoop_ok F seed S ctr hbound hctr n (self.remove (36 * k) dparams)
        (chr_swapRemove L k) k hlen' hNodup' (chr_remove_data F seed self L hdata k hk)
        (by rw [hFin']; exact fun x hx => hsub (Finset.mem_of_mem_erase hx))
        (fun j hj hwin => by
          rw [hFin', Finset.mem_erase]
          exact ⟨by omega, hkeep j hj hwin⟩)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
        simp only [KeyHistory.KEY_SIZE]; omega
      rw [hstep]
      exact chr_gcLoop_ok F seed S ctr hbound hctr n self L (k + 1) (by omega)
        hNodup hdata hsub hkeep

private theorem chr_histRepr_gc (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory)
    (hS : HistRepr F seed S h) (ctr : BitVec 32) (hS' : ∀ i ∈ S, 1 ≤ i ∧ i ≤ ctr.toNat) :
    ∃ h' S', h.gc ctr dparams = .ok h' ∧ HistRepr F seed S' h' ∧ S' ⊆ S ∧
      ∀ j ∈ S, ctr.toNat ≤ j + 2000 → j ∈ S' := by
  rcases hS with ⟨L, hNodup, hFin, hdata⟩
  change h.data = chr_data F seed L at hdata
  unfold KeyHistory.gc
  by_cases htrim : h.data.length ≥ dparams.trimSize * KeyHistory.KEY_SIZE
  · simp only [htrim, ↓reduceIte]
    have hcard : S.card = L.length := by rw [← hFin, List.toFinset_card_of_nodup hNodup]
    have hlen : h.data.length = 36 * S.card := by rw [hdata, chr_data_length, hcard]
    have hS_sub : S ⊆ Finset.Icc 1 ctr.toNat := by
      intro i hi
      rw [Finset.mem_Icc]
      exact hS' i hi
    have hcard_le : S.card ≤ ctr.toNat := by
      have h1 := Finset.card_le_card hS_sub
      rw [Nat.card_Icc] at h1
      omega
    have hctr2000 : 2000 ≤ ctr.toNat := by
      rw [dparams_trimSize, KeyHistory.KEY_SIZE] at htrim
      omega
    have hnotlt : ¬ (ctr < dparams.maxOooKeysOrDefault) := by
      rw [dparams_maxOoo]
      change ¬ (ctr.toNat < 2000)
      omega
    simp only [hnotlt, ↓reduceIte]
    have hbound : ∀ i ∈ S, i < 2 ^ 32 := fun i hi =>
      Nat.lt_of_le_of_lt (hS' i hi).2 ctr.isLt
    have h0 := chr_gcLoop_ok F seed S ctr hbound hctr2000 L.length h L 0 (Nat.sub_zero _)
      hNodup hdata (by rw [hFin]) (fun j hj _ => by rwa [hFin])
    simpa using h0
  · simp only [htrim, ↓reduceIte]
    exact ⟨h, S, rfl, ⟨L, hNodup, hFin, hdata⟩, Finset.Subset.refl _, fun _ hj _ => hj⟩

private theorem chr_getLoop_miss (F : ShaCompress) (seed : Bytes) (self : KeyHistory)
    (L : List ℕ) (hdata : self.data = chr_data F seed L) (atIdx : BitVec 32)
    (hmiss : ∀ j ∈ L, toBEBytes 4 (BitVec.ofNat 32 j) ≠ toBEBytes 4 atIdx) :
    ∀ (n k : ℕ), L.length - k = n →
      KeyHistory.getLoop self atIdx (toBEBytes 4 atIdx) dparams (36 * k) =
        .error (.err (.keyAlreadyRequested atIdx))
  | 0, k, hn => by
    have hnotlt : ¬ (36 * k < self.data.length) := by rw [hdata, chr_data_length]; omega
    rw [KeyHistory.getLoop]
    simp [hnotlt]
  | n + 1, k, hn => by
    have hk : k < L.length := by omega
    have hlt : 36 * k < self.data.length := by rw [hdata, chr_data_length]; omega
    have htake4 : (self.data.drop (36 * k)).take 4 = toBEBytes 4 (BitVec.ofNat 32 L[k]) := by
      rw [hdata, chr_data_drop_take4 F seed L k hk]
    have hne : ((self.data.drop (36 * k)).take 4 == toBEBytes 4 atIdx) = false := by
      rw [htake4, beq_eq_false_iff_ne]
      exact hmiss L[k] (List.getElem_mem hk)
    rw [KeyHistory.getLoop]
    simp only [hlt, ↓reduceDIte, hne, Bool.false_eq_true, ↓reduceIte]
    have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
      simp only [KeyHistory.KEY_SIZE]; omega
    rw [hstep]
    exact chr_getLoop_miss F seed self L hdata atIdx hmiss n (k + 1) (by omega)

private theorem chr_sup_id_mem_of_pos (R : Finset ℕ) (h : 0 < R.sup id) : R.sup id ∈ R := by
  induction R using Finset.induction_on with
  | empty => simp at h
  | @insert a s _ ih =>
    rw [Finset.sup_insert]
    change max a (s.sup id) ∈ insert a s
    by_cases hle : s.sup id ≤ a
    · rw [Nat.max_eq_left hle]; exact Finset.mem_insert_self a s
    · rw [Nat.max_eq_right (by omega)]
      exact Finset.mem_insert_of_mem (ih (by omega))

private theorem chr_le_sup_id {R : Finset ℕ} {x : ℕ} (hx : x ∈ R) : x ≤ R.sup id :=
  Finset.le_sup (f := id) hx

private theorem chr_sup_insert_id (idx : ℕ) (R : Finset ℕ) :
    (insert idx R).sup id = max idx (R.sup id) :=
  Finset.sup_insert

private theorem chr_nextKeyInternal_step (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32)
    (n : ℕ) (ctr : BitVec 32) (hctr : ctr.toNat = n) (hn : n + 1 < 2 ^ 32) :
    ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) (nextAt F seed n) ctr =
      .ok (nextAt F seed (n + 1), BitVec.ofNat 32 (n + 1),
        (BitVec.ofNat 32 (n + 1), keyAt F seed n)) := by
  unfold ChainEpochDirection.nextKeyInternal
  have hlen : ((nextAt F seed n).length != 32) = false := by
    rw [length_nextAt F seed hseed n]; decide
  have hne : (ctr == 0xffffffff#32) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have : ctr.toNat = 4294967295 := by rw [heq]; rfl
    omega
  have hadd : ctr + 1#32 = BitVec.ofNat 32 (n + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hctr, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [hlen, Bool.false_eq_true, ↓reduceIte, hne, hadd]
  rfl

/-- `ChainEpochDirection.key` on an honest receive direction returns `keyAt F seed (idx - 1)`
for any fresh in-window index `idx` (`idx ∉ R`, jump `≤ 25000`, not trimmed) and preserves
`RecvDirOk` on `insert idx R`. -/
theorem recvDir_key (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32) (R : Finset ℕ)
    (d : ChainEpochDirection) (h : RecvDirOk F seed R d) (idx : ℕ) (hidx : 1 ≤ idx)
    (hnew : idx ∉ R) (hjump : R.sup id < idx → idx - R.sup id ≤ 25000)
    (htrim : idx < R.sup id → R.sup id ≤ idx + 2000) (hb : idx + 2000 ≤ 2 ^ 32)
    (hR : R.sup id + 2000 ≤ 2 ^ 32) :
    ∃ d', d.key (spqrHkdfWith F) (BitVec.ofNat 32 idx) dparams = .ok (d', keyAt F seed (idx - 1)) ∧
      RecvDirOk F seed (insert idx R) d' := by
  have hctr_eq : d.ctr.toNat = R.sup id := h.hctr
  have hidx32 : idx < 2 ^ 32 := by omega
  have hatVal : (BitVec.ofNat 32 idx).toNat = idx := Nat.mod_eq_of_lt hidx32
  have hne_ctr : idx ≠ d.ctr.toNat := by
    intro heq
    have hmem : R.sup id ∈ R := chr_sup_id_mem_of_pos R (by omega)
    rw [← hctr_eq, ← heq] at hmem
    exact hnew hmem
  rcases h.hprev with ⟨S, hS, hS_props, hS_comp⟩
  by_cases hlt_ctr : idx < d.ctr.toNat
  · have hat_lt : BitVec.ofNat 32 idx < d.ctr := by
      change (BitVec.ofNat 32 idx).toNat < d.ctr.toNat
      omega
    have hidx_S : idx ∈ S :=
      hS_comp idx hidx hlt_ctr hnew (by rw [hctr_eq]; exact htrim (by omega))
    have hS32 : ∀ i ∈ S, i < 2 ^ 32 := fun i hi =>
      Nat.lt_trans (hS_props i hi).2.1 d.ctr.isLt
    rcases histRepr_get F seed S d.prev hS hS32 idx hidx_S d.ctr (by omega)
        (by rw [hctr_eq]; exact htrim (by omega)) with
      ⟨prev', hget, hRepr'⟩
    refine ⟨{ d with prev := prev' }, ?_, ?_⟩
    · unfold ChainEpochDirection.key
      simp only [hat_lt, ↓reduceIte, hget]
      rfl
    · refine ⟨?_, ?_, h.hnext, ⟨S.erase idx, hRepr', ?_, ?_⟩⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjR
        · exact hidx
        · exact h.hpos j hjR
      · rw [chr_sup_insert_id, ← hctr_eq, Nat.max_eq_right (by omega)]
      · intro j hj
        rcases Finset.mem_erase.mp hj with ⟨hne, hjS⟩
        rcases hS_props j hjS with ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun hjIns => (Finset.mem_insert.mp hjIns).elim hne h3⟩
      · intro j h1 h2 hjNotIns hwin
        rw [Finset.mem_erase]
        refine ⟨fun heq => hjNotIns (heq ▸ Finset.mem_insert_self idx R), ?_⟩
        exact hS_comp j h1 h2 (fun hjR => hjNotIns (Finset.mem_insert_of_mem hjR)) hwin
  · have hgt_ctr : d.ctr.toNat < idx := by omega
    have hnot_lt : ¬ (BitVec.ofNat 32 idx < d.ctr) := by
      change ¬ ((BitVec.ofNat 32 idx).toNat < d.ctr.toNat); omega
    have hnot_eq : (BitVec.ofNat 32 idx == d.ctr) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      have := congrArg BitVec.toNat heq
      omega
    have hnot_jump : ¬ (BitVec.ofNat 32 idx - d.ctr > dparams.maxJumpOrDefault) := by
      rw [dparams_maxJump]
      change ¬ (25000 < (BitVec.ofNat 32 idx - d.ctr).toNat)
      rw [BitVec.toNat_sub_of_le (by change d.ctr.toNat ≤ (BitVec.ofNat 32 idx).toNat; omega)]
      have hj := hjump (by omega)
      omega
    have hnot_ovf : ¬ (d.ctr.toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) := by
      rw [dparams_maxOoo]
      change ¬ (d.ctr.toNat + 2000 ≥ 2 ^ 32)
      omega
    let maxOoo := dparams.maxOooKeysOrDefault
    let self0 : ChainEpochDirection :=
      if BitVec.ofNat 32 idx > d.ctr + maxOoo then { d with prev := d.prev.clear } else d
    let S0 : Finset ℕ :=
      if BitVec.ofNat 32 idx > d.ctr + maxOoo then ∅ else S
    have hself0_ctr : self0.ctr = d.ctr := by dsimp [self0]; split_ifs <;> rfl
    have hself0_next : self0.next = d.next := by dsimp [self0]; split_ifs <;> rfl
    have hS0_repr : HistRepr F seed S0 self0.prev := by
      dsimp [self0, S0]
      split_ifs
      · exact histRepr_empty F seed
      · exact hS
    have hS0_props : ∀ j ∈ S0, 1 ≤ j ∧ j < d.ctr.toNat ∧ j ∉ R := by
      intro j hj
      dsimp [S0] at hj
      split_ifs at hj
      · simp at hj
      · exact hS_props j hj
    have hS0_comp : ∀ j, 1 ≤ j → j < d.ctr.toNat → j ∉ R → idx ≤ j + 2000 → j ∈ S0 := by
      intro j h1 h2 h3 hwin
      dsimp [S0]
      split_ifs with hclr
      · have hclr' : (d.ctr + maxOoo).toNat < (BitVec.ofNat 32 idx).toNat := hclr
        have haddOoo : (d.ctr + maxOoo).toNat = d.ctr.toNat + 2000 := by
          change (d.ctr + dparams.maxOooKeysOrDefault).toNat = d.ctr.toNat + 2000
          rw [dparams_maxOoo, BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        omega
      · exact hS_comp j h1 h2 h3 (by omega)
    rcases keyAdvanceLoop_ok F seed hseed self0 S0 hS0_repr
        (fun i hi => by rw [hself0_ctr]; exact Nat.le_of_lt (hS0_props i hi).2.1)
        (by rw [hself0_next, hself0_ctr, h.hnext]) idx
        (by rw [hself0_ctr]; exact hgt_ctr) hb with
      ⟨self1, hloop, hself1_ctr, hself1_next, hS1_repr⟩
    rw [hself0_ctr] at hS1_repr
    let S1 : Finset ℕ := S0 ∪ (Finset.Ioo d.ctr.toNat idx).filter fun j => idx ≤ j + 2000
    have hS1_le : ∀ i ∈ S1, 1 ≤ i ∧ i ≤ self1.ctr.toNat := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi0 | hiF
      · have hp := hS0_props i hi0
        exact ⟨hp.1, by omega⟩
      · rw [Finset.mem_filter, Finset.mem_Ioo] at hiF
        omega
    rcases chr_histRepr_gc F seed S1 self1.prev hS1_repr self1.ctr hS1_le with
      ⟨prevGc, S', hgc, hS'_repr, hS'_sub, hS'_comp⟩
    have hnk := chr_nextKeyInternal_step F seed hseed (idx - 1) self1.ctr hself1_ctr (by omega)
    have hidx_sub : idx - 1 + 1 = idx := by omega
    rw [hidx_sub] at hnk
    let d' : ChainEpochDirection :=
      { self1 with prev := prevGc, next := nextAt F seed idx, ctr := BitVec.ofNat 32 idx }
    refine ⟨d', ?_, ?_⟩
    · unfold ChainEpochDirection.key
      simp only [hnot_lt, ↓reduceIte, hnot_eq, Bool.false_eq_true, hnot_jump, hnot_ovf]
      change (do
        let self1 ← self0.keyAdvanceLoop (spqrHkdfWith F) (BitVec.ofNat 32 idx) dparams
        let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr dparams)
        let self2 : ChainEpochDirection := { self1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ←
          ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) self2.next self2.ctr)
        return ({ self2 with next := next', ctr := ctr' }, outKey)) =
        .ok (d', keyAt F seed (idx - 1))
      rw [hloop]
      simp only [bind, Except.bind, hgc, ChainResult.ofPanic, hself1_next, hnk]
      rfl
    · refine ⟨?_, ?_, ?_, ⟨S', hS'_repr, ?_, ?_⟩⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjR
        · exact hidx
        · exact h.hpos j hjR
      · dsimp [d']
        rw [hatVal, chr_sup_insert_id, ← hctr_eq, Nat.max_eq_left (by omega)]
      · dsimp [d']
        rw [hatVal]
      · intro j hj'
        have hj1 : j ∈ S1 := hS'_sub hj'
        dsimp [d']
        rw [hatVal]
        rcases Finset.mem_union.mp hj1 with hj0 | hjF
        · rcases hS0_props j hj0 with ⟨h1, h2, h3⟩
          refine ⟨h1, by omega, fun hjIns => ?_⟩
          rcases Finset.mem_insert.mp hjIns with rfl | hjR
          · omega
          · exact h3 hjR
        · rw [Finset.mem_filter, Finset.mem_Ioo] at hjF
          refine ⟨by omega, hjF.1.2, fun hjIns => ?_⟩
          rcases Finset.mem_insert.mp hjIns with rfl | hjR
          · omega
          · have := chr_le_sup_id hjR
            omega
      · intro j h1 h2 hjNotIns hwin
        dsimp [d'] at h2 hwin
        rw [hatVal] at h2 hwin
        have hjNotR : j ∉ R := fun hjR => hjNotIns (Finset.mem_insert_of_mem hjR)
        have hj_ne_ctr : j ≠ d.ctr.toNat := by
          intro heq
          have hmem : R.sup id ∈ R := chr_sup_id_mem_of_pos R (by omega)
          rw [← hctr_eq, ← heq] at hmem
          exact hjNotR hmem
        have hj1 : j ∈ S1 := by
          rw [Finset.mem_union]
          by_cases hj_lt : j < d.ctr.toNat
          · exact Or.inl (hS0_comp j h1 hj_lt hjNotR hwin)
          · right
            rw [Finset.mem_filter, Finset.mem_Ioo]
            exact ⟨⟨by omega, h2⟩, hwin⟩
        exact hS'_comp j hj1 (by omega)

/-- `ChainEpochDirection.key` rejects any index `idx < 2 ^ 32` that is already in `R`, jumps
ahead by more than `25000`, or falls below the `2000`-key window. -/
theorem recvDir_key_err (F : ShaCompress) (seed : Bytes) (R : Finset ℕ) (d : ChainEpochDirection)
    (h : RecvDirOk F seed R d) (idx : ℕ) (hidx32 : idx < 2 ^ 32)
    (hout : idx ∈ R ∨ (R.sup id < idx ∧ 25000 < idx - R.sup id) ∨
      (idx < R.sup id ∧ idx + 2000 < R.sup id)) :
    ∀ r, d.key (spqrHkdfWith F) (BitVec.ofNat 32 idx) dparams ≠ .ok r := by
  intro r
  have hctr_eq : d.ctr.toNat = R.sup id := h.hctr
  have hatVal : (BitVec.ofNat 32 idx).toNat = idx := Nat.mod_eq_of_lt hidx32
  by_cases hlt_ctr : idx < d.ctr.toNat
  · have hat_lt : BitVec.ofNat 32 idx < d.ctr := by
      change (BitVec.ofNat 32 idx).toNat < d.ctr.toNat; omega
    unfold ChainEpochDirection.key
    simp only [hat_lt, ↓reduceIte]
    suffices hget_err : ∀ p, d.prev.get (BitVec.ofNat 32 idx) d.ctr dparams ≠ .ok p by
      intro hok
      cases hget : d.prev.get (BitVec.ofNat 32 idx) d.ctr dparams with
      | error e =>
        rw [hget] at hok
        contradiction
      | ok p => exact hget_err p hget
    intro p
    dsimp only [KeyHistory.get]
    split_ifs with halign hovf htrim
    · simp
    · simp
    · simp
    · have hnot_trim : d.ctr.toNat ≤ idx + 2000 := by
        rw [dparams_maxOoo, hatVal] at hovf
        change ¬ (idx + 2000 ≥ 2 ^ 32) at hovf
        rw [dparams_maxOoo] at htrim
        change ¬ ((BitVec.ofNat 32 idx + 2000#32).toNat < d.ctr.toNat) at htrim
        rw [BitVec.toNat_add, hatVal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at htrim
        omega
      have hidx_R : idx ∈ R := by
        rcases hout with hR | ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hR
        · omega
        · omega
      rcases h.hprev with ⟨S, ⟨L, _, hFin, hdata⟩, hS_props, _⟩
      have hmiss : ∀ j ∈ L,
          toBEBytes 4 (BitVec.ofNat 32 j) ≠ toBEBytes 4 (BitVec.ofNat 32 idx) := by
        intro j hjL heq
        have hjS : j ∈ S := by rw [← hFin]; exact List.mem_toFinset.mpr hjL
        rcases hS_props j hjS with ⟨_, hj_lt, hj_notR⟩
        have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt d.ctr.isLt
        have hbvEq := toBEBytes4_injective heq
        have hnatEq : (BitVec.ofNat 32 j).toNat = (BitVec.ofNat 32 idx).toNat :=
          congrArg BitVec.toNat hbvEq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32, hatVal] at hnatEq
        exact hj_notR (hnatEq ▸ hidx_R)
      have hloop := chr_getLoop_miss F seed d.prev L hdata (BitVec.ofNat 32 idx) hmiss
        L.length 0 (Nat.sub_zero _)
      change KeyHistory.getLoop d.prev (BitVec.ofNat 32 idx) (toBEBytes 4 (BitVec.ofNat 32 idx))
        dparams (36 * 0) ≠ .ok p
      rw [hloop]
      rintro ⟨⟩
  · by_cases heq_ctr : idx = d.ctr.toNat
    · have hat_not_lt : ¬ (BitVec.ofNat 32 idx < d.ctr) := by
        change ¬ ((BitVec.ofNat 32 idx).toNat < d.ctr.toNat); omega
      have hat_eq : (BitVec.ofNat 32 idx == d.ctr) = true := by
        rw [beq_iff_eq]
        apply BitVec.eq_of_toNat_eq
        omega
      unfold ChainEpochDirection.key
      simp [hat_not_lt, hat_eq]
    · have hgt_ctr : d.ctr.toNat < idx := by omega
      have hat_not_lt : ¬ (BitVec.ofNat 32 idx < d.ctr) := by
        change ¬ ((BitVec.ofNat 32 idx).toNat < d.ctr.toNat); omega
      have hat_not_eq : (BitVec.ofNat 32 idx == d.ctr) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        have := congrArg BitVec.toNat heq
        omega
      have hjump_gt : 25000 < idx - R.sup id := by
        rcases hout with hR | ⟨_, h2⟩ | ⟨h1, _⟩
        · have := chr_le_sup_id hR
          omega
        · exact h2
        · omega
      have hat_jump : BitVec.ofNat 32 idx - d.ctr > dparams.maxJumpOrDefault := by
        rw [dparams_maxJump]
        change 25000 < (BitVec.ofNat 32 idx - d.ctr).toNat
        rw [BitVec.toNat_sub_of_le (by change d.ctr.toNat ≤ (BitVec.ofNat 32 idx).toNat; omega)]
        omega
      unfold ChainEpochDirection.key
      simp [hat_not_lt, hat_not_eq, hat_jump]

/-! ## The chain -/

/-- `Chain.new` establishes `ChainOk` at chain epoch `0` with empty send and receive counters. -/
theorem chainNew_ok (F : ShaCompress) (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes)
    (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (hs : ∀ e, 0 < e → sendCtr e = 0)
    (hr : ∀ e, 0 < e → recvSet e = ∅) (hs0 : sendCtr 0 = 0) (hr0 : recvSet 0 = ∅) :
    ∃ ch, Chain.new (spqrHkdfWith F) authKey dir dparams = .ok ch ∧
      ChainOk F authKey dir secret sendCtr recvSet ch := by
  let genr8r := genAt F authKey secret 0
  let epoch0 : ChainEpoch :=
    { send := Chain.cedForDirection genr8r dir
      recv := Chain.cedForDirection genr8r dir.switch }
  refine ⟨{ dir := dir, currentEpoch := 0#64, sendEpoch := 0#64,
            links := [epoch0], nextRoot := genr8r.take 32, params := dparams }, rfl, ?_⟩
  refine
    { hdir := rfl
      hparams := rfl
      hsend_le := le_rfl
      hroot := rfl
      hlen := rfl
      hsendDir := ?_
      hsendOld := ?_
      hrecvDir := ?_
      hfreshSend := fun e he => hs e he
      hfreshRecv := fun e he => hr e he }
  · intro e _ he
    have he0 : e = 0 := by
      change e ≤ 0 at he
      omega
    subst he0
    refine ⟨epoch0, rfl, ?_⟩
    rw [hs0]
    change SendDirOk F (seedAt F authKey secret dir 0) 0 (Chain.cedForDirection genr8r dir)
    rw [cedForDirection_eq]
    exact sendDirOk_new F (seedAt F authKey secret dir 0)
  · intro l h1 _
    change 1 ≤ 0 at h1
    omega
  · intro e _ he
    have he0 : e = 0 := by
      change e ≤ 0 at he
      omega
    subst he0
    refine ⟨epoch0, rfl, ?_⟩
    rw [hr0]
    change RecvDirOk F (seedAt F authKey secret dir.switch 0) ∅
      (Chain.cedForDirection genr8r dir.switch)
    rw [cedForDirection_eq]
    exact recvDirOk_new F (seedAt F authKey secret dir.switch 0)

/-- `chainFromVersionNegotiation` on `ChainParams.default` establishes `ChainOk` at epoch `0`. -/
theorem chainFromVN_ok (F : ShaCompress) (authKey : Bytes) (dir : Direction) (minVersion : BitVec 32)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (hs : ∀ e, sendCtr e = 0) (hr : ∀ e, recvSet e = ∅) :
    ∃ ch, chainFromVersionNegotiation (spqrHkdfWith F)
        { authKey := authKey, direction := dir.toI32, minVersion := minVersion,
          chainParams := some dparams } = .ok ch ∧
      ChainOk F authKey dir secret sendCtr recvSet ch := by
  have hdir : Direction.fromI32? dir.toI32 = some dir := by cases dir <;> rfl
  unfold chainFromVersionNegotiation
  simp only [hdir]
  exact chainNew_ok F authKey dir secret sendCtr recvSet (fun e _ => hs e) (fun e _ => hr e)
    (hs 0) (hr 0)

/-- `Chain.addEpoch` with the next epoch secret `secret (cur + 1)` advances `currentEpoch` to
`cur + 1` and preserves `ChainOk`. -/
theorem addEpoch_ok (F : ShaCompress) (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes)
    (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (es : EpochSecret)
    (hep : es.epoch.toNat = ch.currentEpoch.toNat + 1)
    (hsec : es.secret = secret (ch.currentEpoch.toNat + 1)) :
    ∃ ch', ch.addEpoch (spqrHkdfWith F) es = .ok ch' ∧ ch'.currentEpoch = es.epoch ∧
      ch'.sendEpoch = ch.sendEpoch ∧ ChainOk F authKey dir secret sendCtr recvSet ch' := by
  have hes_lt : es.epoch.toNat < 2 ^ 64 := es.epoch.isLt
  have hcur_ne : (ch.currentEpoch == 0xffffffffffffffff#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have hval : ch.currentEpoch.toNat = 18446744073709551615 := by rw [heq]; rfl
    omega
  have hes_eq : es.epoch = ch.currentEpoch + 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hes_bne : (es.epoch != ch.currentEpoch + 1#64) = false := by
    simp [hes_eq]
  let genr8r := spqrHkdfWith F ch.nextRoot es.secret chainAddEpochInfo 96
  have hgen : genr8r = genAt F authKey secret (ch.currentEpoch.toNat + 1) := by
    change spqrHkdfWith F ch.nextRoot es.secret chainAddEpochInfo 96 = _
    rw [h.hroot, hsec, genAt]
  let newLink : ChainEpoch :=
    { send := Chain.cedForDirection genr8r ch.dir
      recv := Chain.cedForDirection genr8r ch.dir.switch }
  let ch' : Chain :=
    { ch with
      currentEpoch := es.epoch
      nextRoot := genr8r.take 32
      links := ch.links ++ [newLink] }
  refine ⟨ch', ?_, rfl, rfl, ?_⟩
  · unfold Chain.addEpoch
    simp only [hcur_ne, hes_bne, Bool.false_eq_true, ↓reduceIte]
    rfl
  · have hsend_le := h.hsend_le
    have hlen := h.hlen
    refine
      { hdir := h.hdir
        hparams := h.hparams
        hsend_le := by change ch.sendEpoch.toNat ≤ es.epoch.toNat; omega
        hroot := by
          change genr8r.take 32 = (genAt F authKey secret es.epoch.toNat).take 32
          rw [hep, hgen]
        hlen := by
          change (ch.links ++ [newLink]).length = es.epoch.toNat - (ch.sendEpoch.toNat - 1) + 1
          rw [List.length_append, List.length_singleton, hlen]
          omega
        hsendDir := ?_
        hsendOld := ?_
        hrecvDir := ?_
        hfreshSend := fun e he => h.hfreshSend e (by change es.epoch.toNat < e at he; omega)
        hfreshRecv := fun e he => h.hfreshRecv e (by change es.epoch.toNat < e at he; omega) }
    · intro e hlo hhi
      change ch.sendEpoch.toNat ≤ e at hlo
      change e ≤ es.epoch.toNat at hhi
      by_cases he : e ≤ ch.currentEpoch.toNat
      · have hidx_lt : e - (ch.sendEpoch.toNat - 1) < ch.links.length := by omega
        change ∃ l, (ch.links ++ [newLink])[e - (ch.sendEpoch.toNat - 1)]? = some l ∧
          SendDirOk F (seedAt F authKey secret dir e) (sendCtr e) l.send
        rw [List.getElem?_append_left hidx_lt]
        exact h.hsendDir e hlo he
      · have he_eq : e = ch.currentEpoch.toNat + 1 := by omega
        have hidx_eq : e - (ch.sendEpoch.toNat - 1) = ch.links.length := by omega
        change ∃ l, (ch.links ++ [newLink])[e - (ch.sendEpoch.toNat - 1)]? = some l ∧
          SendDirOk F (seedAt F authKey secret dir e) (sendCtr e) l.send
        rw [hidx_eq, List.getElem?_append_right le_rfl, Nat.sub_self]
        refine ⟨newLink, rfl, ?_⟩
        have hsc : sendCtr e = 0 := h.hfreshSend e (by omega)
        rw [hsc]
        change SendDirOk F (seedAt F authKey secret dir e) 0 (Chain.cedForDirection genr8r ch.dir)
        rw [h.hdir, cedForDirection_eq, hgen, ← he_eq]
        exact sendDirOk_new F (seedAt F authKey secret dir e)
    · intro l h1 h0
      change 1 ≤ ch.sendEpoch.toNat at h1
      change (ch.links ++ [newLink])[0]? = some l at h0
      have h0_lt : 0 < ch.links.length := by omega
      rw [List.getElem?_append_left h0_lt] at h0
      exact h.hsendOld l h1 h0
    · intro e hlo hhi
      change ch.sendEpoch.toNat - 1 ≤ e at hlo
      change e ≤ es.epoch.toNat at hhi
      by_cases he : e ≤ ch.currentEpoch.toNat
      · have hidx_lt : e - (ch.sendEpoch.toNat - 1) < ch.links.length := by omega
        change ∃ l, (ch.links ++ [newLink])[e - (ch.sendEpoch.toNat - 1)]? = some l ∧
          RecvDirOk F (seedAt F authKey secret dir.switch e) (recvSet e) l.recv
        rw [List.getElem?_append_left hidx_lt]
        exact h.hrecvDir e hlo he
      · have he_eq : e = ch.currentEpoch.toNat + 1 := by omega
        have hidx_eq : e - (ch.sendEpoch.toNat - 1) = ch.links.length := by omega
        change ∃ l, (ch.links ++ [newLink])[e - (ch.sendEpoch.toNat - 1)]? = some l ∧
          RecvDirOk F (seedAt F authKey secret dir.switch e) (recvSet e) l.recv
        rw [hidx_eq, List.getElem?_append_right le_rfl, Nat.sub_self]
        refine ⟨newLink, rfl, ?_⟩
        have hrs : recvSet e = ∅ := h.hfreshRecv e (by omega)
        rw [hrs]
        change RecvDirOk F (seedAt F authKey secret dir.switch e) ∅
          (Chain.cedForDirection genr8r ch.dir.switch)
        rw [h.hdir, cedForDirection_eq, hgen, ← he_eq]
        exact recvDirOk_new F (seedAt F authKey secret dir.switch e)

theorem chs_epochIdx_eq (ch : Chain) (e : Epoch)
    (hlen : ch.links.length = ch.currentEpoch.toNat - (ch.sendEpoch.toNat - 1) + 1)
    (hlo : ch.sendEpoch.toNat - 1 ≤ e.toNat) (hhi : e.toNat ≤ ch.currentEpoch.toNat) :
    ch.epochIdx e = .ok (e.toNat - (ch.sendEpoch.toNat - 1)) := by
  unfold Chain.epochIdx
  have hgt : ¬(e > ch.currentEpoch) := by
    simp only [gt_iff_lt, BitVec.lt_def, not_lt]
    exact hhi
  have hback : (ch.currentEpoch - e).toNat = ch.currentEpoch.toNat - e.toNat :=
    BitVec.toNat_sub_of_le hhi
  have hge : ¬((ch.currentEpoch - e).toNat ≥ ch.links.length) := by
    omega
  simp only [hgt, ↓reduceIte, hge]
  congr 1
  omega

private theorem chs_clearSendNextPrefix_one_length (xs : List ChainEpoch) :
    (Chain.clearSendNextPrefix 1 xs).length = xs.length := by
  cases xs <;> rfl

private theorem chs_clearSendNextPrefix_one_zero (xs : List ChainEpoch) :
    (Chain.clearSendNextPrefix 1 xs)[0]? =
      xs[0]?.map (fun x => { x with send := x.send.clearNext }) := by
  cases xs <;> rfl

private theorem chs_clearSendNextPrefix_one_succ (xs : List ChainEpoch) (i : ℕ) :
    (Chain.clearSendNextPrefix 1 xs)[i + 1]? = xs[i + 1]? := by
  cases xs <;> rfl

private theorem chs_clearSendNextPrefix_one_recv (xs : List ChainEpoch) (i : ℕ)
    (l : ChainEpoch) (h : xs[i]? = some l) :
    ∃ l', (Chain.clearSendNextPrefix 1 xs)[i]? = some l' ∧ l'.recv = l.recv := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨{ x with send := x.send.clearNext }, rfl, rfl⟩
    | succ j =>
      exact ⟨l, h, rfl⟩

theorem chs_advance_sendEpoch_ok (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (e : Epoch)
    (hlt : ch.sendEpoch.toNat < e.toNat) (hhi : e.toNat ≤ ch.currentEpoch.toNat) :
    let epochIndex0 := e.toNat - (ch.sendEpoch.toNat - 1)
    let dropCount := epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
    let epochIndex' := epochIndex0 - dropCount
    ChainOk F authKey dir secret sendCtr recvSet
      { ch with sendEpoch := e,
                links := Chain.clearSendNextPrefix epochIndex' (ch.links.drop dropCount) } := by
  intro epochIndex0 dropCount epochIndex'
  have hidx' : epochIndex' = 1 := by
    dsimp [epochIndex', dropCount, epochIndex0, EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH]
    omega
  refine
    { hdir := h.hdir
      hparams := h.hparams
      hsend_le := hhi
      hroot := h.hroot
      hlen := ?_
      hsendDir := ?_
      hsendOld := ?_
      hrecvDir := ?_
      hfreshSend := h.hfreshSend
      hfreshRecv := h.hfreshRecv }
  · dsimp only
    rw [hidx', chs_clearSendNextPrefix_one_length, List.length_drop, h.hlen]
    dsimp [dropCount, epochIndex0, EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH]
    omega
  · intro e' hlo' hhi'
    dsimp only at hlo' hhi' ⊢
    have hpos : e' - (e.toNat - 1) = (e' - e.toNat) + 1 := by omega
    rw [hidx', hpos, chs_clearSendNextPrefix_one_succ, List.getElem?_drop]
    have hshift : dropCount + (e' - e.toNat + 1) = e' - (ch.sendEpoch.toNat - 1) := by
      dsimp [dropCount, epochIndex0, EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH]
      omega
    rw [hshift]
    exact h.hsendDir e' (by omega) hhi'
  · intro l _hl1 hl0
    dsimp only at hl0
    rw [hidx', chs_clearSendNextPrefix_one_zero] at hl0
    rcases Option.mem_map.mp hl0 with ⟨x, _, rfl⟩
    rfl
  · intro e' hlo' hhi'
    dsimp only at hlo' hhi' ⊢
    rw [hidx']
    have hshift : dropCount + (e' - (e.toNat - 1)) = e' - (ch.sendEpoch.toNat - 1) := by
      dsimp [dropCount, epochIndex0, EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH]
      omega
    rcases h.hrecvDir e' (by omega) hhi' with ⟨l, hl, hrecv⟩
    have hdrop : (ch.links.drop dropCount)[e' - (e.toNat - 1)]? = some l := by
      rw [List.getElem?_drop, hshift, hl]
    rcases chs_clearSendNextPrefix_one_recv (ch.links.drop dropCount)
        (e' - (e.toNat - 1)) l hdrop with ⟨l', hl', hrecv_eq⟩
    exact ⟨l', hl', hrecv_eq ▸ hrecv⟩

private theorem chs_sendKey_at_sendEpoch (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch1 : Chain)
    (h1 : ChainOk F authKey dir secret sendCtr recvSet ch1) (e : Epoch)
    (he : ch1.sendEpoch = e) (hhi : e.toNat ≤ ch1.currentEpoch.toNat)
    (hn : sendCtr e.toNat + 1 < 2 ^ 32)
    (epochIndex : ℕ) (hidx : epochIndex = e.toNat - (e.toNat - 1)) :
    ∃ ch',
      ((match ch1.links[epochIndex]? with
        | none => .error (.panic .linksOutOfBounds)
        | some link => do
          let (send', out) ← ChainResult.ofPanic (link.send.nextKey (spqrHkdfWith F))
          let links' := ch1.links.set epochIndex { link with send := send' }
          return ({ ch1 with links := links' }, out)) :
          ChainResult (Chain × (BitVec 32 × Bytes))) =
        .ok (ch', (BitVec.ofNat 32 (sendCtr e.toNat + 1),
          keyAt F (seedAt F authKey secret dir e.toNat) (sendCtr e.toNat))) ∧
      ch'.currentEpoch = ch1.currentEpoch ∧ ch'.sendEpoch = e ∧
      ChainOk F authKey dir secret (Function.update sendCtr e.toNat (sendCtr e.toNat + 1))
        recvSet ch' := by
  have he_lo : ch1.sendEpoch.toNat ≤ e.toNat := by rw [he]
  rcases h1.hsendDir e.toNat he_lo hhi with ⟨link, hlink, hsendOk⟩
  have hidx_eq : epochIndex = e.toNat - (ch1.sendEpoch.toNat - 1) := by rw [he, hidx]
  rw [← hidx_eq] at hlink
  have hlt_len : epochIndex < ch1.links.length := (List.getElem?_eq_some_iff.mp hlink).1
  have hnk := sendDir_nextKey F (seedAt F authKey secret dir e.toNat)
    (length_seedAt F authKey secret dir e.toNat) (sendCtr e.toNat) link.send hsendOk hn
  have hsend' := sendDir_nextKey_ok F (seedAt F authKey secret dir e.toNat)
    (sendCtr e.toNat) link.send hn
  let send' : ChainEpochDirection :=
    { link.send with
      next := nextAt F (seedAt F authKey secret dir e.toNat) (sendCtr e.toNat + 1)
      ctr := BitVec.ofNat 32 (sendCtr e.toNat + 1) }
  refine ⟨{ ch1 with links := ch1.links.set epochIndex { link with send := send' } },
    ?_, rfl, he, ?_⟩
  · rw [hlink]; dsimp only; rw [hnk]; rfl
  · refine
      { hdir := h1.hdir
        hparams := h1.hparams
        hsend_le := h1.hsend_le
        hroot := h1.hroot
        hlen := by dsimp only; rw [List.length_set, h1.hlen]
        hsendDir := ?_
        hsendOld := ?_
        hrecvDir := ?_
        hfreshSend := ?_
        hfreshRecv := h1.hfreshRecv }
    · intro e' hlo' hhi'
      dsimp only at hlo' hhi' ⊢
      by_cases he' : e' = e.toNat
      · subst he'
        rw [← hidx_eq, List.getElem?_set_self hlt_len, Function.update_self]
        exact ⟨{ link with send := send' }, rfl, hsend'⟩
      · have hne_idx : epochIndex ≠ e' - (ch1.sendEpoch.toNat - 1) := by
          rw [he] at hlo'
          omega
        rw [List.getElem?_set_ne hne_idx, Function.update_of_ne he']
        exact h1.hsendDir e' hlo' hhi'
    · intro l0 hl1 hl0
      dsimp only at hl1 hl0
      have hne0 : epochIndex ≠ 0 := by
        rw [he] at hl1
        omega
      rw [List.getElem?_set_ne hne0] at hl0
      exact h1.hsendOld l0 hl1 hl0
    · intro e' hlo' hhi'
      dsimp only at hlo' hhi' ⊢
      by_cases hidx_e' : epochIndex = e' - (ch1.sendEpoch.toNat - 1)
      · rcases h1.hrecvDir e' hlo' hhi' with ⟨l, hl, hrecv⟩
        rw [← hidx_e', hlink] at hl
        injection hl with hl_eq
        subst hl_eq
        rw [← hidx_e', List.getElem?_set_self hlt_len]
        exact ⟨{ link with send := send' }, rfl, hrecv⟩
      · rw [List.getElem?_set_ne hidx_e']
        exact h1.hrecvDir e' hlo' hhi'
    · intro e' hgt'
      dsimp only at hgt'
      have hne' : e' ≠ e.toNat := by omega
      rw [Function.update_of_ne hne']
      exact h1.hfreshSend e' hgt'

/-- `Chain.sendKey` at epoch `e ∈ [sendEpoch, currentEpoch]` derives the next message key
`keyAt F (seedAt … e) (sendCtr e)` and preserves `ChainOk` with `sendEpoch := e`. -/
theorem sendKey_ok (F : ShaCompress) (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes)
    (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (e : Epoch)
    (hlo : ch.sendEpoch.toNat ≤ e.toNat) (hhi : e.toNat ≤ ch.currentEpoch.toNat)
    (hn : sendCtr e.toNat + 1 < 2 ^ 32) :
    ∃ ch', ch.sendKey (spqrHkdfWith F) e =
        .ok (ch', (BitVec.ofNat 32 (sendCtr e.toNat + 1),
          keyAt F (seedAt F authKey secret dir e.toNat) (sendCtr e.toNat))) ∧
      ch'.currentEpoch = ch.currentEpoch ∧ ch'.sendEpoch = e ∧
      ChainOk F authKey dir secret (Function.update sendCtr e.toNat (sendCtr e.toNat + 1))
        recvSet ch' := by
  have hlt_false : ¬(e < ch.sendEpoch) := by
    simp only [BitVec.lt_def, not_lt]
    exact hlo
  have hepIdx := chs_epochIdx_eq ch e h.hlen (by omega) hhi
  unfold Chain.sendKey
  simp only [hlt_false, ↓reduceIte, hepIdx, ChainResult.ofError, bind, Except.bind]
  by_cases hne : (ch.sendEpoch != e) = true
  · simp only [hne, ↓reduceIte]
    have hlt : ch.sendEpoch.toNat < e.toNat := by
      have hne' : ch.sendEpoch ≠ e := by simpa [bne_iff_ne] using hne
      have : ch.sendEpoch.toNat ≠ e.toNat := fun heq => hne' (BitVec.eq_of_toNat_eq heq)
      omega
    have h1 := chs_advance_sendEpoch_ok F authKey dir secret sendCtr recvSet ch h e hlt hhi
    let epochIndex0 := e.toNat - (ch.sendEpoch.toNat - 1)
    let dropCount := epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
    let epochIndex' := epochIndex0 - dropCount
    exact chs_sendKey_at_sendEpoch F authKey dir secret sendCtr recvSet _ h1 e rfl hhi hn
      epochIndex' (by dsimp [epochIndex', dropCount, epochIndex0, EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH]; omega)
  · simp only [Bool.not_eq_true] at hne
    have heq : ch.sendEpoch = e := by simpa [bne_eq_false_iff_eq] using hne
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact chs_sendKey_at_sendEpoch F authKey dir secret sendCtr recvSet ch h e heq hhi hn
      (e.toNat - (ch.sendEpoch.toNat - 1)) (by rw [heq])

private theorem chv_ofNat32_beq_zero_false {idx : ℕ} (hidx : 1 ≤ idx) (hlt : idx < 2 ^ 32) :
    (BitVec.ofNat 32 idx == 0#32) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h1
  omega

private theorem chv_epochIdx_ok {ch : Chain} {e : Epoch}
    (hlen : ch.links.length = ch.currentEpoch.toNat - (ch.sendEpoch.toNat - 1) + 1)
    (hlo : ch.sendEpoch.toNat - 1 ≤ e.toNat) (hhi : e.toNat ≤ ch.currentEpoch.toNat) :
    ch.epochIdx e = .ok (e.toNat - (ch.sendEpoch.toNat - 1)) := by
  unfold Chain.epochIdx
  have hnotgt : ¬ (e > ch.currentEpoch) := by
    simp only [gt_iff_lt, BitVec.lt_def]
    omega
  have hsub : (ch.currentEpoch - e).toNat = ch.currentEpoch.toNat - e.toNat := by
    apply BitVec.toNat_sub_of_le
    rw [BitVec.le_def]
    exact hhi
  have hback : ¬ ((ch.currentEpoch - e).toNat ≥ ch.links.length) := by
    rw [hsub, hlen]
    omega
  simp only [hnotgt, ↓reduceIte, hback, Except.ok.injEq]
  rw [hsub, hlen]
  omega

private theorem chv_epochIdx_err {ch : Chain} {e : Epoch}
    (hsend_le : ch.sendEpoch.toNat ≤ ch.currentEpoch.toNat)
    (hlen : ch.links.length = ch.currentEpoch.toNat - (ch.sendEpoch.toNat - 1) + 1)
    (herr : e.toNat + 1 < ch.sendEpoch.toNat ∨ ch.currentEpoch.toNat < e.toNat) :
    ch.epochIdx e = .error (.epochOutOfRange e) := by
  unfold Chain.epochIdx
  by_cases hgt : e > ch.currentEpoch
  · simp only [hgt, ↓reduceIte]
  · have hle : e.toNat ≤ ch.currentEpoch.toNat := by
      simp only [gt_iff_lt, BitVec.lt_def, not_lt] at hgt
      exact hgt
    have hsub : (ch.currentEpoch - e).toNat = ch.currentEpoch.toNat - e.toNat := by
      apply BitVec.toNat_sub_of_le
      rw [BitVec.le_def]
      exact hle
    have hback : (ch.currentEpoch - e).toNat ≥ ch.links.length := by
      rw [hsub, hlen]
      omega
    simp only [hgt, ↓reduceIte, hback]

/-- `Chain.recvKey` at an active chain epoch `e` and fresh in-window index `idx` returns
`keyAt F (seedAt … dir.switch e) (idx - 1)` and preserves `ChainOk` on `insert idx (recvSet e)`. -/
theorem recvKey_ok (F : ShaCompress) (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes)
    (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (e : Epoch) (idx : ℕ)
    (hlo : ch.sendEpoch.toNat - 1 ≤ e.toNat) (hhi : e.toNat ≤ ch.currentEpoch.toNat)
    (hidx : 1 ≤ idx) (hnew : idx ∉ recvSet e.toNat)
    (hjump : (recvSet e.toNat).sup id < idx → idx - (recvSet e.toNat).sup id ≤ 25000)
    (htrim : idx < (recvSet e.toNat).sup id → (recvSet e.toNat).sup id ≤ idx + 2000)
    (hb : idx + 2000 ≤ 2 ^ 32) (hR : (recvSet e.toNat).sup id + 2000 ≤ 2 ^ 32) :
    ∃ ch', ch.recvKey (spqrHkdfWith F) e (BitVec.ofNat 32 idx) =
        .ok (ch', keyAt F (seedAt F authKey secret dir.switch e.toNat) (idx - 1)) ∧
      ch'.currentEpoch = ch.currentEpoch ∧ ch'.sendEpoch = ch.sendEpoch ∧
      ChainOk F authKey dir secret sendCtr
        (Function.update recvSet e.toNat (insert idx (recvSet e.toNat))) ch' := by
  have hidx_ne : (BitVec.ofNat 32 idx == 0#32) = false :=
    chv_ofNat32_beq_zero_false hidx (by omega)
  have hep : ch.epochIdx e = .ok (e.toNat - (ch.sendEpoch.toNat - 1)) :=
    chv_epochIdx_ok h.hlen hlo hhi
  obtain ⟨link, hlink, hrecv⟩ := h.hrecvDir e.toNat hlo hhi
  obtain ⟨recv', hkey, hrecv'⟩ :=
    recvDir_key F (seedAt F authKey secret dir.switch e.toNat)
      (length_seedAt F authKey secret dir.switch e.toNat) (recvSet e.toNat) link.recv hrecv
      idx hidx hnew hjump htrim hb hR
  have hkey' : link.recv.key (spqrHkdfWith F) (BitVec.ofNat 32 idx) ch.params =
      .ok (recv', keyAt F (seedAt F authKey secret dir.switch e.toNat) (idx - 1)) := by
    rw [h.hparams]; exact hkey
  have hlt_len : e.toNat - (ch.sendEpoch.toNat - 1) < ch.links.length := by
    rw [h.hlen]; omega
  refine ⟨{ ch with links := ch.links.set (e.toNat - (ch.sendEpoch.toNat - 1)) { link with recv := recv' } },
    ?_, rfl, rfl, ?_⟩
  · unfold Chain.recvKey
    simp only [hidx_ne, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hep, ChainResult.ofError,
      bind, Except.bind, hlink, hkey', pure, Except.pure]
  · refine
      { hdir := h.hdir
        hparams := h.hparams
        hsend_le := h.hsend_le
        hroot := h.hroot
        hlen := by rw [List.length_set, h.hlen]
        hsendDir := fun e' hlo' hhi' => by
          dsimp only at hlo' hhi' ⊢
          obtain ⟨l', hl', hs'⟩ := h.hsendDir e' hlo' hhi'
          rw [List.getElem?_set]
          split_ifs with heq
          · rw [heq] at hlink
            rw [hlink] at hl'
            cases hl'
            exact ⟨{ link with recv := recv' }, rfl, hs'⟩
          · exact ⟨l', hl', hs'⟩
        hsendOld := fun l0 hs1 hl0 => by
          dsimp only at hs1 hl0
          rw [List.getElem?_set] at hl0
          split_ifs at hl0 with heq
          · cases hl0
            rw [heq] at hlink
            exact h.hsendOld link hs1 hlink
          · exact h.hsendOld l0 hs1 hl0
        hrecvDir := fun e' hlo' hhi' => by
          dsimp only at hlo' hhi' ⊢
          rw [List.getElem?_set]
          by_cases he' : e' = e.toNat
          · subst he'
            simp only [↓reduceIte, hlt_len, Function.update_self]
            exact ⟨{ link with recv := recv' }, rfl, hrecv'⟩
          · have hne : e.toNat - (ch.sendEpoch.toNat - 1) ≠ e' - (ch.sendEpoch.toNat - 1) := by omega
            simp only [hne, ↓reduceIte, Function.update_of_ne he']
            exact h.hrecvDir e' hlo' hhi'
        hfreshSend := h.hfreshSend
        hfreshRecv := fun e' hgt' => by
          dsimp only at hgt'
          have hne : e' ≠ e.toNat := by omega
          rw [Function.update_of_ne hne]
          exact h.hfreshRecv e' hgt' }

/-- `Chain.recvKey` rejects messages whose epoch lies outside `[lo, currentEpoch]` or whose
index violates the replay, jump, or trim window bounds. -/
theorem recvKey_err (F : ShaCompress) (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes)
    (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (e : Epoch) (idx : ℕ) (hidx : 1 ≤ idx)
    (hidx32 : idx < 2 ^ 32)
    (hout : e.toNat + 1 < ch.sendEpoch.toNat ∨ ch.currentEpoch.toNat < e.toNat ∨
      idx ∈ recvSet e.toNat ∨
      ((recvSet e.toNat).sup id < idx ∧ 25000 < idx - (recvSet e.toNat).sup id) ∨
      (idx < (recvSet e.toNat).sup id ∧ idx + 2000 < (recvSet e.toNat).sup id)) :
    ∀ r, ch.recvKey (spqrHkdfWith F) e (BitVec.ofNat 32 idx) ≠ .ok r := by
  intro r
  have hidx_ne : (BitVec.ofNat 32 idx == 0#32) = false :=
    chv_ofNat32_beq_zero_false hidx hidx32
  unfold Chain.recvKey
  simp only [hidx_ne, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hrange : e.toNat + 1 < ch.sendEpoch.toNat ∨ ch.currentEpoch.toNat < e.toNat
  · rw [chv_epochIdx_err h.hsend_le h.hlen hrange]
    simp [ChainResult.ofError, bind, Except.bind]
  · have hlo : ch.sendEpoch.toNat - 1 ≤ e.toNat := by omega
    have hhi : e.toNat ≤ ch.currentEpoch.toNat := by omega
    have hout' : idx ∈ recvSet e.toNat ∨
        ((recvSet e.toNat).sup id < idx ∧ 25000 < idx - (recvSet e.toNat).sup id) ∨
        (idx < (recvSet e.toNat).sup id ∧ idx + 2000 < (recvSet e.toNat).sup id) := by
      rcases hout with h1 | h2 | h3
      · exact False.elim (hrange (.inl h1))
      · exact False.elim (hrange (.inr h2))
      · exact h3
    rw [chv_epochIdx_ok h.hlen hlo hhi]
    obtain ⟨link, hlink, hrecv⟩ := h.hrecvDir e.toNat hlo hhi
    simp only [ChainResult.ofError, bind, Except.bind, hlink, h.hparams]
    have herr := recvDir_key_err F (seedAt F authKey secret dir.switch e.toNat)
      (recvSet e.toNat) link.recv hrecv idx hidx32 hout'
    rcases hkey : link.recv.key (spqrHkdfWith F) (BitVec.ofNat 32 idx) dparams with err | ⟨recv', out⟩
    · simp
    · exact False.elim (herr (recv', out) hkey)

/-- `genAt` reads `secret` only on `[1, e]`. -/
theorem genAt_congr (F : ShaCompress) (authKey : Bytes) (secret secret' : ℕ → Bytes) :
    ∀ e, (∀ i, 1 ≤ i → i ≤ e → secret' i = secret i) →
      genAt F authKey secret' e = genAt F authKey secret e
  | 0, _ => rfl
  | e + 1, hs => by
    simp only [genAt]
    rw [genAt_congr F authKey secret secret' e (fun i h1 h2 => hs i h1 (by omega)),
      hs (e + 1) (by omega) le_rfl]

/-- `ChainOk` depends on the ghost `secret` schedule only at epochs `1 ≤ i ≤ currentEpoch`. -/
theorem chainOk_congr (F : ShaCompress) (authKey : Bytes) (dir : Direction) (secret secret' : ℕ → Bytes)
    (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch)
    (hs : ∀ e, 1 ≤ e → e ≤ ch.currentEpoch.toNat → secret' e = secret e) :
    ChainOk F authKey dir secret' sendCtr recvSet ch := by
  have hseed : ∀ d e, e ≤ ch.currentEpoch.toNat →
      seedAt F authKey secret' d e = seedAt F authKey secret d e := by
    intro d e he
    simp only [seedAt, genAt_congr F authKey secret secret' e (fun i h1 h2 => hs i h1 (h2.trans he))]
  exact
    { hdir := h.hdir
      hparams := h.hparams
      hsend_le := h.hsend_le
      hroot := by
        rw [genAt_congr F authKey secret secret' ch.currentEpoch.toNat hs]
        exact h.hroot
      hlen := h.hlen
      hsendDir := fun e hlo hhi => by
        rw [hseed dir e hhi]
        exact h.hsendDir e hlo hhi
      hsendOld := h.hsendOld
      hrecvDir := fun e hlo hhi => by
        rw [hseed dir.switch e hhi]
        exact h.hrecvDir e hlo hhi
      hfreshSend := h.hfreshSend
      hfreshRecv := h.hfreshRecv }

/-- Key agreement on chain epoch `e`: the `(n + 1)`-th send key on `dir` equals the receive key
at index `n + 1` on `dir.switch`. -/
theorem send_recv_key_eq (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes)
    (dir : Direction) (e n : ℕ) :
    keyAt F (seedAt F authKey secret dir.switch.switch e) (n + 1 - 1) =
      keyAt F (seedAt F authKey secret dir e) n := by
  simp only [seedAt_send_recv, Nat.add_sub_cancel]

end CryptoVerification.SpqrV1Sync.ChainSync
