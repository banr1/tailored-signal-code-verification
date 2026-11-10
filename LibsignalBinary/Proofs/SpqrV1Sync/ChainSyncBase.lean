/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top

set_option autoImplicit false

/-!
# SPQR V1 Symmetric Chain Base Definitions and `KeyHistory` Invariants

Ghost key-schedule functions (`stepGen`, `nextAt`, `keyAt`, `genAt`, `seedOf`, `seedAt`),
`KeyHistory` representation (`HistRepr`), and chain invariants (`SendDirOk`, `RecvDirOk`, `ChainOk`)
used by `ChainSync`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.ChainSync

open CryptoVerification.LibsignalSpqrV1
open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)

/-- Default chain parameters serialized to protobuf (`max_jump = 25000`, `max_ooo_keys = 2000`). -/
abbrev dparams : ChainParamsPB := ChainParams.default.intoPb

/-- 32 zero bytes, used as the HKDF salt in `Chain.new` and `nextKeyInternal`. -/
abbrev zeros32 : Bytes := List.replicate 32 0#8

/-- 64-byte HKDF output derived when stepping the chain counter from `i` to `i + 1`. -/
def stepGen (F : ShaCompress) (next : Bytes) (i : ℕ) : Bytes :=
  spqrHkdfWith F zeros32 next (toBEBytes 4 (BitVec.ofNat 32 (i + 1)) ++ chainNextInfo) 64

/-- Chain value `next` of a direction started at `seed` after `n` derived keys. -/
def nextAt (F : ShaCompress) (seed : Bytes) : ℕ → Bytes
  | 0 => seed
  | n + 1 => (stepGen F (nextAt F seed n) n).take 32

/-- Message key at 1-based index `n + 1` of a direction started at `seed`. -/
def keyAt (F : ShaCompress) (seed : Bytes) (n : ℕ) : Bytes :=
  ((stepGen F (nextAt F seed n) n).drop 32).take 32

/-- 96-byte epoch generator for chain epoch `e`, incorporating `secret (e + 1)` at each step. -/
def genAt (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes) : ℕ → Bytes
  | 0 => spqrHkdfWith F zeros32 authKey chainStartInfo 96
  | e + 1 => spqrHkdfWith F ((genAt F authKey secret e).take 32) (secret (e + 1)) chainAddEpochInfo 96

/-- Directional 32-byte slice of a 96-byte epoch generator (`a2b` at `[32..64]`, `b2a` at `[64..96]`). -/
def seedOf (dir : Direction) (g : Bytes) : Bytes :=
  match dir with
  | .a2b => (g.drop 32).take 32
  | .b2a => (g.drop 64).take 32

/-- Initial 32-byte directional seed for `dir` in chain epoch `e`. -/
abbrev seedAt (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes) (dir : Direction) (e : ℕ) :
    Bytes :=
  seedOf dir (genAt F authKey secret e)

/-- Invariant on a send direction that has derived `n` keys from `seed`. -/
structure SendDirOk (F : ShaCompress) (seed : Bytes) (n : ℕ) (d : ChainEpochDirection) : Prop where
  hctr : d.ctr.toNat = n
  hnext : d.next = nextAt F seed n

/-- 36-byte `KeyHistory` entry encoding 4-byte big-endian index `j` followed by 32-byte key `k`. -/
def histEntry (j : ℕ) (k : Bytes) : Bytes :=
  toBEBytes 4 (BitVec.ofNat 32 j) ++ k

/-- `KeyHistory` representation invariant: `h` stores `keyAt F seed (j - 1)` for each `j ∈ S`
with no duplicate indices. -/
def HistRepr (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory) : Prop :=
  ∃ L : List ℕ, L.Nodup ∧ L.toFinset = S ∧
    h.data = (L.map fun j => histEntry j (keyAt F seed (j - 1))).flatten

/-- Honest receive-direction invariant for accepted index set `R ⊆ [1, ∞)`: `ctr = R.sup id`,
`next = nextAt F seed ctr`, and `prev` represents a set `S` of skipped indices below `ctr`
containing every skipped index `j` with `ctr ≤ j + 2000`. -/
structure RecvDirOk (F : ShaCompress) (seed : Bytes) (R : Finset ℕ) (d : ChainEpochDirection) :
    Prop where
  hpos : ∀ j ∈ R, 1 ≤ j
  hctr : d.ctr.toNat = R.sup id
  hnext : d.next = nextAt F seed d.ctr.toNat
  hprev : ∃ S : Finset ℕ, HistRepr F seed S d.prev ∧
    (∀ j ∈ S, 1 ≤ j ∧ j < d.ctr.toNat ∧ j ∉ R) ∧
    (∀ j, 1 ≤ j → j < d.ctr.toNat → j ∉ R → d.ctr.toNat ≤ j + 2000 → j ∈ S)

/-- Honest symmetric-chain invariant over ghost epoch secrets `secret`, per-epoch send counts
`sendCtr`, and per-epoch received index sets `recvSet`. Links cover `[sendEpoch - 1, currentEpoch]`,
active send directions satisfy `SendDirOk`, and kept receive directions satisfy `RecvDirOk`. -/
structure ChainOk (F : ShaCompress) (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes)
    (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain) : Prop where
  hdir : ch.dir = dir
  hparams : ch.params = dparams
  hsend_le : ch.sendEpoch.toNat ≤ ch.currentEpoch.toNat
  hroot : ch.nextRoot = (genAt F authKey secret ch.currentEpoch.toNat).take 32
  hlen : ch.links.length = ch.currentEpoch.toNat - (ch.sendEpoch.toNat - 1) + 1
  hsendDir : ∀ e, ch.sendEpoch.toNat ≤ e → e ≤ ch.currentEpoch.toNat →
    ∃ l, ch.links[e - (ch.sendEpoch.toNat - 1)]? = some l ∧
      SendDirOk F (seedAt F authKey secret dir e) (sendCtr e) l.send
  hsendOld : ∀ l, 1 ≤ ch.sendEpoch.toNat → ch.links[0]? = some l → l.send.next = []
  hrecvDir : ∀ e, ch.sendEpoch.toNat - 1 ≤ e → e ≤ ch.currentEpoch.toNat →
    ∃ l, ch.links[e - (ch.sendEpoch.toNat - 1)]? = some l ∧
      RecvDirOk F (seedAt F authKey secret dir.switch e) (recvSet e) l.recv
  hfreshSend : ∀ e, ch.currentEpoch.toNat < e → sendCtr e = 0
  hfreshRecv : ∀ e, ch.currentEpoch.toNat < e → recvSet e = ∅

end CryptoVerification.SpqrV1Sync.ChainSync

namespace LibsignalBinary.Proofs.SpqrV1Sync.ChainSyncBase

open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.LibsignalSpqrV1
open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)

theorem dparams_maxOoo : dparams.maxOooKeysOrDefault = 2000#32 := rfl

theorem dparams_maxJump : dparams.maxJumpOrDefault = 25000#32 := rfl

theorem dparams_trimSize : dparams.trimSize = 2201 := rfl

@[local simp] theorem length_stepGen (F : ShaCompress) (next : Bytes) (i : ℕ) :
    (stepGen F next i).length = 64 := by
  simp [stepGen]

theorem length_nextAt (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32) :
    ∀ n, (nextAt F seed n).length = 32
  | 0 => hseed
  | n + 1 => by simp [nextAt]

@[local simp] theorem length_keyAt (F : ShaCompress) (seed : Bytes) (n : ℕ) :
    (keyAt F seed n).length = 32 := by
  simp [keyAt]

@[local simp] theorem length_genAt (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes) (e : ℕ) :
    (genAt F authKey secret e).length = 96 := by
  cases e <;> simp [genAt]

theorem length_seedOf (dir : Direction) (g : Bytes) (hg : g.length = 96) :
    (seedOf dir g).length = 32 := by
  cases dir <;> simp [seedOf, hg]

@[local simp] theorem length_seedAt (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes)
    (dir : Direction) (e : ℕ) : (seedAt F authKey secret dir e).length = 32 :=
  length_seedOf dir _ (length_genAt F authKey secret e)

theorem cedForDirection_eq (g : Bytes) (dir : Direction) :
    Chain.cedForDirection g dir = ChainEpochDirection.new (seedOf dir g) := by
  cases dir <;> rfl

@[local simp] theorem switch_switch (dir : Direction) : dir.switch.switch = dir := by
  cases dir <;> rfl

/-- Peer directional seeds agree (`dir.switch.switch = dir`). -/
theorem seedAt_send_recv (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes)
    (dir : Direction) (e : ℕ) :
    seedAt F authKey secret dir.switch.switch e = seedAt F authKey secret dir e := by
  rw [switch_switch]

theorem sendDirOk_new (F : ShaCompress) (seed : Bytes) :
    SendDirOk F seed 0 (ChainEpochDirection.new seed) :=
  ⟨rfl, rfl⟩

/-- Stepping an honest send direction with `n + 1 < 2 ^ 32` outputs `keyAt F seed n` at index
`n + 1` and advances `next` to `nextAt F seed (n + 1)`. -/
theorem sendDir_nextKey (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32) (n : ℕ)
    (d : ChainEpochDirection) (h : SendDirOk F seed n d) (hn : n + 1 < 2 ^ 32) :
    d.nextKey (spqrHkdfWith F) =
      .ok ({ d with next := nextAt F seed (n + 1), ctr := BitVec.ofNat 32 (n + 1) },
        (BitVec.ofNat 32 (n + 1), keyAt F seed n)) := by
  have hlen : (nextAt F seed n).length = 32 := length_nextAt F seed hseed n
  have hctr := h.hctr
  have hne : (d.ctr == 0xffffffff#32) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have : d.ctr.toNat = 4294967295 := by rw [heq]; rfl
    omega
  have hctr' : d.ctr + 1#32 = BitVec.ofNat 32 (n + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [ChainEpochDirection.nextKey, ChainEpochDirection.nextKeyInternal,
    h.hnext, hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hne, hctr']
  rfl

theorem sendDir_nextKey_ok (F : ShaCompress) (seed : Bytes) (n : ℕ) (d : ChainEpochDirection)
    (hn : n + 1 < 2 ^ 32) :
    SendDirOk F seed (n + 1) { d with next := nextAt F seed (n + 1), ctr := BitVec.ofNat 32 (n + 1) } := by
  refine ⟨?_, rfl⟩
  simp only [BitVec.toNat_ofNat]
  omega

theorem histRepr_empty (F : ShaCompress) (seed : Bytes) : HistRepr F seed ∅ KeyHistory.new :=
  ⟨[], List.nodup_nil, rfl, rfl⟩

theorem recvDirOk_new (F : ShaCompress) (seed : Bytes) :
    RecvDirOk F seed ∅ (ChainEpochDirection.new seed) := by
  refine ⟨by simp, by simp [ChainEpochDirection.new], rfl, ∅, histRepr_empty F seed, by simp, ?_⟩
  intro j _ hj
  simp [ChainEpochDirection.new] at hj

private theorem toBEBytes4_eq (x : BitVec 32) :
    toBEBytes 4 x =
      [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] :=
  rfl

private theorem u32_digits_decomp (x : BitVec 32) :
    (x.extractLsb' 24 8).toNat < 256 ∧
    (x.extractLsb' 16 8).toNat < 256 ∧
    (x.extractLsb' 8 8).toNat < 256 ∧
    (x.extractLsb' 0 8).toNat < 256 ∧
    x.toNat =
      (x.extractLsb' 24 8).toNat * 16777216 +
      (x.extractLsb' 16 8).toNat * 65536 +
      (x.extractLsb' 8 8).toNat * 256 +
      (x.extractLsb' 0 8).toNat := by
  have hx := x.isLt
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

/-- Lexicographic comparison on 4-byte big-endian encodings agrees with `<` on `BitVec 32`. -/
theorem bytesLt_toBEBytes4 (a b : BitVec 32) :
    bytesLt (toBEBytes 4 a) (toBEBytes 4 b) = decide (a.toNat < b.toNat) := by
  rw [toBEBytes4_eq a, toBEBytes4_eq b]
  obtain ⟨ha3, ha2, ha1, ha0, ha⟩ := u32_digits_decomp a
  obtain ⟨hb3, hb2, hb1, hb0, hb⟩ := u32_digits_decomp b
  simp only [bytesLt, BitVec.lt_def]
  rw [ha, hb]
  generalize (a.extractLsb' 24 8).toNat = a3 at ha3 ⊢
  generalize (a.extractLsb' 16 8).toNat = a2 at ha2 ⊢
  generalize (a.extractLsb' 8 8).toNat = a1 at ha1 ⊢
  generalize (a.extractLsb' 0 8).toNat = a0 at ha0 ⊢
  generalize (b.extractLsb' 24 8).toNat = b3 at hb3 ⊢
  generalize (b.extractLsb' 16 8).toNat = b2 at hb2 ⊢
  generalize (b.extractLsb' 8 8).toNat = b1 at hb1 ⊢
  generalize (b.extractLsb' 0 8).toNat = b0 at hb0 ⊢
  split_ifs <;> simp_all <;> omega

/-- 4-byte big-endian encoding is injective on `BitVec 32`. -/
theorem toBEBytes4_injective : Function.Injective (fun x : BitVec 32 => toBEBytes 4 x) := by
  intro a b h
  dsimp only at h
  have h1 := bytesLt_toBEBytes4 a b
  have h2 := bytesLt_toBEBytes4 b a
  rw [h, bytesLt_toBEBytes4 b b] at h1 h2
  simp at h1 h2
  exact BitVec.eq_of_toNat_eq (by omega)

abbrev encEntry (F : ShaCompress) (seed : Bytes) (j : ℕ) : Bytes :=
  histEntry j (keyAt F seed (j - 1))

def encList (F : ShaCompress) (seed : Bytes) (L : List ℕ) : Bytes :=
  (L.map (encEntry F seed)).flatten

private theorem length_toBEBytes4 (x : BitVec 32) : (toBEBytes 4 x).length = 4 := rfl

private theorem length_encEntry (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (encEntry F seed j).length = 36 := by
  simp [encEntry, histEntry, length_toBEBytes4]

private theorem encList_cons (F : ShaCompress) (seed : Bytes) (x : ℕ) (xs : List ℕ) :
    encList F seed (x :: xs) = encEntry F seed x ++ encList F seed xs := rfl

private theorem encList_append (F : ShaCompress) (seed : Bytes) (L1 L2 : List ℕ) :
    encList F seed (L1 ++ L2) = encList F seed L1 ++ encList F seed L2 := by
  simp [encList]

private theorem length_encList (F : ShaCompress) (seed : Bytes) :
    ∀ L : List ℕ, (encList F seed L).length = 36 * L.length
  | [] => rfl
  | x :: xs => by
    rw [encList_cons, List.length_append, length_encEntry, length_encList F seed xs,
      List.length_cons]
    omega

private theorem encList_take (F : ShaCompress) (seed : Bytes) :
    ∀ (k : ℕ) (L : List ℕ), (encList F seed L).take (36 * k) = encList F seed (L.take k)
  | 0, _ => rfl
  | k + 1, [] => rfl
  | k + 1, x :: xs => by
    have hlen : (encEntry F seed x).length = 36 := length_encEntry F seed x
    rw [encList_cons, List.take_append, hlen,
      List.take_of_length_le (by rw [hlen]; omega),
      show 36 * (k + 1) - 36 = 36 * k by omega,
      encList_take F seed k xs]
    rfl

private theorem encList_drop (F : ShaCompress) (seed : Bytes) :
    ∀ (k : ℕ) (L : List ℕ), (encList F seed L).drop (36 * k) = encList F seed (L.drop k)
  | 0, _ => rfl
  | k + 1, [] => rfl
  | k + 1, x :: xs => by
    have hlen : (encEntry F seed x).length = 36 := length_encEntry F seed x
    rw [encList_cons, List.drop_append, hlen,
      List.drop_eq_nil_of_le (by rw [hlen]; omega), List.nil_append,
      show 36 * (k + 1) - 36 = 36 * k by omega,
      encList_drop F seed k xs]
    rfl

private theorem encList_entry_tag (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) :
    ((encList F seed L).drop (36 * k)).take 4 = toBEBytes 4 (BitVec.ofNat 32 L[k]) := by
  rw [encList_drop, List.drop_eq_getElem_cons hk, encList_cons]
  simp only [encEntry, histEntry, List.append_assoc, toBEBytes4_eq]
  rfl

private theorem encList_entry_val (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) :
    ((encList F seed L).drop (36 * k + 4)).take 32 = keyAt F seed (L[k] - 1) := by
  have hd : (encList F seed L).drop (36 * k + 4) = ((encList F seed L).drop (36 * k)).drop 4 := by
    simp [List.drop_drop, Nat.add_comm]
  rw [hd, encList_drop, List.drop_eq_getElem_cons hk, encList_cons]
  simp only [encEntry, histEntry, List.append_assoc, toBEBytes4_eq]
  dsimp only [List.cons_append, List.nil_append, List.drop]
  rw [List.take_append_of_le_length (by rw [length_keyAt]),
    List.take_of_length_le (by rw [length_keyAt])]

private def swapRemoveIdx (L : List ℕ) (k : ℕ) : List ℕ :=
  if k + 1 < L.length then
    L.take k ++ L.drop (L.length - 1) ++ (L.take (L.length - 1)).drop (k + 1)
  else
    L.take k

private theorem swapRemoveIdx_perm (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    List.Perm (L[k] :: swapRemoveIdx L k) L := by
  unfold swapRemoveIdx
  split_ifs with hk1
  · let n := L.length - 1
    have hkn : k < n := by omega
    have hk_tn : k < (L.take n).length := by simp [n]; omega
    have hsplit_tn : L.take n = L.take k ++ (L[k] :: (L.take n).drop (k + 1)) := by
      conv_lhs => rw [← List.take_append_drop k (L.take n)]
      rw [List.take_take, Nat.min_eq_left (by omega), List.drop_eq_getElem_cons hk_tn,
        List.getElem_take]
    have hsplit_L : L = L.take k ++ (L[k] :: ((L.take n).drop (k + 1) ++ L.drop n)) := by
      calc L = L.take n ++ L.drop n := (List.take_append_drop n L).symm
        _ = (L.take k ++ (L[k] :: (L.take n).drop (k + 1))) ++ L.drop n := by
          conv_lhs => arg 1; rw [hsplit_tn]
        _ = L.take k ++ (L[k] :: ((L.take n).drop (k + 1) ++ L.drop n)) := by
          rw [List.append_assoc, List.cons_append]
    rw [List.append_assoc]
    have hp1 :
        List.Perm (L[k] :: (L.take k ++ (L.drop n ++ (L.take n).drop (k + 1))))
          (L[k] :: (L.take k ++ ((L.take n).drop (k + 1) ++ L.drop n))) :=
      List.Perm.cons L[k] (List.Perm.append_left (L.take k) List.perm_append_comm)
    conv_rhs => rw [hsplit_L]
    exact hp1.trans List.perm_middle.symm
  · have hsplit_L : L = L.take k ++ [L[k]] := by
      conv_lhs => rw [← List.take_append_drop k L]
      rw [List.drop_eq_getElem_cons hk, List.drop_eq_nil_of_le (by omega)]
    conv_rhs => rw [hsplit_L]
    simpa only [List.append_nil] using (@List.perm_middle _ L[k] (L.take k) []).symm

private theorem length_swapRemoveIdx (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (swapRemoveIdx L k).length = L.length - 1 := by
  have hp := (swapRemoveIdx_perm L k hk).length_eq
  simp only [List.length_cons] at hp
  omega

private theorem swapRemoveIdx_nodup_toFinset (L : List ℕ) (hL : L.Nodup) (k : ℕ)
    (hk : k < L.length) :
    (swapRemoveIdx L k).Nodup ∧ (swapRemoveIdx L k).toFinset = L.toFinset.erase L[k] := by
  have hp := swapRemoveIdx_perm L k hk
  have hcons : (L[k] :: swapRemoveIdx L k).Nodup := hp.nodup_iff.mpr hL
  rw [List.nodup_cons] at hcons
  refine ⟨hcons.2, ?_⟩
  ext x
  simp only [List.mem_toFinset, Finset.mem_erase, ← hp.mem_iff, List.mem_cons]
  by_cases hx : x = L[k] <;> simp [hx, hcons.1]

private theorem encList_remove (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) (params : ChainParamsPB) :
    ({ data := encList F seed L } : KeyHistory).remove (36 * k) params =
      { data := encList F seed (swapRemoveIdx L k) } := by
  unfold KeyHistory.remove swapRemoveIdx
  simp only [KeyHistory.KEY_SIZE, length_encList]
  by_cases hk1 : k + 1 < L.length
  · have hlt : 36 * k + (4 + 32) < 36 * L.length := by omega
    simp only [hlt, hk1, ↓reduceIte]
    have hnewEnd : 36 * L.length - (4 + 32) = 36 * (L.length - 1) := by omega
    have hidx1 : 36 * k + (4 + 32) = 36 * (k + 1) := by omega
    rw [hnewEnd, hidx1, encList_take, encList_take, encList_drop, encList_drop, ← encList_append,
      ← encList_append]
    congr 1
    apply List.take_of_length_le
    rw [length_encList]
    have hlen_sr := length_swapRemoveIdx L k hk
    unfold swapRemoveIdx at hlen_sr
    simp only [hk1, ↓reduceIte] at hlen_sr
    rw [hlen_sr]
  · have hnlt : ¬ (36 * k + (4 + 32) < 36 * L.length) := by omega
    simp only [hnlt, hk1, ↓reduceIte, encList_take]

private theorem getLoop_found (F : ShaCompress) (seed : Bytes) (L : List ℕ)
    (hL : L.Nodup) (hlt : ∀ x ∈ L, x < 2 ^ 32) (j : ℕ) (hj32 : j < 2 ^ 32) :
    ∀ (rem k : ℕ), L.length - k = rem → j ∈ L.drop k →
      ∃ h', KeyHistory.getLoop { data := encList F seed L } (BitVec.ofNat 32 j)
          (toBEBytes 4 (BitVec.ofNat 32 j)) dparams (36 * k) =
        .ok (h', keyAt F seed (j - 1)) ∧
        HistRepr F seed (L.toFinset.erase j) h'
  | 0, k, hrem, hj => by
    have hdrop : L.drop k = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop] at hj
    nomatch hj
  | rem + 1, k, hrem, hj => by
    have hk : k < L.length := by omega
    have hk_bytes : 36 * k < (encList F seed L).length := by rw [length_encList]; omega
    have hLk32 : L[k] < 2 ^ 32 := hlt L[k] (List.getElem_mem hk)
    rw [KeyHistory.getLoop]
    simp only [hk_bytes, ↓reduceDIte, encList_entry_tag F seed L k hk]
    by_cases heq : L[k] = j
    · subst heq
      simp only [beq_self_eq_true, ↓reduceIte, encList_entry_val F seed L k hk,
        encList_remove F seed L k hk dparams]
      obtain ⟨hnodup', hfin'⟩ := swapRemoveIdx_nodup_toFinset L hL k hk
      exact ⟨_, rfl, swapRemoveIdx L k, hnodup', hfin', rfl⟩
    · have hbeq : (toBEBytes 4 (BitVec.ofNat 32 L[k]) == toBEBytes 4 (BitVec.ofNat 32 j)) = false := by
        rw [beq_eq_false_iff_ne]
        intro hbytes
        have hbv := toBEBytes4_injective hbytes
        have hnat : (BitVec.ofNat 32 L[k]).toNat = (BitVec.ofNat 32 j).toNat := congrArg BitVec.toNat hbv
        simp only [BitVec.toNat_ofNat] at hnat
        omega
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      have hj_next : j ∈ L.drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hk, List.mem_cons] at hj
        exact hj.resolve_left (Ne.symm heq)
      have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
        simp only [KeyHistory.KEY_SIZE]; omega
      rw [hstep]
      exact getLoop_found F seed L hL hlt j hj32 rem (k + 1) (by omega) hj_next

theorem getLoop_not_mem (F : ShaCompress) (seed : Bytes) (L : List ℕ)
    (hlt : ∀ x ∈ L, x < 2 ^ 32) (j : ℕ) (hj32 : j < 2 ^ 32) (hnot : ∀ x ∈ L, x ≠ j) :
    ∀ (rem k : ℕ), L.length - k = rem →
      KeyHistory.getLoop { data := encList F seed L } (BitVec.ofNat 32 j)
        (toBEBytes 4 (BitVec.ofNat 32 j)) dparams (36 * k) =
      .error (.err (.keyAlreadyRequested (BitVec.ofNat 32 j)))
  | 0, k, hrem => by
    have hnlt : ¬ (36 * k < (encList F seed L).length) := by rw [length_encList]; omega
    rw [KeyHistory.getLoop]
    simp only [hnlt, ↓reduceDIte]
  | rem + 1, k, hrem => by
    have hk : k < L.length := by omega
    have hk_bytes : 36 * k < (encList F seed L).length := by rw [length_encList]; omega
    have hLk_mem : L[k] ∈ L := List.getElem_mem hk
    have hLk32 : L[k] < 2 ^ 32 := hlt L[k] hLk_mem
    have hne : L[k] ≠ j := hnot L[k] hLk_mem
    have hbeq : (toBEBytes 4 (BitVec.ofNat 32 L[k]) == toBEBytes 4 (BitVec.ofNat 32 j)) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbytes
      have hbv := toBEBytes4_injective hbytes
      have hnat : (BitVec.ofNat 32 L[k]).toNat = (BitVec.ofNat 32 j).toNat := congrArg BitVec.toNat hbv
      simp only [BitVec.toNat_ofNat] at hnat
      omega
    rw [KeyHistory.getLoop]
    simp only [hk_bytes, ↓reduceDIte, encList_entry_tag F seed L k hk, hbeq, Bool.false_eq_true, ↓reduceIte]
    have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
      simp only [KeyHistory.KEY_SIZE]; omega
    rw [hstep]
    exact getLoop_not_mem F seed L hlt j hj32 hnot rem (k + 1) (by omega)

/-- `KeyHistory.get` retrieves and removes `keyAt F seed (j - 1)` for `j ∈ S` inside the
2000-key window when `j + 2000 < 2 ^ 32`. -/
theorem histRepr_get (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory)
    (hS : HistRepr F seed S h) (hlt : ∀ i ∈ S, i < 2 ^ 32) (j : ℕ) (hj : j ∈ S)
    (ctr : BitVec 32) (hjb : j + 2000 < 2 ^ 32) (hctr : ctr.toNat ≤ j + 2000) :
    ∃ h', h.get (BitVec.ofNat 32 j) ctr dparams = .ok (h', keyAt F seed (j - 1)) ∧
      HistRepr F seed (S.erase j) h' := by
  rcases hS with ⟨L, hLnodup, hLfin, hdata⟩
  have hh_eq : h = { data := encList F seed L } := by
    cases h
    dsimp only at hdata
    rw [hdata]
    rfl
  subst hh_eq
  subst hLfin
  have hLlt : ∀ x ∈ L, x < 2 ^ 32 := fun x hx => hlt x (List.mem_toFinset.mpr hx)
  have hjL : j ∈ L := List.mem_toFinset.mp hj
  unfold KeyHistory.get
  have hal : ((encList F seed L).length % KeyHistory.KEY_SIZE != 0) = false := by
    rw [length_encList]
    simp [KeyHistory.KEY_SIZE]
  have hovf : ¬ ((BitVec.ofNat 32 j).toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) := by
    rw [dparams_maxOoo]
    simp only [BitVec.toNat_ofNat]
    omega
  have hntrim : ¬ (BitVec.ofNat 32 j + dparams.maxOooKeysOrDefault < ctr) := by
    rw [dparams_maxOoo]
    simp only [BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [hal, Bool.false_eq_true, ↓reduceIte, hovf, hntrim]
  have h0 : (0 : ℕ) = 36 * 0 := rfl
  rw [h0]
  exact getLoop_found F seed L hLnodup hLlt j (by omega) L.length 0 (Nat.sub_zero _) hjL

private theorem gcLoop_ok (F : ShaCompress) (seed : Bytes) (horizon : BitVec 32) :
    ∀ (n : ℕ) (L : List ℕ) (k : ℕ), L.length - k ≤ n → L.Nodup → (∀ x ∈ L, x < 2 ^ 32) →
      ∃ h' S', KeyHistory.gcLoop { data := encList F seed L } (toBEBytes 4 horizon) dparams (36 * k) = .ok h' ∧
        HistRepr F seed S' h' ∧ S' ⊆ L.toFinset ∧
        ∀ j ∈ L.toFinset, horizon.toNat ≤ j → j ∈ S'
  | 0, L, k, hle, hLnodup, _ => by
    have hnlt : ¬ (36 * k < (encList F seed L).length) := by rw [length_encList]; omega
    rw [KeyHistory.gcLoop]
    simp only [hnlt, ↓reduceDIte]
    exact ⟨_, L.toFinset, rfl, ⟨L, hLnodup, rfl, rfl⟩, Finset.Subset.refl _, fun _ hj _ => hj⟩
  | n + 1, L, k, hle, hLnodup, hLlt => by
    by_cases hk : k < L.length
    · have hk_bytes : 36 * k < (encList F seed L).length := by rw [length_encList]; omega
      have hnslice : ¬ ((encList F seed L).length < 36 * k + 4) := by rw [length_encList]; omega
      have hLk32 : L[k] < 2 ^ 32 := hLlt L[k] (List.getElem_mem hk)
      rw [KeyHistory.gcLoop]
      simp only [hk_bytes, ↓reduceDIte, hnslice, ↓reduceIte, encList_entry_tag F seed L k hk,
        bytesLt_toBEBytes4]
      have hLk_toNat : (BitVec.ofNat 32 L[k]).toNat = L[k] := by
        simp only [BitVec.toNat_ofNat]; omega
      rw [hLk_toNat]
      by_cases hlt_hor : L[k] < horizon.toNat
      · simp only [hlt_hor, decide_true, ↓reduceIte, encList_remove F seed L k hk dparams]
        have hp := swapRemoveIdx_perm L k hk
        obtain ⟨hnodup', hfin'⟩ := swapRemoveIdx_nodup_toFinset L hLnodup k hk
        have hlen' : (swapRemoveIdx L k).length = L.length - 1 := length_swapRemoveIdx L k hk
        have hLlt' : ∀ x ∈ swapRemoveIdx L k, x < 2 ^ 32 := by
          intro x hx
          exact hLlt x (hp.subset (List.mem_cons_of_mem _ hx))
        obtain ⟨h', S', hgc', hrepr', hsub', hkeep'⟩ :=
          gcLoop_ok F seed horizon n (swapRemoveIdx L k) k (by omega) hnodup' hLlt'
        refine ⟨h', S', hgc', hrepr', ?_, ?_⟩
        · rw [hfin'] at hsub'
          exact hsub'.trans (Finset.erase_subset _ _)
        · intro j hj hge
          apply hkeep' j _ hge
          rw [hfin', Finset.mem_erase]
          exact ⟨by omega, hj⟩
      · simp only [hlt_hor, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
          simp only [KeyHistory.KEY_SIZE]; omega
        rw [hstep]
        exact gcLoop_ok F seed horizon n L (k + 1) (by omega) hLnodup hLlt
    · have hnlt : ¬ (36 * k < (encList F seed L).length) := by rw [length_encList]; omega
      rw [KeyHistory.gcLoop]
      simp only [hnlt, ↓reduceDIte]
      exact ⟨_, L.toFinset, rfl, ⟨L, hLnodup, rfl, rfl⟩, Finset.Subset.refl _, fun _ hj _ => hj⟩

theorem histRepr_gc_le (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory)
    (hS : HistRepr F seed S h) (ctr : BitVec 32) (hS' : ∀ i ∈ S, 1 ≤ i ∧ i ≤ ctr.toNat) :
    ∃ h' S', h.gc ctr dparams = .ok h' ∧ HistRepr F seed S' h' ∧ S' ⊆ S ∧
      ∀ j ∈ S, ctr.toNat ≤ j + 2000 → j ∈ S' := by
  rcases hS with ⟨L, hLnodup, hLfin, hdata⟩
  have hh_eq : h = { data := encList F seed L } := by
    cases h
    dsimp only at hdata
    rw [hdata]
    rfl
  subst hh_eq
  unfold KeyHistory.gc
  by_cases htrim : (encList F seed L).length ≥ dparams.trimSize * KeyHistory.KEY_SIZE
  · simp only [htrim, ↓reduceIte]
    rw [length_encList, dparams_trimSize] at htrim
    simp only [KeyHistory.KEY_SIZE] at htrim
    have hLcard : S.card = L.length := by
      rw [← hLfin]
      exact List.toFinset_card_of_nodup hLnodup
    have hsub_icc : S ⊆ Finset.Icc 1 ctr.toNat := by
      intro x hx
      rw [Finset.mem_Icc]
      exact hS' x hx
    have hcard_le : S.card ≤ ctr.toNat := by
      have h1 := Finset.card_le_card hsub_icc
      rw [Nat.card_Icc] at h1
      omega
    have hctr_ge : 2000 ≤ ctr.toNat := by omega
    have hnunder : ¬ (ctr < dparams.maxOooKeysOrDefault) := by
      rw [dparams_maxOoo]
      simp only [BitVec.lt_def, BitVec.toNat_ofNat]
      omega
    simp only [hnunder, ↓reduceIte]
    have hLlt : ∀ x ∈ L, x < 2 ^ 32 := by
      intro x hx
      have hxS : x ∈ S := hLfin ▸ List.mem_toFinset.mpr hx
      have := (hS' x hxS).2
      have := ctr.isLt
      omega
    have h0 : (0 : ℕ) = 36 * 0 := rfl
    rw [h0]
    obtain ⟨h', S', hgc, hrepr, hsub, hkeep⟩ :=
      gcLoop_ok F seed (ctr - dparams.maxOooKeysOrDefault) L.length L 0 (Nat.le_refl _) hLnodup hLlt
    rw [hLfin] at hsub hkeep
    refine ⟨h', S', hgc, hrepr, hsub, ?_⟩
    intro j hj hge
    apply hkeep j hj
    rw [dparams_maxOoo]
    have := ctr.isLt
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega
  · simp only [htrim, ↓reduceIte]
    exact ⟨_, S, rfl, ⟨L, hLnodup, hLfin, rfl⟩, Finset.Subset.refl _, fun _ hj _ => hj⟩

/-- `KeyHistory.gc` retains every entry of `S` within the 2000-key window (`ctr.toNat ≤ j + 2000`). -/
theorem histRepr_gc (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory)
    (hS : HistRepr F seed S h) (ctr : BitVec 32) (hS' : ∀ i ∈ S, 1 ≤ i ∧ i < ctr.toNat) :
    ∃ h' S', h.gc ctr dparams = .ok h' ∧ HistRepr F seed S' h' ∧ S' ⊆ S ∧
      ∀ j ∈ S, ctr.toNat ≤ j + 2000 → j ∈ S' :=
  histRepr_gc_le F seed S h hS ctr (fun i hi => ⟨(hS' i hi).1, Nat.le_of_lt (hS' i hi).2⟩)

theorem nextKeyInternal_ok (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32)
    (c : ℕ) (next : Bytes) (ctr : BitVec 32) (hnext : next = nextAt F seed c)
    (hctr : ctr.toNat = c) (hc : c + 1 < 2 ^ 32) :
    ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) next ctr =
      .ok (nextAt F seed (c + 1), BitVec.ofNat 32 (c + 1),
        (BitVec.ofNat 32 (c + 1), keyAt F seed c)) := by
  have hlen : (nextAt F seed c).length = 32 := length_nextAt F seed hseed c
  have hne : (ctr == 0xffffffff#32) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have : ctr.toNat = 4294967295 := by rw [heq]; rfl
    omega
  have hctr' : ctr + 1#32 = BitVec.ofNat 32 (c + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [ChainEpochDirection.nextKeyInternal, hnext, hlen, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, hne, hctr']
  rfl

private theorem histRepr_add (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory)
    (hS : HistRepr F seed S h) (j : ℕ) (hj_not : j ∉ S) (params : ChainParamsPB) :
    HistRepr F seed (insert j S) (h.add (BitVec.ofNat 32 j, keyAt F seed (j - 1)) params) := by
  rcases hS with ⟨L, hLnodup, hLfin, hdata⟩
  refine ⟨L ++ [j], ?_, ?_, ?_⟩
  · have hjL : j ∉ L := fun hm => hj_not (hLfin ▸ List.mem_toFinset.mpr hm)
    have hcons : (j :: L).Nodup := List.nodup_cons.mpr ⟨hjL, hLnodup⟩
    have hp : (L ++ [j]).Perm (j :: L) := by
      simpa only [List.append_nil] using (@List.perm_middle _ j L [])
    exact hp.nodup_iff.mpr hcons
  · ext x
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton, Finset.mem_insert, ← hLfin]
    exact Or.comm
  · simp only [KeyHistory.add, hdata, List.map_append, List.map_singleton, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, histEntry, List.append_assoc]

private theorem keyAdvanceLoop_aux (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32)
    (atN : ℕ) (hat : atN + 2000 ≤ 2 ^ 32) :
    ∀ (m : ℕ) (d : ChainEpochDirection) (S : Finset ℕ),
      atN - 1 - d.ctr.toNat = m →
      HistRepr F seed S d.prev →
      (∀ i ∈ S, i ≤ d.ctr.toNat) →
      d.next = nextAt F seed d.ctr.toNat →
      d.ctr.toNat < atN →
      ∃ d', d.keyAdvanceLoop (spqrHkdfWith F) (BitVec.ofNat 32 atN) dparams = .ok d' ∧
        d'.ctr.toNat = atN - 1 ∧ d'.next = nextAt F seed (atN - 1) ∧
        HistRepr F seed
          (S ∪ (Finset.Ioo d.ctr.toNat atN).filter fun j => atN ≤ j + 2000) d'.prev
  | 0, d, S, hm, hS, _, hnext, hc => by
    have hat_toNat : (BitVec.ofNat 32 atN).toNat = atN := by
      simp only [BitVec.toNat_ofNat]; omega
    have hc_eq : d.ctr.toNat = atN - 1 := by omega
    have hnlt : ¬ (d.ctr.toNat + 1 < (BitVec.ofNat 32 atN).toNat) := by rw [hat_toNat]; omega
    have hne_max : (d.ctr == 0xffffffff#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      have : d.ctr.toNat = 4294967295 := by rw [heq]; rfl
      omega
    rw [ChainEpochDirection.keyAdvanceLoop]
    simp only [hnlt, ↓reduceDIte, hne_max, Bool.false_eq_true, ↓reduceIte]
    have hioo : Finset.Ioo d.ctr.toNat atN = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [hioo, Finset.filter_empty, Finset.union_empty]
    exact ⟨d, rfl, hc_eq, hc_eq ▸ hnext, hS⟩
  | m + 1, d, S, hm, hS, hS', hnext, hc => by
    let c := d.ctr.toNat
    have hat_toNat : (BitVec.ofNat 32 atN).toNat = atN := by
      simp only [BitVec.toNat_ofNat]; omega
    have hlt_at : d.ctr.toNat + 1 < (BitVec.ofNat 32 atN).toNat := by rw [hat_toNat]; omega
    have hnk := nextKeyInternal_ok F seed hseed c d.next d.ctr hnext rfl (by omega)
    let ctr' := BitVec.ofNat 32 (c + 1)
    have hctr'_nat : ctr'.toNat = c + 1 := by
      dsimp only [ctr']; simp only [BitVec.toNat_ofNat]; omega
    have hnovf : ¬ (ctr'.toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) := by
      rw [hctr'_nat, dparams_maxOoo]
      simp only [BitVec.toNat_ofNat]
      omega
    have hcond_iff : (ctr' + dparams.maxOooKeysOrDefault ≥ BitVec.ofNat 32 atN) ↔ atN ≤ (c + 1) + 2000 := by
      rw [dparams_maxOoo]
      simp only [ge_iff_le, BitVec.le_def, BitVec.toNat_add, hctr'_nat, BitVec.toNat_ofNat, hat_toNat]
      have hmod : (c + 1 + 2000) % 4294967296 = c + 1 + 2000 := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
    let prev' :=
      if ctr' + dparams.maxOooKeysOrDefault ≥ BitVec.ofNat 32 atN then
        d.prev.add (ctr', keyAt F seed c) dparams
      else
        d.prev
    let d1 : ChainEpochDirection := { ctr := ctr', next := nextAt F seed (c + 1), prev := prev' }
    have hstep_loop :
        d.keyAdvanceLoop (spqrHkdfWith F) (BitVec.ofNat 32 atN) dparams =
          d1.keyAdvanceLoop (spqrHkdfWith F) (BitVec.ofNat 32 atN) dparams := by
      rw [ChainEpochDirection.keyAdvanceLoop]
      simp only [hlt_at, ↓reduceDIte]
      split
      · rename_i p heq
        rw [hnk] at heq
        nomatch heq
      · rename_i next' ctr'' k heq
        rw [hnk] at heq
        have h1 := Except.ok.inj heq
        have hnext' : nextAt F seed (c + 1) = next' := congrArg Prod.fst h1
        have hctr'' : ctr' = ctr'' := congrArg (Prod.fst ∘ Prod.snd) h1
        have hk_eq : (ctr', keyAt F seed c) = k := congrArg (Prod.snd ∘ Prod.snd) h1
        subst hnext' hctr'' hk_eq
        simp only [hnovf, ↓reduceIte]
        rfl
    let S1 : Finset ℕ := if atN ≤ (c + 1) + 2000 then insert (c + 1) S else S
    have hS1 : HistRepr F seed S1 prev' := by
      dsimp only [prev', S1]
      by_cases hw : atN ≤ (c + 1) + 2000
      · have hw_bv : ctr' + dparams.maxOooKeysOrDefault ≥ BitVec.ofNat 32 atN := hcond_iff.mpr hw
        simp only [hw, hw_bv, ↓reduceIte]
        have hnot : c + 1 ∉ S := fun hm => by have := hS' (c + 1) hm; omega
        have hsub1 : c + 1 - 1 = c := Nat.add_sub_cancel c 1
        rw [← hsub1]
        exact histRepr_add F seed S d.prev hS (c + 1) hnot dparams
      · have hnw_bv : ¬ (ctr' + dparams.maxOooKeysOrDefault ≥ BitVec.ofNat 32 atN) :=
          fun hbv => hw (hcond_iff.mp hbv)
        simp only [hw, hnw_bv, ↓reduceIte]
        exact hS
    have hS1' : ∀ i ∈ S1, i ≤ ctr'.toNat := by
      intro i hi
      rw [hctr'_nat]
      dsimp only [S1] at hi
      split_ifs at hi
      · rw [Finset.mem_insert] at hi
        rcases hi with rfl | hiS
        · exact Nat.le_refl _
        · exact Nat.le_trans (hS' i hiS) (Nat.le_succ c)
      · exact Nat.le_trans (hS' i hi) (Nat.le_succ c)
    obtain ⟨d', hd', hd'_ctr, hd'_next, hd'_prev⟩ :=
      keyAdvanceLoop_aux F seed hseed atN hat m d1 S1
        (by dsimp only [d1]; rw [hctr'_nat]; omega)
        hS1 hS1'
        (by dsimp only [d1]; rw [hctr'_nat])
        (by dsimp only [d1]; rw [hctr'_nat]; omega)
    have hset_eq :
        (S1 ∪ (Finset.Ioo d1.ctr.toNat atN).filter fun j => atN ≤ j + 2000) =
          (S ∪ (Finset.Ioo c atN).filter fun j => atN ≤ j + 2000) := by
      dsimp only [d1, S1]
      rw [hctr'_nat]
      ext x
      by_cases hw : atN ≤ (c + 1) + 2000
      · simp only [hw, ↓reduceIte, Finset.mem_union, Finset.mem_insert, Finset.mem_filter, Finset.mem_Ioo]
        constructor
        · rintro ((rfl | hxS) | ⟨⟨h1, h2⟩, h3⟩)
          · exact Or.inr ⟨⟨by omega, by omega⟩, hw⟩
          · exact Or.inl hxS
          · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
        · rintro (hxS | ⟨⟨h1, h2⟩, h3⟩)
          · exact Or.inl (Or.inr hxS)
          · by_cases hx : x = c + 1
            · exact Or.inl (Or.inl hx)
            · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
      · simp only [hw, ↓reduceIte, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioo]
        constructor
        · rintro (hxS | ⟨⟨h1, h2⟩, h3⟩)
          · exact Or.inl hxS
          · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
        · rintro (hxS | ⟨⟨h1, h2⟩, h3⟩)
          · exact Or.inl hxS
          · have hx_ne : x ≠ c + 1 := fun heq => hw (heq ▸ h3)
            exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    rw [hset_eq] at hd'_prev
    exact ⟨d', hstep_loop.trans hd', hd'_ctr, hd'_next, hd'_prev⟩

/-- `keyAdvanceLoop` derives skipped keys up to `atIdx - 1` and stores those within the
2000-key window into `prev`. -/
theorem keyAdvanceLoop_ok (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32)
    (d : ChainEpochDirection) (S : Finset ℕ) (hS : HistRepr F seed S d.prev)
    (hS' : ∀ i ∈ S, i ≤ d.ctr.toNat) (hnext : d.next = nextAt F seed d.ctr.toNat)
    (atN : ℕ) (hc : d.ctr.toNat < atN) (hat : atN + 2000 ≤ 2 ^ 32) :
    ∃ d', d.keyAdvanceLoop (spqrHkdfWith F) (BitVec.ofNat 32 atN) dparams = .ok d' ∧
      d'.ctr.toNat = atN - 1 ∧ d'.next = nextAt F seed (atN - 1) ∧
      HistRepr F seed
        (S ∪ (Finset.Ioo d.ctr.toNat atN).filter fun j => atN ≤ j + 2000) d'.prev :=
  keyAdvanceLoop_aux F seed hseed atN hat (atN - 1 - d.ctr.toNat) d S rfl hS hS' hnext hc

/-- `genAt` reads `secret` only on `[1, e]`. -/
theorem genAt_congr (F : ShaCompress) (authKey : Bytes) (secret secret' : ℕ → Bytes) :
    ∀ e, (∀ i, 1 ≤ i → i ≤ e → secret' i = secret i) →
      genAt F authKey secret' e = genAt F authKey secret e
  | 0, _ => rfl
  | e + 1, hs => by
    have ih := genAt_congr F authKey secret secret' e (fun i h1 hi => hs i h1 (by omega))
    simp only [genAt, ih, hs (e + 1) (by omega) (by omega)]

/-- `ChainOk` depends on `secret` only at epochs `1 ≤ i ≤ currentEpoch`. -/
theorem chainOk_congr (F : ShaCompress) (authKey : Bytes) (dir : Direction) (secret secret' : ℕ → Bytes)
    (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch)
    (hs : ∀ e, 1 ≤ e → e ≤ ch.currentEpoch.toNat → secret' e = secret e) :
    ChainOk F authKey dir secret' sendCtr recvSet ch :=
  { hdir := h.hdir
    hparams := h.hparams
    hsend_le := h.hsend_le
    hroot := by rw [genAt_congr F authKey secret secret' ch.currentEpoch.toNat hs]; exact h.hroot
    hlen := h.hlen
    hsendDir := fun e hlo hhi => by
      simp only [seedAt, genAt_congr F authKey secret secret' e (fun i h1 hi => hs i h1 (by omega))]
      exact h.hsendDir e hlo hhi
    hsendOld := h.hsendOld
    hrecvDir := fun e hlo hhi => by
      simp only [seedAt, genAt_congr F authKey secret secret' e (fun i h1 hi => hs i h1 (by omega))]
      exact h.hrecvDir e hlo hhi
    hfreshSend := h.hfreshSend
    hfreshRecv := h.hfreshRecv }

/-- Key agreement on chain epoch `e`: the `(n + 1)`-th send key on `dir` equals the receive key
at index `n + 1` on `dir.switch`. -/
theorem send_recv_key_eq (F : ShaCompress) (authKey : Bytes) (secret : ℕ → Bytes)
    (dir : Direction) (e n : ℕ) :
    keyAt F (seedAt F authKey secret dir.switch.switch e) (n + 1 - 1) =
      keyAt F (seedAt F authKey secret dir e) n := by
  rw [seedAt_send_recv, Nat.add_sub_cancel]

end LibsignalBinary.Proofs.SpqrV1Sync.ChainSyncBase
