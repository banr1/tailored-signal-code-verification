/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.SizeDefs
import LibsignalBinary.Proofs.SpqrV1Sync.TopSize
import LibsignalBinary.Proofs.SpqrV1Sync.ErasureRoundTrip
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.DecoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.EncoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Assembly
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainDir
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainPrev
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainRecv
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainSmall
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Erasure
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ErasureDecAdd
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ErasureDecMsg
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidSendClosed
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidRecvEk
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidRecvCt
import ProofLib.BV.WidthNorm

/-!
# SPQR V1 Tight State-Size Invariants (`RecvSmallTight`, `DecWFTight`, `BOkTight`)

Tightens the SPQR V1 serialized-state bounds from `SendTotal/`:
1. **Per-link receive history (`RecvSmallTight`)**: `KeyHistory.gc` trims whenever
   `data.length ≥ dparams.trimSize * KEY_SIZE = 2201 * 36 = 79236` down to `≤ 2001 * 36 = 72036`
   bytes, so every stored chain link satisfies `l.recv.prev.data.length ≤ 79236` (tightening
   `RecvSmall`'s `< 2 ^ 20`), bounding a `≤ 3`-link `rawChain` by `3 * 79500 + 32 = 238532` bytes.
2. **Polynomial decoder point sets (`DecWFTight`, `BOkTight`)**: `PolyDecoder.addChunkLoop` pushes
   into polynomial `i` (`nec = necessaryPoints i`) only when `polyIdx < nec ∨ polyPts.len < nec`,
   so the subset of keys `≥ nec` has cardinality `≤ nec` and total cardinality is `≤ 2 * nec ≤ 72`
   (for `ptsNeeded ≤ 576`), bounding `rawPolyDec ≤ 16 * (4 * 72 + 22) = 4960` bytes and
   `rawV1State st.into_pb ≤ 46880` bytes (tightening `st_bSize`'s `≤ 2 ^ 40`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoVerification.SpqrV1Sync.Erasure
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawVN rawChain rawEpochDir rawV1State)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.HMAC (toBEBytes)

/-! ## 1. Tight receive-history invariant `RecvSmallTight` (`≤ 79236 = 2201 * 36`) -/

/-- Every receive history of the chain has at most `2201 * 36 = 79236` bytes. -/
def RecvSmallTight (ch : Chain) : Prop :=
  ∀ l ∈ ch.links, l.recv.prev.data.length ≤ 79236

theorem RecvSmallTight.toRecvSmall {ch : Chain} (h : RecvSmallTight ch) : RecvSmall ch :=
  fun l hl => Nat.lt_of_le_of_lt (h l hl) (by decide)

theorem st_recvSmallVN_tight (F : ShaCompress) {vn : VersionNegotiationPB} {ch : Chain}
    (h : chainFromVersionNegotiation (spqrHkdfWith F) vn = .ok ch) : RecvSmallTight ch := by
  unfold chainFromVersionNegotiation at h
  cases hd : Direction.fromI32? vn.direction with
  | none => simp [hd, bind, Except.bind] at h
  | some d =>
    cases hp : vn.chainParams with
    | none => simp [hd, hp, bind, Except.bind] at h
    | some p =>
      simp only [hd, hp, bind, Except.bind, Chain.new, Except.ok.injEq] at h
      subst h
      intro l hl
      simp only [List.mem_singleton] at hl
      subst hl
      show ([] : Bytes).length ≤ 79236
      decide

theorem st_recvSmallAdd_tight {hkdf : HkdfFn} {ch ch' : Chain} {es : EpochSecret}
    (hs : RecvSmallTight ch) (h : ch.addEpoch hkdf es = .ok ch') : RecvSmallTight ch' := by
  unfold Chain.addEpoch at h
  split_ifs at h
  simp only [Except.ok.injEq] at h
  subst h
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact hs l hl
  · simp only [List.mem_singleton] at hl
    subst hl
    show ([] : Bytes).length ≤ 79236
    decide

private theorem rsst_clearSendNextPrefix (n : ℕ) (xs : List ChainEpoch)
    (hs : ∀ l ∈ xs, l.recv.prev.data.length ≤ 79236) :
    ∀ l ∈ Chain.clearSendNextPrefix n xs, l.recv.prev.data.length ≤ 79236 := by
  induction xs generalizing n with
  | nil => cases n <;> simp [Chain.clearSendNextPrefix]
  | cons x xs ih =>
    cases n with
    | zero => exact hs
    | succ n =>
      intro l hl
      simp only [Chain.clearSendNextPrefix, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact hs x (List.mem_cons_self ..)
      · exact ih n (fun l hl => hs l (List.mem_cons_of_mem _ hl)) l hl

private theorem rsst_set (xs : List ChainEpoch) (i : ℕ) (l' : ChainEpoch)
    (hs : ∀ l ∈ xs, l.recv.prev.data.length ≤ 79236) (h' : l'.recv.prev.data.length ≤ 79236) :
    ∀ l ∈ xs.set i l', l.recv.prev.data.length ≤ 79236 := by
  intro l hl
  rcases List.mem_or_eq_of_mem_set hl with hl | rfl
  · exact hs l hl
  · exact h'

theorem st_recvSmallSend_tight {hkdf : HkdfFn} {ch ch' : Chain} {e : Epoch}
    {out : BitVec 32 × Bytes} (hs : RecvSmallTight ch)
    (h : ch.sendKey hkdf e = .ok (ch', out)) : RecvSmallTight ch' := by
  unfold Chain.sendKey at h
  by_cases hlt : e < ch.sendEpoch
  · simp [hlt] at h
  simp only [hlt, ↓reduceIte] at h
  cases hidx : ch.epochIdx e with
  | error err => simp [hidx, ChainResult.ofError, bind, Except.bind] at h
  | ok idx0 =>
    simp only [hidx, ChainResult.ofError, bind, Except.bind] at h
    by_cases hne : (ch.sendEpoch != e) = true
    · simp only [hne, ↓reduceIte] at h
      have hxs := rsst_clearSendNextPrefix (idx0 - (idx0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
        (ch.links.drop (idx0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
        (fun l hl => hs l (List.mem_of_mem_drop hl))
      split at h
      · cases h
      · rename_i link hlink
        split at h
        · cases h
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact rsst_set _ _ _ hxs (hxs link (List.mem_iff_getElem?.mpr ⟨_, hlink⟩))
    · simp only [hne] at h
      have hxs : ∀ l ∈ ch.links, l.recv.prev.data.length ≤ 79236 := hs
      split at h
      · cases h
      · rename_i link hlink
        split at h
        · cases h
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact rsst_set _ _ _ hxs (hxs link (List.mem_iff_getElem?.mpr ⟨_, hlink⟩))

private def cpt_entry (F : ShaCompress) (seed : Bytes) (j : ℕ) : Bytes :=
  histEntry j (keyAt F seed (j - 1))

private def cpt_data (F : ShaCompress) (seed : Bytes) (L : List ℕ) : Bytes :=
  (L.map (cpt_entry F seed)).flatten

@[simp] private theorem cpt_length_toBEBytes (n : ℕ) {w : ℕ} (x : BitVec w) :
    (toBEBytes n x).length = n := by
  simp [toBEBytes]

@[simp] private theorem cpt_entry_length (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (cpt_entry F seed j).length = 36 := by
  simp [cpt_entry, histEntry, length_keyAt]

private theorem cpt_entry_take4 (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (cpt_entry F seed j).take 4 = toBEBytes 4 (BitVec.ofNat 32 j) := by
  simp [cpt_entry, histEntry]

@[simp] private theorem cpt_data_nil (F : ShaCompress) (seed : Bytes) :
    cpt_data F seed [] = [] := rfl

@[simp] private theorem cpt_data_cons (F : ShaCompress) (seed : Bytes) (x : ℕ) (xs : List ℕ) :
    cpt_data F seed (x :: xs) = cpt_entry F seed x ++ cpt_data F seed xs := rfl

private theorem cpt_data_append (F : ShaCompress) (seed : Bytes) (A B : List ℕ) :
    cpt_data F seed (A ++ B) = cpt_data F seed A ++ cpt_data F seed B := by
  simp [cpt_data, List.map_append, List.flatten_append]

@[simp] private theorem cpt_data_length (F : ShaCompress) (seed : Bytes) (L : List ℕ) :
    (cpt_data F seed L).length = 36 * L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [cpt_data_cons, List.length_append, cpt_entry_length, ih, List.length_cons]
    omega

private theorem cpt_data_drop (F : ShaCompress) (seed : Bytes) :
    ∀ (k : ℕ) (L : List ℕ), (cpt_data F seed L).drop (36 * k) = cpt_data F seed (L.drop k)
  | 0, L => by simp
  | k + 1, [] => by simp
  | k + 1, x :: xs => by
    have h1 : 36 * (k + 1) = (cpt_entry F seed x).length + 36 * k := by
      rw [cpt_entry_length]; omega
    rw [cpt_data_cons, h1, List.drop_append, List.drop_of_length_le (by omega),
      List.nil_append, Nat.add_sub_cancel_left, List.drop_succ_cons]
    exact cpt_data_drop F seed k xs

private theorem cpt_data_take (F : ShaCompress) (seed : Bytes) :
    ∀ (k : ℕ) (L : List ℕ), (cpt_data F seed L).take (36 * k) = cpt_data F seed (L.take k)
  | 0, L => by simp
  | k + 1, [] => by simp
  | k + 1, x :: xs => by
    have h1 : 36 * (k + 1) = (cpt_entry F seed x).length + 36 * k := by
      rw [cpt_entry_length]; omega
    rw [cpt_data_cons, h1, List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, List.take_succ_cons, cpt_data_cons, cpt_data_take F seed k xs]

private theorem cpt_data_drop_take4 (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) :
    ((cpt_data F seed L).drop (36 * k)).take 4 = toBEBytes 4 (BitVec.ofNat 32 L[k]) := by
  rw [cpt_data_drop, List.drop_eq_getElem_cons hk, cpt_data_cons,
    List.take_append_of_le_length (by rw [cpt_entry_length]; omega), cpt_entry_take4]

private def cpt_swapRemove (L : List ℕ) (k : ℕ) : List ℕ :=
  if k + 1 < L.length then
    L.take k ++ L.drop (L.length - 1) ++ (L.take (L.length - 1)).drop (k + 1)
  else
    L.take k

private theorem cpt_swapRemove_length (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (cpt_swapRemove L k).length = L.length - 1 := by
  unfold cpt_swapRemove
  split_ifs with hlt <;> simp <;> omega

private theorem cpt_swapRemove_take (L : List ℕ) (k : ℕ) (_hk : k < L.length) :
    (cpt_swapRemove L k).take k = L.take k := by
  unfold cpt_swapRemove
  split_ifs with hlt
  · rw [List.append_assoc, List.take_left' (by simp; omega)]
  · rw [List.take_take, Nat.min_self]

private theorem cpt_take_succ :
    ∀ (L : List ℕ) (k : ℕ) (_ : k < L.length), L.take (k + 1) = L.take k ++ [L[k]]
  | [], _, hk => by simp at hk
  | _ :: _, 0, _ => rfl
  | _ :: xs, k + 1, hk => by
    simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
    congr 1
    exact cpt_take_succ xs k (Nat.lt_of_succ_lt_succ hk)

private theorem cpt_remove_data (F : ShaCompress) (seed : Bytes) (self : KeyHistory)
    (L : List ℕ) (hdata : self.data = cpt_data F seed L) (k : ℕ) (hk : k < L.length) :
    (self.remove (36 * k) dparams).data = cpt_data F seed (cpt_swapRemove L k) := by
  unfold KeyHistory.remove cpt_swapRemove
  simp only [KeyHistory.KEY_SIZE, hdata, cpt_data_length]
  by_cases hlt : k + 1 < L.length
  · have hlt36 : 36 * k + (4 + 32) < 36 * L.length := by omega
    have hsub : 36 * L.length - (4 + 32) = 36 * (L.length - 1) := by omega
    have hadd : 36 * k + (4 + 32) = 36 * (k + 1) := by omega
    simp only [hlt36, hlt, ↓reduceIte]
    simp only [hsub, hadd, cpt_data_drop, cpt_data_take, ← cpt_data_append]
    congr 1
    apply List.take_of_length_le
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · have hlt36 : ¬ (36 * k + (4 + 32) < 36 * L.length) := by omega
    simp only [hlt36, hlt, ↓reduceIte, cpt_data_take]

private theorem cpt_perm_swapRemove (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    L.Perm (L[k] :: cpt_swapRemove L k) := by
  unfold cpt_swapRemove
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

private theorem cpt_gcLoop_bound (F : ShaCompress) (seed : Bytes) (ctr : BitVec 32)
    (hctr : 2000 ≤ ctr.toNat) :
    ∀ (n : ℕ) (self : KeyHistory) (L : List ℕ) (k : ℕ),
      L.length - k = n →
      k ≤ L.length →
      L.Nodup →
      self.data = cpt_data F seed L →
      (∀ i ∈ L, i ≤ ctr.toNat) →
      (∀ i ∈ L.take k, ctr.toNat ≤ i + 2000) →
      ∀ h',
        KeyHistory.gcLoop self (toBEBytes 4 (ctr - dparams.maxOooKeysOrDefault)) dparams (36 * k) =
          .ok h' →
        h'.data.length ≤ 79236
  | 0, self, L, k, _, _, hNodup, hdata, hle, hkeep, h', hgc => by
    have hkeq : k = L.length := by omega
    subst hkeq
    have hnotlt : ¬ (36 * L.length < self.data.length) := by
      rw [hdata, cpt_data_length]; omega
    rw [KeyHistory.gcLoop] at hgc
    simp only [hnotlt, ↓reduceDIte, Except.ok.injEq] at hgc
    rw [← hgc, hdata, cpt_data_length]
    have hsub : L.toFinset ⊆ Finset.Icc (ctr.toNat - 2000) ctr.toNat := by
      intro i hi
      rw [List.mem_toFinset] at hi
      rw [Finset.mem_Icc]
      have h1 := hle i hi
      have h2 := hkeep i (by rwa [List.take_length])
      omega
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hNodup, Nat.card_Icc] at hcard
    omega
  | n + 1, self, L, k, _, _, hNodup, hdata, hle, hkeep, h', hgc => by
    have hklt : k < L.length := by omega
    have hlt : 36 * k < self.data.length := by rw [hdata, cpt_data_length]; omega
    have hnot4 : ¬ (self.data.length < 36 * k + 4) := by rw [hdata, cpt_data_length]; omega
    have htake4 : (self.data.drop (36 * k)).take 4 = toBEBytes 4 (BitVec.ofNat 32 L[k]) := by
      rw [hdata, cpt_data_drop_take4 F seed L k hklt]
    rw [KeyHistory.gcLoop] at hgc
    simp only [hlt, ↓reduceDIte, hnot4, ↓reduceIte, htake4] at hgc
    by_cases hb : bytesLt (toBEBytes 4 (BitVec.ofNat 32 L[k]))
        (toBEBytes 4 (ctr - dparams.maxOooKeysOrDefault)) = true
    · simp only [hb, ↓reduceIte] at hgc
      have hPerm := cpt_perm_swapRemove L k hklt
      have hNodup' : (cpt_swapRemove L k).Nodup :=
        (List.nodup_cons.mp (hPerm.nodup_iff.mp hNodup)).2
      have hle' : ∀ i ∈ cpt_swapRemove L k, i ≤ ctr.toNat := fun i hi =>
        hle i (hPerm.mem_iff.mpr (List.mem_cons_of_mem L[k] hi))
      have hkeep' : ∀ i ∈ (cpt_swapRemove L k).take k, ctr.toNat ≤ i + 2000 := by
        rw [cpt_swapRemove_take L k hklt]
        exact hkeep
      have hlen' : (cpt_swapRemove L k).length = L.length - 1 :=
        cpt_swapRemove_length L k hklt
      exact cpt_gcLoop_bound F seed ctr hctr n (self.remove (36 * k) dparams)
        (cpt_swapRemove L k) k (by omega) (by omega) hNodup'
        (cpt_remove_data F seed self L hdata k hklt) hle' hkeep' h' hgc
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hgc
      rw [bytesLt_toBEBytes4, decide_eq_true_eq] at hb
      have hLk_le : L[k] ≤ ctr.toNat := hle L[k] (List.getElem_mem hklt)
      have hLk_lt32 : L[k] < 2 ^ 32 := Nat.lt_of_le_of_lt hLk_le ctr.isLt
      have hLkVal : (BitVec.ofNat 32 L[k]).toNat = L[k] := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLk_lt32]
      have hSubVal : (ctr - dparams.maxOooKeysOrDefault).toNat = ctr.toNat - 2000 := by
        rw [dparams_maxOoo, BitVec.toNat_sub_of_le]
        · rfl
        · change (2000#32 : BitVec 32).toNat ≤ ctr.toNat; exact hctr
      rw [hLkVal, hSubVal] at hb
      have hLk_win : ctr.toNat ≤ L[k] + 2000 := by omega
      have hkeep' : ∀ i ∈ L.take (k + 1), ctr.toNat ≤ i + 2000 := by
        rw [cpt_take_succ L k hklt]
        intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact hkeep i hi
        · simp only [List.mem_singleton] at hi
          subst hi
          exact hLk_win
      have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
        simp only [KeyHistory.KEY_SIZE]; omega
      rw [hstep] at hgc
      exact cpt_gcLoop_bound F seed ctr hctr n self L (k + 1) (by omega) (by omega)
        hNodup hdata hle hkeep' h' hgc

private theorem cpt_histRepr_gc_bound (F : ShaCompress) (seed : Bytes) (S : Finset ℕ)
    (h h' : KeyHistory) (hS : HistRepr F seed S h) (ctr : BitVec 32)
    (hS' : ∀ i ∈ S, 1 ≤ i ∧ i ≤ ctr.toNat) (hgc : h.gc ctr dparams = .ok h') :
    h'.data.length ≤ 79236 := by
  rcases hS with ⟨L, hNodup, hFin, hdata⟩
  change h.data = cpt_data F seed L at hdata
  unfold KeyHistory.gc at hgc
  by_cases htrim : h.data.length ≥ dparams.trimSize * KeyHistory.KEY_SIZE
  · simp only [htrim, ↓reduceIte] at hgc
    have hcard : S.card = L.length := by rw [← hFin, List.toFinset_card_of_nodup hNodup]
    have hlen : h.data.length = 36 * S.card := by rw [hdata, cpt_data_length, hcard]
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
    simp only [hnotlt, ↓reduceIte] at hgc
    have hle : ∀ i ∈ L, i ≤ ctr.toNat := fun i hi =>
      (hS' i (hFin ▸ List.mem_toFinset.mpr hi)).2
    exact cpt_gcLoop_bound F seed ctr hctr2000 L.length h L 0 (Nat.sub_zero _) (Nat.zero_le _)
      hNodup hdata hle (by simp) h' hgc
  · simp only [htrim, ↓reduceIte, Except.ok.injEq] at hgc
    rw [← hgc]
    rw [dparams_trimSize, KeyHistory.KEY_SIZE] at htrim
    omega

private theorem cpt_getLoop_length_lt (self : KeyHistory) (atIdx : BitVec 32) (want : Bytes)
    (params : ChainParamsPB) :
    ∀ (n i : ℕ), self.data.length - i ≤ n →
      ∀ self' out, self.getLoop atIdx want params i = .ok (self', out) →
        self'.data.length < self.data.length
  | 0, i, _, _, _, h => by
    have hnot : ¬ (i < self.data.length) := by omega
    rw [KeyHistory.getLoop] at h
    simp [hnot] at h
  | n + 1, i, _, self', out, h => by
    rw [KeyHistory.getLoop] at h
    by_cases hlt : i < self.data.length
    · simp only [hlt, ↓reduceDIte] at h
      split_ifs at h with hbeq
      · injection h with hpair
        injection hpair with hself' _
        rw [← hself']
        exact KeyHistory.remove_length_lt self i params hlt
      · exact cpt_getLoop_length_lt self atIdx want params n (i + KeyHistory.KEY_SIZE)
          (by unfold KeyHistory.KEY_SIZE; omega) self' out h
    · simp [hlt] at h

private theorem cpt_get_length_lt (self self' : KeyHistory) (atIdx currentCtr : BitVec 32)
    (params : ChainParamsPB) (out : Bytes)
    (h : self.get atIdx currentCtr params = .ok (self', out)) :
    self'.data.length < self.data.length := by
  dsimp only [KeyHistory.get] at h
  split_ifs at h
  exact cpt_getLoop_length_lt self atIdx (toBEBytes 4 atIdx) params self.data.length 0
    (Nat.sub_le _ _) self' out h

private theorem cpt_keyAdvanceLoop_bound (hkdf : HkdfFn) (atIdx : BitVec 32) :
    ∀ (n : ℕ) (self self1 : ChainEpochDirection),
      atIdx.toNat - self.ctr.toNat = n →
      self.ctr.toNat < atIdx.toNat →
      self.ctr.toNat + 2000 < 2 ^ 32 →
      self.keyAdvanceLoop hkdf atIdx dparams = .ok self1 →
      atIdx.toNat + 2000 ≤ 2 ^ 32
  | 0, _, _, _, _, _, _ => by omega
  | n + 1, self, self1, _, _, _, hloop => by
    rw [ChainEpochDirection.keyAdvanceLoop] at hloop
    by_cases hstep : self.ctr.toNat + 1 < atIdx.toNat
    · simp only [hstep, ↓reduceDIte] at hloop
      split at hloop
      · contradiction
      · rename_i next' ctr' k hnk
        have hctr' : ctr'.toNat = self.ctr.toNat + 1 :=
          ChainEpochDirection.nextKeyInternal_ctr hkdf self.next next' self.ctr ctr' k hnk
        have hooo : dparams.maxOooKeysOrDefault.toNat = 2000 := by
          rw [dparams_maxOoo]; rfl
        by_cases hc : ctr'.toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
        · simp only [hc, ↓reduceIte] at hloop
          contradiction
        · simp only [hc, ↓reduceIte] at hloop
          exact cpt_keyAdvanceLoop_bound hkdf atIdx n _ self1
            (by dsimp only; omega)
            (by dsimp only; omega)
            (by dsimp only; omega)
            hloop
    · omega

theorem st_recvPrev_tight (F : ShaCompress) {seed : Bytes} {R : Finset ℕ}
    {d d' : ChainEpochDirection} {idx : BitVec 32} {out : Bytes}
    (hseed : seed.length = 32) (h : RecvDirOk F seed R d)
    (hsmall : d.prev.data.length ≤ 79236)
    (hkey : d.key (spqrHkdfWith F) idx dparams = .ok (d', out)) :
    d'.prev.data.length ≤ 79236 := by
  unfold ChainEpochDirection.key at hkey
  by_cases hlt : idx < d.ctr
  · simp only [hlt, ↓reduceIte] at hkey
    rcases hget : d.prev.get idx d.ctr dparams with _ | ⟨prev', out'⟩
    · rw [hget] at hkey; contradiction
    · rw [hget] at hkey
      injection hkey with hpair
      injection hpair with hd' _
      rw [← hd']
      have hlt_len := cpt_get_length_lt d.prev prev' idx d.ctr dparams out' hget
      dsimp only
      omega
  · simp only [hlt, ↓reduceIte] at hkey
    by_cases heq : (idx == d.ctr) = true
    · simp only [heq, ↓reduceIte] at hkey; contradiction
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hkey
      by_cases hjump : idx - d.ctr > dparams.maxJumpOrDefault
      · simp only [hjump, ↓reduceIte] at hkey; contradiction
      · simp only [hjump, ↓reduceIte] at hkey
        by_cases hovf : d.ctr.toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
        · simp only [hovf, ↓reduceIte] at hkey; contradiction
        · simp only [hovf, ↓reduceIte] at hkey
          have hne_ctr : idx ≠ d.ctr := beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr heq)
          have hnot_lt_nat : ¬ (idx.toNat < d.ctr.toNat) := hlt
          have hne_nat : idx.toNat ≠ d.ctr.toNat := fun hnat => hne_ctr (BitVec.eq_of_toNat_eq hnat)
          have hgt_ctr : d.ctr.toNat < idx.toNat := by omega
          have hooo_val : dparams.maxOooKeysOrDefault.toNat = 2000 := by
            rw [dparams_maxOoo]; rfl
          have hovf' : d.ctr.toNat + 2000 < 2 ^ 32 := by omega
          let maxOoo := dparams.maxOooKeysOrDefault
          let self0 : ChainEpochDirection :=
            if idx > d.ctr + maxOoo then { d with prev := d.prev.clear } else d
          change (do
            let self1 ← self0.keyAdvanceLoop (spqrHkdfWith F) idx dparams
            let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr dparams)
            let self2 : ChainEpochDirection := { self1 with prev := prevGc }
            let (next', ctr', (_, outKey)) ←
              ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) self2.next self2.ctr)
            return ({ self2 with next := next', ctr := ctr' }, outKey)) = .ok (d', out) at hkey
          rcases hloop : self0.keyAdvanceLoop (spqrHkdfWith F) idx dparams with _ | self1
          · rw [hloop] at hkey; contradiction
          · rw [hloop] at hkey
            simp only [bind, Except.bind] at hkey
            rcases hgc : self1.prev.gc self1.ctr dparams with _ | prevGc
            · rw [hgc] at hkey; contradiction
            · rw [hgc] at hkey
              simp only [ChainResult.ofPanic] at hkey
              rcases hnk : ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) self1.next self1.ctr with
                _ | ⟨next', ctr', k1, outKey⟩
              · rw [hnk] at hkey; contradiction
              · rw [hnk] at hkey
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hkey
                rcases hkey with ⟨hd', _⟩
                rw [← hd']
                dsimp only
                have hself0_ctr : self0.ctr = d.ctr := by dsimp [self0]; split_ifs <;> rfl
                have hself0_next : self0.next = d.next := by dsimp [self0]; split_ifs <;> rfl
                have hb : idx.toNat + 2000 ≤ 2 ^ 32 :=
                  cpt_keyAdvanceLoop_bound (spqrHkdfWith F) idx (idx.toNat - self0.ctr.toNat)
                    self0 self1 rfl (by rw [hself0_ctr]; exact hgt_ctr)
                    (by rw [hself0_ctr]; exact hovf') hloop
                rcases h.hprev with ⟨S, hS, hS_props, _⟩
                let S0 : Finset ℕ := if idx > d.ctr + maxOoo then ∅ else S
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
                have hidx_bv : BitVec.ofNat 32 idx.toNat = idx := by simp
                rcases keyAdvanceLoop_ok F seed hseed self0 S0 hS0_repr
                    (fun i hi => by rw [hself0_ctr]; exact Nat.le_of_lt (hS0_props i hi).2.1)
                    (by rw [hself0_next, hself0_ctr, h.hnext]) idx.toNat
                    (by rw [hself0_ctr]; exact hgt_ctr) hb with
                  ⟨self1', hloop', hself1_ctr, _, hS1_repr⟩
                rw [hidx_bv, hloop] at hloop'
                injection hloop' with hself1_eq
                subst hself1_eq
                rw [hself0_ctr] at hS1_repr
                let S1 : Finset ℕ := S0 ∪ (Finset.Ioo d.ctr.toNat idx.toNat).filter fun j => idx.toNat ≤ j + 2000
                have hS1_le : ∀ i ∈ S1, 1 ≤ i ∧ i ≤ self1.ctr.toNat := by
                  intro i hi
                  rcases Finset.mem_union.mp hi with hi0 | hiF
                  · have hp := hS0_props i hi0
                    exact ⟨hp.1, by omega⟩
                  · rw [Finset.mem_filter, Finset.mem_Ioo] at hiF
                    omega
                exact cpt_histRepr_gc_bound F seed S1 self1.prev prevGc hS1_repr self1.ctr hS1_le hgc

theorem st_chainRecv_tight (F : ShaCompress) {authKey : Bytes} {dir : Direction}
    {secret : ℕ → Bytes} {sendCtr : ℕ → ℕ} {recvSet : ℕ → Finset ℕ} {ch ch' : Chain}
    {e : Epoch} {idx : BitVec 32} {out : Bytes}
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (hsmall : RecvSmallTight ch)
    (hrecv : ch.recvKey (spqrHkdfWith F) e idx = .ok (ch', out)) :
    ∃ recvSet', ChainOk F authKey dir secret sendCtr recvSet' ch' ∧ RecvSmallTight ch' ∧
      ch'.currentEpoch = ch.currentEpoch ∧ ch'.sendEpoch = ch.sendEpoch := by
  obtain ⟨recvSet', hok', -, hcur', hsend'⟩ :=
    st_chainRecv F (st_recvDir F) (st_recvPrev F) authKey dir secret sendCtr recvSet
      ch ch' e idx out h hsmall.toRecvSmall hrecv
  refine ⟨recvSet', hok', ?_, hcur', hsend'⟩
  unfold Chain.recvKey at hrecv
  by_cases hzero : (e == 0#64 && idx == 0#32) = true
  · simp only [hzero, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hrecv
    rcases hrecv with ⟨rfl, _⟩
    exact hsmall
  · simp only [Bool.not_eq_true] at hzero
    simp only [hzero, Bool.false_eq_true, ↓reduceIte] at hrecv
    cases hep : ch.epochIdx e with
    | error _ => rw [hep] at hrecv; nomatch hrecv
    | ok epochIndex =>
      obtain ⟨hlo, hhi, rfl⟩ := crcv_epochIdx_eq h.hsend_le h.hlen hep
      obtain ⟨link, hlink, hrecvD⟩ := h.hrecvDir e.toNat hlo hhi
      rw [hep] at hrecv
      simp only [ChainResult.ofError, bind, Except.bind, hlink] at hrecv
      cases hkey : link.recv.key (spqrHkdfWith F) idx ch.params with
      | error _ => rw [hkey] at hrecv; nomatch hrecv
      | ok p =>
        rcases p with ⟨recv', out'⟩
        rw [hkey] at hrecv
        cases hrecv
        rw [h.hparams] at hkey
        have hseed := length_seedAt F authKey secret dir.switch e.toNat
        have hlink_mem : link ∈ ch.links := List.mem_of_getElem? hlink
        have hrecv'_tight : recv'.prev.data.length ≤ 79236 :=
          st_recvPrev_tight F hseed hrecvD (hsmall link hlink_mem) hkey
        intro l hl
        rcases List.mem_or_eq_of_mem_set hl with hl_old | rfl
        · exact hsmall l hl_old
        · exact hrecv'_tight

theorem tsz_link_tight_le (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (hsp : SendPrevNil ch)
    (hsmall : RecvSmallTight ch) (l : ChainEpoch) (hmem : l ∈ ch.links) :
    rawEpochDir l.send.intoPb + rawEpochDir l.recv.intoPb + 200 ≤ 79500 := by
  obtain ⟨i, hl⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hl
  have hlen := h.hlen
  have hsle := h.hsend_le
  have he : ch.sendEpoch.toNat - 1 + i ≤ ch.currentEpoch.toNat := by omega
  have hidx : ch.sendEpoch.toNat - 1 + i - (ch.sendEpoch.toNat - 1) = i := by omega
  obtain ⟨l', hl', hrd⟩ := h.hrecvDir (ch.sendEpoch.toNat - 1 + i) (by omega) he
  rw [hidx, hl] at hl'
  obtain rfl := Option.some.inj hl'
  have hrn : l.recv.next.length = 32 := by
    rw [hrd.hnext]
    exact length_nextAt F _ (length_seedAt _ _ _ _ _) _
  have hrp : l.recv.prev.data.length ≤ 79236 := hsmall l hmem
  have hsn : l.send.next.length ≤ 32 := by
    by_cases hse : ch.sendEpoch.toNat ≤ ch.sendEpoch.toNat - 1 + i
    · obtain ⟨l'', hl'', hsd⟩ := h.hsendDir (ch.sendEpoch.toNat - 1 + i) hse he
      rw [hidx, hl] at hl''
      obtain rfl := Option.some.inj hl''
      rw [hsd.hnext, length_nextAt F _ (length_seedAt _ _ _ _ _) _]
    · have hi0 : i = 0 := by omega
      subst hi0
      rw [h.hsendOld l (by omega) hl]
      simp
  have hsp' : l.send.prev.data = [] := hsp l hmem
  show l.send.next.length + l.send.prev.data.length +
      (l.recv.next.length + l.recv.prev.data.length) + 200 ≤ 79500
  rw [hsp', List.length_nil]
  omega

theorem tsz_rawChain_tight_le (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (hsp : SendPrevNil ch)
    (hsmall : RecvSmallTight ch) (hlinks_le : ch.links.length ≤ 3) :
    rawChain ch.intoPb ≤ 238532 := by
  have hroot : ch.nextRoot.length = 32 := by
    rw [h.hroot]
    simp
  have hlinks :
      (ch.links.map (fun l => rawEpochDir l.send.intoPb + rawEpochDir l.recv.intoPb + 200)).sum ≤
        ch.links.length * 79500 := by
    have hsum := List.sum_le_length_nsmul
      (ch.links.map (fun l => rawEpochDir l.send.intoPb + rawEpochDir l.recv.intoPb + 200))
      79500 (fun x hx => by
        rcases List.mem_map.mp hx with ⟨l, hl, rfl⟩
        exact tsz_link_tight_le F authKey dir secret sendCtr recvSet ch h hsp hsmall l hl)
    simpa using hsum
  have heq : rawChain ch.intoPb =
      (ch.links.map (fun l => rawEpochDir l.send.intoPb + rawEpochDir l.recv.intoPb + 200)).sum +
        ch.nextRoot.length := by
    simp only [rawChain, Chain.intoPb, List.map_map, Function.comp_def]
    rfl
  rw [heq, hroot]
  omega

/-! ## 2. Tight polynomial-decoder and braid invariants (`DecWFTight`, `BOkTight`) -/

/-- A `DecWF` polynomial decoder in which each polynomial `j`'s stored keys `≥ necessaryPoints j`
number at most `necessaryPoints j`, bounding total stored points per polynomial by
`2 * necessaryPoints j`. -/
def DecWFTight (n : ℕ) (d : PolyDecoder) : Prop :=
  DecWF n d ∧
    ∀ j (hj : j < d.pts.length),
      (((d.pts[j]).vec.map fun pt => pt.x.value.toNat).toFinset.filter
        (d.necessaryPoints j ≤ ·)).card ≤ d.necessaryPoints j

/-- Arm-by-arm tight decoder conjunct supplementing `BOk`. -/
def DecTightOnly {F : ShaCompress} : St F → Prop
  | .headerSent s => DecWFTight 480 s.receiving_ct1
  | .ekSentCt1Received s => DecWFTight 80 s.receiving_ct2
  | .noHeaderReceived s => DecWFTight 48 s.receiving_hdr
  | .headerReceived s => DecWFTight 576 s.receiving_ek
  | .ct1Sampled s => DecWFTight 576 s.receiving_ek
  | .ct1Acknowledged s => DecWFTight 576 s.receiving_ek
  | _ => True

/-- Tight well-formed braid state (`BOk` + `DecTightOnly`), bounding `rawV1State` by `46880` B. -/
def BOkTight {F : ShaCompress} (st : St F) : Prop :=
  BOk st ∧ DecTightOnly st

private abbrev tbPtKey (pt : Pt) : ℕ := pt.x.value.toNat

private theorem tb_pt_cmp_eq_lt {a b : Pt} : Pt.cmp a b = .lt ↔ tbPtKey a < tbPtKey b := by
  unfold Pt.cmp tbPtKey
  change compareOfLessAndEq a.x.value.toNat b.x.value.toNat = .lt ↔ _
  simp only [compareOfLessAndEq]
  split_ifs <;> simp_all

private theorem tb_pt_cmp_eq_eq {a b : Pt} : Pt.cmp a b = .eq ↔ tbPtKey a = tbPtKey b := by
  unfold Pt.cmp tbPtKey
  change compareOfLessAndEq a.x.value.toNat b.x.value.toNat = .eq ↔ _
  simp only [compareOfLessAndEq]
  split_ifs <;> simp_all
  omega

private theorem tb_pt_cmp_eq_gt {a b : Pt} : Pt.cmp a b = .gt ↔ tbPtKey b < tbPtKey a := by
  unfold Pt.cmp tbPtKey
  change compareOfLessAndEq a.x.value.toNat b.x.value.toNat = .gt ↔ _
  simp only [compareOfLessAndEq]
  split_ifs <;> simp_all <;> omega

private theorem tb_binarySearchAux_spec (target : Pt) (idx : ℕ) (rest : List Pt)
    (hr : (rest.map tbPtKey).Pairwise (· < ·)) :
    (∃ k, ∃ _ : k < rest.length,
      SortedSetPt.binarySearchAux target idx rest = .ok (idx + k) ∧
      tbPtKey rest[k] = tbPtKey target) ∨
    (∃ k, k ≤ rest.length ∧
      SortedSetPt.binarySearchAux target idx rest = .error (idx + k) ∧
      (∀ p ∈ rest.take k, tbPtKey p < tbPtKey target) ∧
      (∀ p ∈ rest.drop k, tbPtKey target < tbPtKey p)) := by
  induction rest generalizing idx with
  | nil =>
    right
    exact ⟨0, Nat.le_refl 0, by simp [SortedSetPt.binarySearchAux], by simp, by simp⟩
  | cons pt tail ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hr
    unfold SortedSetPt.binarySearchAux
    cases hc : Pt.cmp pt target with
    | lt =>
      simp only []
      have hlt : tbPtKey pt < tbPtKey target := tb_pt_cmp_eq_lt.mp hc
      rcases ih (idx + 1) hr.2 with ⟨k, hk, hok, heq⟩ | ⟨k, hk, herr, htake, hdrop⟩
      · left
        refine ⟨k + 1, Nat.succ_lt_succ hk, ?_, ?_⟩
        · rw [hok]; congr 1; omega
        · simpa using heq
      · right
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_, ?_, ?_⟩
        · rw [herr]; congr 1; omega
        · intro p hp
          simp only [List.take_succ_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hlt
          · exact htake p hp
        · intro p hp
          simp only [List.drop_succ_cons] at hp
          exact hdrop p hp
    | eq =>
      simp only []
      have heq : tbPtKey pt = tbPtKey target := tb_pt_cmp_eq_eq.mp hc
      left
      exact ⟨0, by simp, by simp, heq⟩
    | gt =>
      simp only []
      have hgt : tbPtKey target < tbPtKey pt := tb_pt_cmp_eq_gt.mp hc
      right
      refine ⟨0, Nat.zero_le _, by simp, by simp, ?_⟩
      intro p hp
      simp only [List.drop_zero, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hgt
      · exact Nat.lt_trans hgt (hr.1 p hp)

private theorem tb_replace_pairwise (s : SortedSetPt) (el : Pt)
    (hs : (s.vec.map tbPtKey).Pairwise (· < ·)) :
    ((s.replace el).1.vec.map tbPtKey).Pairwise (· < ·) := by
  unfold SortedSetPt.replace SortedSetPt.binarySearch
  rcases tb_binarySearchAux_spec el 0 s.vec hs with ⟨k, hk, hok, heq⟩ | ⟨k, _, herr, htake, hdrop⟩
  · rw [Nat.zero_add] at hok
    simp only [hok]
    have hmap : (s.vec.set k el).map tbPtKey = s.vec.map tbPtKey := by
      apply List.ext_getElem
      · simp
      · intro m hm1 hm2
        simp only [List.getElem_map, List.getElem_set]
        split_ifs with hkm
        · subst hkm; exact heq.symm
        · rfl
    rw [hmap]
    exact hs
  · rw [Nat.zero_add] at herr
    simp only [herr, List.map_append, List.map_cons]
    have hsplit : (s.vec.take k).map tbPtKey ++ (s.vec.drop k).map tbPtKey = s.vec.map tbPtKey := by
      rw [← List.map_append, List.take_append_drop]
    rw [← hsplit] at hs
    rcases List.pairwise_append.mp hs with ⟨hs1, hs2, hs12⟩
    refine List.pairwise_append.mpr ⟨hs1, List.pairwise_cons.mpr ⟨?_, hs2⟩, ?_⟩
    · intro b hb
      rcases List.mem_map.mp hb with ⟨p, hp, rfl⟩
      exact hdrop p hp
    · intro a ha b hb
      rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact htake p hp
      · exact hs12 (tbPtKey p) ha b hb

private theorem tb_replace_mem (s : SortedSetPt) (el : Pt)
    (hs : (s.vec.map tbPtKey).Pairwise (· < ·)) :
    ∀ p ∈ (s.replace el).1.vec, p = el ∨ p ∈ s.vec := by
  unfold SortedSetPt.replace SortedSetPt.binarySearch
  rcases tb_binarySearchAux_spec el 0 s.vec hs with ⟨k, _, hok, _⟩ | ⟨k, _, herr, _, _⟩
  · rw [Nat.zero_add] at hok
    simp only [hok]
    intro p hp
    exact (List.mem_or_eq_of_mem_set hp).symm
  · rw [Nat.zero_add] at herr
    simp only [herr]
    intro p hp
    rcases List.mem_append.mp hp with hp1 | hp2
    · exact Or.inr (List.mem_of_mem_take hp1)
    · rcases List.mem_cons.mp hp2 with rfl | hp3
      · exact Or.inl rfl
      · exact Or.inr (List.mem_of_mem_drop hp3)

private theorem tb_eq_dropLast_append_of_getLast? :
    ∀ {l : List Pt} {last : Pt}, l.getLast? = some last → l = l.dropLast ++ [last]
  | [], _, h => by simp at h
  | [a], last, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h; rfl
  | a :: b :: tl, last, h => by
    have ih := tb_eq_dropLast_append_of_getLast? (l := b :: tl) (by simpa using h)
    simp only [List.dropLast, List.cons_append]
    exact congrArg (a :: ·) ih

private theorem edadd_push_sorted' (s : SortedSetPt) (pt : Pt)
    (hs : (s.vec.map tbPtKey).Pairwise (· < ·)) :
    (((s.push pt).1).vec.map tbPtKey).Pairwise (· < ·) := by
  unfold SortedSetPt.push
  cases hlast : s.vec.getLast? with
  | none => simp
  | some last =>
    simp only
    have hsplit : s.vec = s.vec.dropLast ++ [last] := tb_eq_dropLast_append_of_getLast? hlast
    have hdl : ((s.vec.dropLast ++ [last]).map tbPtKey).Pairwise (· < ·) := hsplit ▸ hs
    rw [List.map_append] at hdl
    rcases List.pairwise_append.mp hdl with ⟨_, _, hdl_lt⟩
    cases hc : Pt.cmp pt last with
    | gt =>
      simp only [List.map_append, List.map_cons, List.map_nil]
      have hgt : tbPtKey last < tbPtKey pt := tb_pt_cmp_eq_gt.mp hc
      refine List.pairwise_append.mpr ⟨hs, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      rw [hsplit, List.mem_map] at ha
      rcases ha with ⟨p, hp, rfl⟩
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact Nat.lt_trans (hdl_lt (tbPtKey p) (List.mem_map_of_mem hp) (tbPtKey last) (by simp)) hgt
      · exact hgt
    | eq =>
      simp only []
      have heq : tbPtKey pt = tbPtKey last := tb_pt_cmp_eq_eq.mp hc
      have hmap : (s.vec.dropLast ++ [pt]).map tbPtKey = s.vec.map tbPtKey := by
        calc (s.vec.dropLast ++ [pt]).map tbPtKey
            = s.vec.dropLast.map tbPtKey ++ [tbPtKey pt] := by simp
          _ = s.vec.dropLast.map tbPtKey ++ [tbPtKey last] := by rw [heq]
          _ = (s.vec.dropLast ++ [last]).map tbPtKey := by simp
          _ = s.vec.map tbPtKey := by rw [← hsplit]
      rw [hmap]
      exact hs
    | lt =>
      simp only []
      exact tb_replace_pairwise s pt hs

private theorem tb_push_mem (s : SortedSetPt) (pt : Pt)
    (hs : (s.vec.map tbPtKey).Pairwise (· < ·)) :
    ∀ p ∈ (s.push pt).1.vec, p = pt ∨ p ∈ s.vec := by
  unfold SortedSetPt.push
  cases hlast : s.vec.getLast? with
  | none =>
    intro p hp
    simp only [List.mem_singleton] at hp
    exact Or.inl hp
  | some last =>
    have hsplit : s.vec = s.vec.dropLast ++ [last] := tb_eq_dropLast_append_of_getLast? hlast
    cases hc : Pt.cmp pt last with
    | gt =>
      intro p hp
      simp only [hc, List.mem_append, List.mem_singleton] at hp
      exact hp.symm
    | eq =>
      intro p hp
      simp only [hc, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact Or.inr (by rw [hsplit]; exact List.mem_append_left _ hp)
      · exact Or.inl rfl
    | lt =>
      simp only [hc]
      exact tb_replace_mem s pt hs

private theorem edadd_push_filter_card (s : SortedSetPt) (pt : Pt) (nec : ℕ)
    (hs : (s.vec.map tbPtKey).Pairwise (· < ·))
    (hcard : ((s.vec.map tbPtKey).toFinset.filter (nec ≤ ·)).card ≤ nec)
    (hcond : tbPtKey pt < nec ∨ s.vec.length < nec) :
    ((((s.push pt).1).vec.map tbPtKey).toFinset.filter (nec ≤ ·)).card ≤ nec := by
  have hsub : (((s.push pt).1).vec.map tbPtKey).toFinset ⊆
      insert (tbPtKey pt) (s.vec.map tbPtKey).toFinset := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    rcases hx with ⟨p, hp, rfl⟩
    rcases tb_push_mem s pt hs p hp with rfl | hp'
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hp'))
  rcases hcond with hlt | hlen
  · have hfsub : ((((s.push pt).1).vec.map tbPtKey).toFinset.filter (nec ≤ ·)) ⊆
        ((s.vec.map tbPtKey).toFinset.filter (nec ≤ ·)) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      rcases Finset.mem_insert.mp (hsub hx.1) with rfl | hx'
      · omega
      · exact ⟨hx', hx.2⟩
    exact (Finset.card_le_card hfsub).trans hcard
  · have hnd : (s.vec.map tbPtKey).Nodup := hs.imp ne_of_lt
    have hscard : (s.vec.map tbPtKey).toFinset.card = s.vec.length := by
      rw [List.toFinset_card_of_nodup hnd, List.length_map]
    have h1 : ((((s.push pt).1).vec.map tbPtKey).toFinset.filter (nec ≤ ·)).card ≤
        (((s.push pt).1).vec.map tbPtKey).toFinset.card :=
      Finset.card_filter_le _ _
    have h2 : (((s.push pt).1).vec.map tbPtKey).toFinset.card ≤
        (insert (tbPtKey pt) (s.vec.map tbPtKey).toFinset).card :=
      Finset.card_le_card hsub
    have h3 : (insert (tbPtKey pt) (s.vec.map tbPtKey).toFinset).card ≤
        (s.vec.map tbPtKey).toFinset.card + 1 :=
      Finset.card_insert_le _ _
    omega

private theorem edadd_set_wf_tight {n : ℕ} {d : PolyDecoder} (hd : DecWFTight n d) (poly : ℕ)
    (s' : SortedSetPt) (hs' : (s'.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·))
    (hcard' : ((s'.vec.map fun pt => pt.x.value.toNat).toFinset.filter
      (d.necessaryPoints poly ≤ ·)).card ≤ d.necessaryPoints poly) :
    DecWFTight n { d with pts := d.pts.set poly s' } := by
  have hlen16 : d.pts.length = 16 := hd.1.2.1
  refine ⟨⟨hd.1.1, by simp [hlen16], fun j hj => ?_⟩, fun j hj => ?_⟩
  · simp only [List.length_set] at hj
    by_cases hjp : poly = j
    · subst hjp
      simp only [List.getElem_set_self]
      exact hs'
    · simp only [List.getElem_set_ne hjp]
      exact hd.1.2.2 j hj
  · simp only [List.length_set] at hj
    have hnec : ({ d with pts := d.pts.set poly s' } : PolyDecoder).necessaryPoints j =
        d.necessaryPoints j := rfl
    rw [hnec]
    by_cases hjp : poly = j
    · subst hjp
      simp only [List.getElem_set_self]
      exact hcard'
    · simp only [List.getElem_set_ne hjp]
      exact hd.2 j hj

private theorem edadd_loop_tight (n : ℕ) (c : Chunk) :
    ∀ (rem i : ℕ), i + rem = 16 → ∀ (d d' : PolyDecoder),
      DecWFTight n d → PolyDecoder.addChunkLoop c i rem d = .ok d' → DecWFTight n d'
  | 0, _, _, d, d', hd, h => by
    simp only [PolyDecoder.addChunkLoop, Except.ok.injEq] at h
    exact h ▸ hd
  | rem + 1, i, hirem, d, d', hd, h => by
    have hi16 : i < 16 := by omega
    have hmod : (c.index.toNat * 16 + i) % 16 = i := by omega
    have hdiv : (c.index.toNat * 16 + i) / 16 = c.index.toNat := by omega
    have hi_lt : i < d.pts.length := by rw [hd.1.2.1]; exact hi16
    have hget? : d.pts[i]? = some (d.pts[i]'hi_lt) := List.getElem?_eq_getElem hi_lt
    unfold PolyDecoder.addChunkLoop at h
    simp only [hmod, hdiv, hget?] at h
    apply edadd_loop_tight n c rem (i + 1) (by omega) _ d' ?_ h
    split
    · next hcond =>
      rw [SortedSetPt.len, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hcond
      have hkey : tbPtKey
          { x := GF16.new (BitVec.ofNat 16 c.index.toNat),
            y := GF16.new (((c.data.get ⟨i * 2 % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 16 <<< 8) +
              (c.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 16) } =
          c.index.toNat := by
        simp [tbPtKey, GF16.new]
      exact edadd_set_wf_tight hd i _
        (edadd_push_sorted' _ _ (hd.1.2.2 i hi_lt))
        (edadd_push_filter_card _ _ (d.necessaryPoints i) (hd.1.2.2 i hi_lt) (hd.2 i hi_lt)
          (by rwa [hkey]))
    · exact hd

theorem st_decFresh_tight (len : ℕ) (heven : len % 2 = 0) :
    ∃ d, PolyDecoder.new len = .ok (.ok d) ∧ DecWFTight (len / 2) d := by
  refine ⟨freshDec len, decoderNew_eq len heven, ⟨rfl, by simp [freshDec], ?_⟩, ?_⟩
  · intro j hj
    simp only [freshDec, List.getElem_replicate, SortedSetPt.new, List.map_nil, List.Pairwise.nil]
  · intro j hj
    have hnil : (freshDec len).pts[j].vec = [] := by
      simp only [freshDec, List.getElem_replicate, SortedSetPt.new]
    rw [hnil]
    simp

theorem st_decAdd_tight {n : ℕ} {d d' : PolyDecoder} {c : Chunk}
    (hd : DecWFTight n d) (hadd : d.addChunk c = .ok d') : DecWFTight n d' :=
  edadd_loop_tight n c 16 0 rfl d d' hd hadd

private theorem tb_authOk_new (F : ShaCompress) (rootKey : Bytes) (ep : Epoch) :
    AuthOk (Authenticator.new F rootKey ep) := by
  unfold AuthOk Authenticator.new Authenticator.update hkdfToVecUnchecked hkdfToSliceUnchecked
  simp [length_hkdfExpand]

theorem st_bInit_tight (F : ShaCompress) {authKey : Bytes} {dir : Direction}
    (_hlen : authKey.length = 32) :
    ∃ st : St F, initStates F authKey dir = .ok st ∧ BOkTight st ∧ phiB st = 0 := by
  cases dir with
  | a2b =>
    refine ⟨.keysUnsampled { uc := { epoch := 1#64, auth := Authenticator.new F authKey 1#64 } },
      ?_, ⟨tb_authOk_new F authKey 1#64, trivial⟩, ?_⟩
    · simp [initStates, St, States.init_a, Chunked.SendEk.KeysUnsampled.new,
        Unchunked.SendEk.KeysUnsampled.new, spqrAuthApi, Bind.bind, Except.bind,
        liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
    · simp [phiB, freshB, States.epoch, Chunked.SendEk.KeysUnsampled.epoch]
  | b2a =>
    obtain ⟨d, hdec, hwf⟩ := st_decFresh_tight (HEADER_SIZE + AUTHENTICATOR_MACSIZE) (by decide)
    have hwf48 : DecWFTight 48 d := by
      simpa [HEADER_SIZE, AUTHENTICATOR_MACSIZE] using hwf
    refine ⟨.noHeaderReceived
        { uc := { epoch := 1#64, auth := Authenticator.new F authKey 1#64 }, receiving_hdr := d },
      ?_, ⟨⟨tb_authOk_new F authKey 1#64, hwf48.1⟩, hwf48⟩, ?_⟩
    · simp [initStates, St, States.init_b, Chunked.SendCt.NoHeaderReceived.new,
        Unchunked.SendCt.NoHeaderReceived.new, spqrPolyApi, spqrAuthApi, hdec, Except.mapError,
        Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
    · simp [phiB, freshB, States.epoch, Chunked.SendCt.NoHeaderReceived.epoch]

private theorem tb_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem tb_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε] {x : Except ε α} {y : α}
    (h : StatesResult.ofPanic x = .ok y) : x = .ok y := by
  cases x with
  | error _ => cases h
  | ok _ => cases h; rfl

theorem st_bSendClosed_tight (F : ShaCompress) (K : MlKem) {st st' : St F}
    {tape tape' : Bytes} {m : Msg} {key : Option EpochSecret} (hbok : BOkTight st)
    (hsend : st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape')) :
    BOkTight st' := by
  refine ⟨st_bSendClosed F K st_encNew st_encNext st st' tape tape' m key hbok.1 hsend, ?_⟩
  cases st with
  | keysUnsampled _ =>
    obtain ⟨_, _, hret⟩ := tb_bind_eq_ok hsend; cases hret; trivial
  | keysSampled _ =>
    obtain ⟨_, _, hret⟩ := tb_bind_eq_ok hsend; cases hret; trivial
  | headerSent state =>
    obtain ⟨⟨state', _⟩, hp, hret⟩ := tb_bind_eq_ok hsend
    cases hret
    obtain ⟨_, _, hret2⟩ := tb_bind_eq_ok (tb_ofPanic_eq_ok hp)
    cases hret2
    exact hbok.2
  | ct1Received _ =>
    obtain ⟨_, _, hret⟩ := tb_bind_eq_ok hsend; cases hret; trivial
  | ekSentCt1Received _ =>
    cases hsend; exact hbok.2
  | noHeaderReceived _ =>
    cases hsend; exact hbok.2
  | headerReceived state =>
    obtain ⟨⟨state', _, _, _⟩, hp, hret⟩ := tb_bind_eq_ok hsend
    cases hret
    obtain ⟨_, _, hrest1⟩ := tb_bind_eq_ok (tb_ofPanic_eq_ok hp)
    obtain ⟨_, _, hrest2⟩ := tb_bind_eq_ok hrest1
    obtain ⟨_, _, hrest3⟩ := tb_bind_eq_ok hrest2
    cases hrest3
    exact hbok.2
  | ct1Sampled state =>
    obtain ⟨⟨state', _⟩, hp, hret⟩ := tb_bind_eq_ok hsend
    cases hret
    obtain ⟨_, _, hret2⟩ := tb_bind_eq_ok (tb_ofPanic_eq_ok hp)
    cases hret2
    exact hbok.2
  | ekReceivedCt1Sampled _ =>
    obtain ⟨_, _, hret⟩ := tb_bind_eq_ok hsend; cases hret; trivial
  | ct1Acknowledged _ =>
    cases hsend; exact hbok.2
  | ct2Sampled _ =>
    obtain ⟨_, _, hret⟩ := tb_bind_eq_ok hsend; cases hret; trivial

private theorem tb_lift_bind {α β : Type} (r : Except SpqrPanic α)
    (f : α → Except StatesPanic β) (y : β) (h : (liftM r >>= f) = .ok y) :
    ∃ x, r = .ok x ∧ f x = .ok y := by
  cases r with
  | error _ => cases h
  | ok x => exact ⟨x, rfl, h⟩

private theorem tb_ofPanic_bind {α β : Type} {ε : Type} [ToStatesPanic ε]
    (r : Except ε α) (f : α → StatesResult β) (y : β)
    (h : (StatesResult.ofPanic r >>= f) = .ok y) :
    ∃ x, r = .ok x ∧ f x = .ok y := by
  cases r with
  | error _ => cases h
  | ok x => exact ⟨x, rfl, h⟩

private theorem tb_expectDecoderNew_tight {site : String} {len half : ℕ} {d : PolyDecoder}
    (hlen : len = 2 * half) (h : expectDecoderNew spqrPolyApi site len = .ok d) :
    DecWFTight half d := by
  obtain ⟨d', hd', hwf⟩ := st_decFresh_tight len (by omega)
  have hdiv : len / 2 = half := by omega
  simp [expectDecoderNew, spqrPolyApi, hd', Except.mapError, bind, Except.bind,
    liftM, monadLift, MonadLift.monadLift, liftSpqrPanic] at h
  exact h ▸ hdiv ▸ hwf

private theorem tb_addChunk_api_tight {n : ℕ} {d d' : PolyDecoder} {c : Chunk}
    (hwf : DecWFTight n d) (h : spqrPolyApi.add_chunk d c = .ok d') :
    DecWFTight n d' := by
  rcases hadd : d.addChunk c with _ | d''
  · simp [spqrPolyApi, hadd, Except.mapError] at h
  · simp [spqrPolyApi, hadd, Except.mapError] at h
    exact h ▸ st_decAdd_tight hwf hadd

private theorem tb_addChunk_ofPanic_tight {n : ℕ} {d d' : PolyDecoder} {c : Chunk}
    (hd : DecWFTight n d) (h : StatesResult.ofPanic (spqrPolyApi.add_chunk d c) = .ok d') :
    DecWFTight n d' :=
  tb_addChunk_api_tight hd (tb_ofPanic_eq_ok h)

theorem st_bRecvEk_tight (F : ShaCompress) (K : MlKem) {st st' : St F} {m : Msg}
    {key : Option EpochSecret} (hek : isEkSide st = true) (hbok : BOkTight st)
    (hrecv : st.recv K m = .ok { key := key, state := st' }) : BOkTight st' := by
  refine ⟨st_bRecvEk F K st_decFresh st_decAdd st_decMsg st_encNew st st' m key hek hbok.1 hrecv,
    ?_⟩
  rcases m with ⟨ep, pl⟩
  cases st with
  | keysUnsampled _ =>
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · injection hrecv with hrecv; injection hrecv with _ hst
      exact hst ▸ hbok.2
  | keysSampled state =>
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · split at hrecv
      · injection hrecv with hrecv; injection hrecv with _ hst
        exact hst ▸ hbok.2
      · cases pl with
        | ct1 chunk =>
          dsimp only [StatesResult.ofPanic, bind, Except.bind] at hrecv
          rcases hstep : state.recv_ct1_chunk ep chunk with _ | s'
          · rw [hstep] at hrecv; cases hrecv
          · rw [hstep] at hrecv
            injection hrecv with hrecv; injection hrecv with _ hst
            subst hst
            unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk at hstep
            split at hstep
            · cases hstep
            · obtain ⟨d0, hd0, hstep⟩ := tb_bind_eq_ok hstep
              obtain ⟨d1, hd1, hstep⟩ := tb_lift_bind _ _ _ hstep
              obtain ⟨_, _, hstep⟩ := tb_bind_eq_ok hstep
              injection hstep with hstep; subst hstep
              exact tb_addChunk_api_tight (tb_expectDecoderNew_tight (half := 480) rfl hd0) hd1
        | _ =>
          injection hrecv with hrecv; injection hrecv with _ hst
          exact hst ▸ hbok.2
  | headerSent state =>
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · split at hrecv
      · injection hrecv with hrecv; injection hrecv with _ hst
        exact hst ▸ hbok.2
      · cases pl with
        | ct1 chunk =>
          dsimp only [StatesResult.ofPanic, bind, Except.bind] at hrecv
          rcases hstep : state.recv_ct1_chunk ep chunk with _ | res
          · rw [hstep] at hrecv; cases hrecv
          · rw [hstep] at hrecv
            unfold Chunked.SendEk.HeaderSent.recv_ct1_chunk at hstep
            split at hstep
            · cases hstep
            · obtain ⟨d1, hd1, hstep⟩ := tb_lift_bind _ _ _ hstep
              have hwf1 := tb_addChunk_api_tight hbok.2 hd1
              obtain ⟨decoded?, _, hstep⟩ := tb_lift_bind _ _ _ hstep
              cases decoded? with
              | none =>
                injection hstep with hstep; subst hstep
                injection hrecv with hrecv; injection hrecv with _ hst
                subst hst; exact hwf1
              | some _ =>
                obtain ⟨_, _, hstep⟩ := tb_bind_eq_ok hstep
                injection hstep with hstep; subst hstep
                injection hrecv with hrecv; injection hrecv with _ hst
                subst hst; trivial
        | _ =>
          injection hrecv with hrecv; injection hrecv with _ hst
          exact hst ▸ hbok.2
  | ct1Received state =>
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · split at hrecv
      · injection hrecv with hrecv; injection hrecv with _ hst
        exact hst ▸ hbok.2
      · cases pl with
        | ct2 chunk =>
          dsimp only [StatesResult.ofPanic, bind, Except.bind] at hrecv
          rcases hstep : state.recv_ct2_chunk ep chunk with _ | s'
          · rw [hstep] at hrecv; cases hrecv
          · rw [hstep] at hrecv
            injection hrecv with hrecv; injection hrecv with _ hst
            subst hst
            unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk at hstep
            split at hstep
            · cases hstep
            · obtain ⟨d0, hd0, hstep⟩ := tb_bind_eq_ok hstep
              obtain ⟨d1, hd1, hstep⟩ := tb_lift_bind _ _ _ hstep
              injection hstep with hstep; subst hstep
              exact tb_addChunk_api_tight (tb_expectDecoderNew_tight (half := 80) rfl hd0) hd1
        | _ =>
          injection hrecv with hrecv; injection hrecv with _ hst
          exact hst ▸ hbok.2
  | ekSentCt1Received state =>
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · split at hrecv
      · injection hrecv with hrecv; injection hrecv with _ hst
        exact hst ▸ hbok.2
      · cases pl with
        | ct2 chunk =>
          dsimp only [bind, Except.bind] at hrecv
          rcases hstep : state.recv_ct2_chunk K ep chunk with _ | res
          · rw [hstep] at hrecv; cases hrecv
          · rw [hstep] at hrecv
            unfold Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at hstep
            split at hstep
            · cases hstep
            · obtain ⟨d1, hd1, hstep⟩ := tb_ofPanic_bind _ _ _ hstep
              have hwf1 := tb_addChunk_api_tight hbok.2 hd1
              obtain ⟨decoded?, _, hstep⟩ := tb_ofPanic_bind _ _ _ hstep
              cases decoded? with
              | none =>
                injection hstep with hstep; subst hstep
                injection hrecv with hrecv; injection hrecv with _ hst
                subst hst; exact hwf1
              | some _ =>
                dsimp only at hstep
                split at hstep
                · cases hstep
                · obtain ⟨_, _, hstep⟩ := tb_bind_eq_ok hstep
                  obtain ⟨dHdr, hdHdr, hstep⟩ := tb_ofPanic_bind _ _ _ hstep
                  injection hstep with hstep; subst hstep
                  injection hrecv with hrecv; injection hrecv with _ hst
                  subst hst
                  exact tb_expectDecoderNew_tight (half := 48) rfl hdHdr
        | _ =>
          injection hrecv with hrecv; injection hrecv with _ hst
          exact hst ▸ hbok.2
  | noHeaderReceived _ | headerReceived _ | ct1Sampled _ | ekReceivedCt1Sampled _
  | ct1Acknowledged _ | ct2Sampled _ => cases hek

theorem st_bRecvCt_tight (F : ShaCompress) (K : MlKem) {st st' : St F} {m : Msg}
    {key : Option EpochSecret} (hside : isEkSide st = false) (hbok : BOkTight st)
    (hrecv : st.recv K m = .ok { key := key, state := st' }) : BOkTight st' := by
  refine ⟨st_bRecvCt F K st_decFresh st_decAdd st_decMsg st_encNew st st' m key hside hbok.1 hrecv,
    ?_⟩
  cases st with
  | keysUnsampled _ | keysSampled _ | headerSent _ | ct1Received _ | ekSentCt1Received _ =>
    cases hside
  | noHeaderReceived state =>
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · split at hrecv
      · simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
        rcases hrecv with ⟨_, rfl⟩; exact hbok.2
      · cases hp : m.payload <;> simp only [hp] at hrecv
        case hdr chunk =>
          cases hr : state.recv_hdr_chunk m.epoch chunk with
          | error _ => simp [hr, bind, Except.bind] at hrecv
          | ok res =>
            simp only [hr, bind, Except.bind] at hrecv
            unfold Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at hr
            split at hr
            · cases hr
            · cases hadd : StatesResult.ofPanic (spqrPolyApi.add_chunk state.receiving_hdr chunk) with
              | error _ => simp [hadd, bind, Except.bind] at hr
              | ok receivingHdr =>
                have hdec' := tb_addChunk_ofPanic_tight hbok.2 hadd
                simp only [hadd, bind, Except.bind] at hr
                cases hdm : StatesResult.ofPanic (spqrPolyApi.decoded_message receivingHdr) with
                | error _ => simp [hdm] at hr
                | ok decoded? =>
                  simp only [hdm] at hr
                  cases decoded? with
                  | none =>
                    simp only [Except.ok.injEq] at hr; subst hr
                    simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
                    rcases hrecv with ⟨_, rfl⟩; exact hdec'
                  | some hdrFull =>
                    dsimp only at hr
                    split at hr
                    · cases hr
                    · obtain ⟨d, hd_new, hd_wf⟩ := st_decFresh_tight ENCAPSULATION_KEY_SIZE (by decide)
                      have hd_api :
                          StatesResult.ofPanic (spqrPolyApi.decoder_new ENCAPSULATION_KEY_SIZE) =
                            .ok (.ok d) := by
                        simp [spqrPolyApi, hd_new, Except.mapError, StatesResult.ofPanic]
                      rw [hd_api] at hr
                      cases hrh : state.uc.recv_header m.epoch (hdrFull.take HEADER_SIZE)
                          (hdrFull.drop HEADER_SIZE) with
                      | error _ => simp [hrh] at hr
                      | ok _ =>
                        simp only [hrh, Except.ok.injEq] at hr; subst hr
                        simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
                        rcases hrecv with ⟨_, rfl⟩; exact hd_wf
        all_goals
          simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
          rcases hrecv with ⟨_, rfl⟩; exact hbok.2
  | headerReceived _ =>
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
      rcases hrecv with ⟨_, rfl⟩; exact hbok.2
  | ct1Sampled state =>
    have hstep_ek : ∀ (chunk : Chunk) (ack : Bool)
        (res : Chunked.SendCt.Ct1SampledRecvChunk spqrPolyApi (spqrAuthApi F)),
        state.recv_ek_chunk K m.epoch chunk ack = .ok res →
        DecTightOnly (F := F) (match res with
          | .stillReceivingStillSending s' => .ct1Sampled s'
          | .stillReceiving s' => .ct1Acknowledged s'
          | .stillSending s' => .ekReceivedCt1Sampled s'
          | .done s' => .ct2Sampled s') := by
      intro chunk ack res hr
      unfold Chunked.SendCt.Ct1Sampled.recv_ek_chunk at hr
      cases hadd : StatesResult.ofPanic (spqrPolyApi.add_chunk state.receiving_ek chunk) with
      | error _ => simp [hadd, bind, Except.bind] at hr
      | ok receivingEk =>
        have hdec' := tb_addChunk_ofPanic_tight hbok.2 hadd
        simp only [hadd, bind, Except.bind] at hr
        cases hdm : StatesResult.ofPanic (spqrPolyApi.decoded_message receivingEk) with
        | error _ => simp [hdm] at hr
        | ok decoded? =>
          simp only [hdm] at hr
          cases decoded? with
          | none =>
            cases ack <;> simp only [↓reduceIte, Bool.false_eq_true, Except.ok.injEq] at hr <;>
              subst hr <;> exact hdec'
          | some decoded =>
            cases hek : state.uc.recv_ek K m.epoch decoded with
            | error _ => simp [hek] at hr
            | ok uc =>
              simp only [hek] at hr
              cases ack with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hr
                subst hr; trivial
              | true =>
                simp only [↓reduceIte] at hr
                cases hs2 : StatesResult.ofPanic (uc.send_ct2 K) with
                | error _ => simp [hs2] at hr
                | ok v =>
                  rcases v with ⟨_, ct2, mac⟩
                  simp only [hs2] at hr
                  cases he2 : StatesResult.ofPanic (Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac) with
                  | error _ => simp [he2] at hr
                  | ok _ =>
                    simp only [he2, Except.ok.injEq] at hr
                    subst hr; trivial
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · split at hrecv
      · simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
        rcases hrecv with ⟨_, rfl⟩; exact hbok.2
      · cases hp : m.payload <;> simp only [hp] at hrecv
        case ek chunk =>
          cases hr : state.recv_ek_chunk K m.epoch chunk false with
          | error _ => simp [hr, bind, Except.bind] at hrecv
          | ok res =>
            have hres := hstep_ek chunk false res hr
            simp only [hr, bind, Except.bind] at hrecv
            cases res <;> simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv <;>
              rcases hrecv with ⟨_, rfl⟩ <;> exact hres
        case ekCt1Ack chunk =>
          cases hr : state.recv_ek_chunk K m.epoch chunk true with
          | error _ => simp [hr, bind, Except.bind] at hrecv
          | ok res =>
            have hres := hstep_ek chunk true res hr
            simp only [hr, bind, Except.bind] at hrecv
            cases res <;> simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv <;>
              rcases hrecv with ⟨_, rfl⟩ <;> exact hres
        all_goals
          simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
          rcases hrecv with ⟨_, rfl⟩; exact hbok.2
  | ekReceivedCt1Sampled state =>
    have hack_ok : ∀ (hr : (do
          let s' ← StatesResult.ofPanic (state.recv_ct1_ack K m.epoch)
          Except.ok ({ key := none, state := .ct2Sampled s' } :
            V1Recv spqrPolyApi (spqrAuthApi F))) = .ok { key := key, state := st' }),
        DecTightOnly st' := by
      intro hr
      cases hr1 : StatesResult.ofPanic (state.recv_ct1_ack K m.epoch) with
      | error _ => simp [hr1, bind, Except.bind] at hr
      | ok _ =>
        simp only [hr1, bind, Except.bind, Except.ok.injEq, V1Recv.mk.injEq] at hr
        rcases hr with ⟨_, rfl⟩; trivial
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · split at hrecv
      · simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
        rcases hrecv with ⟨_, rfl⟩; exact hbok.2
      · cases hp : m.payload <;> simp only [hp] at hrecv
        case ekCt1Ack _ => exact hack_ok hrecv
        case ct1Ack b =>
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, V1Recv.mk.injEq] at hrecv
            rcases hrecv with ⟨_, rfl⟩; exact hbok.2
          · simp only [↓reduceIte] at hrecv
            exact hack_ok hrecv
        all_goals
          simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, V1Recv.mk.injEq] at hrecv
          rcases hrecv with ⟨_, rfl⟩; exact hbok.2
  | ct1Acknowledged state =>
    have hstep_ack : ∀ (chunk : Chunk)
        (res : Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)),
        state.recv_ek_chunk K m.epoch chunk = .ok res →
        DecTightOnly (F := F) (match res with
          | .stillReceiving s' => .ct1Acknowledged s'
          | .done s' => .ct2Sampled s') := by
      intro chunk res hr
      unfold Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at hr
      cases hadd : StatesResult.ofPanic (spqrPolyApi.add_chunk state.receiving_ek chunk) with
      | error _ => simp [hadd, bind, Except.bind] at hr
      | ok receivingEk =>
        have hdec' := tb_addChunk_ofPanic_tight hbok.2 hadd
        simp only [hadd, bind, Except.bind] at hr
        cases hdm : StatesResult.ofPanic (spqrPolyApi.decoded_message receivingEk) with
        | error _ => simp [hdm] at hr
        | ok decoded? =>
          simp only [hdm] at hr
          cases decoded? with
          | none =>
            simp only [Except.ok.injEq] at hr; subst hr; exact hdec'
          | some decoded =>
            cases hek : state.uc.recv_ek K m.epoch decoded with
            | error _ => simp [hek] at hr
            | ok uc =>
              simp only [hek] at hr
              cases hs2 : StatesResult.ofPanic (uc.send_ct2 K) with
              | error _ => simp [hs2] at hr
              | ok v =>
                rcases v with ⟨_, ct2, mac⟩
                simp only [hs2] at hr
                cases he2 : StatesResult.ofPanic (Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac) with
                | error _ => simp [he2] at hr
                | ok _ =>
                  simp only [he2, Except.ok.injEq] at hr
                  subst hr; trivial
    dsimp only [States.recv] at hrecv
    split at hrecv
    · cases hrecv
    · split at hrecv
      · simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
        rcases hrecv with ⟨_, rfl⟩; exact hbok.2
      · cases hp : m.payload <;> simp only [hp] at hrecv
        case ek chunk =>
          cases hr : state.recv_ek_chunk K m.epoch chunk with
          | error _ => simp [hr, bind, Except.bind] at hrecv
          | ok res =>
            have hres := hstep_ack chunk res hr
            simp only [hr, bind, Except.bind] at hrecv
            cases res <;> simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv <;>
              rcases hrecv with ⟨_, rfl⟩ <;> exact hres
        case ekCt1Ack chunk =>
          cases hr : state.recv_ek_chunk K m.epoch chunk with
          | error _ => simp [hr, bind, Except.bind] at hrecv
          | ok res =>
            have hres := hstep_ack chunk res hr
            simp only [hr, bind, Except.bind] at hrecv
            cases res <;> simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv <;>
              rcases hrecv with ⟨_, rfl⟩ <;> exact hres
        all_goals
          simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
          rcases hrecv with ⟨_, rfl⟩; exact hbok.2
  | ct2Sampled state =>
    dsimp only [States.recv] at hrecv
    split at hrecv
    · split at hrecv
      · cases hr : StatesResult.ofPanic (state.recv_next_epoch m.epoch) with
        | error _ => simp [hr, bind, Except.bind] at hrecv
        | ok _ =>
          simp only [hr, bind, Except.bind, Except.ok.injEq, V1Recv.mk.injEq] at hrecv
          rcases hrecv with ⟨_, rfl⟩; trivial
      · cases hrecv
    · simp only [Except.ok.injEq, V1Recv.mk.injEq] at hrecv
      rcases hrecv with ⟨_, rfl⟩; exact hbok.2

/-! ## 3. Tight serialized braid size `st_bSize_tight ≤ 46880` -/

private theorem tbsz_rawAuth_of_authOk (F : ShaCompress) {a : Authenticator} (h : AuthOk a) :
    CryptoVerification.SpqrV1.Top.StateSize.rawAuth ((spqrAuthApi F).into_pb a) = 64 := by
  simp [CryptoVerification.SpqrV1.Top.StateSize.rawAuth, spqrAuthApi, Authenticator.intoPb,
    h.1, h.2]

private theorem tbsz_sum_map_le {α : Type} (l : List α) (f : α → Nat) (B : Nat)
    (h : ∀ x ∈ l, f x ≤ B) : (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_one_mul]
    have hx := h x List.mem_cons_self
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

private theorem tbsz_needed_le {len : Nat} (hlen : len ≤ 1152) (j : Nat) :
    Erasure.needed len j ≤ 1200 := by
  unfold Erasure.needed
  split <;> omega

private theorem tbsz_rawPolyEnc_le {len : Nat} {enc : PolyEncoder}
    (henc : EncWF len enc) (hlen : len ≤ 1152) :
    CryptoVerification.SpqrV1.Top.StateSize.rawPolyEnc (spqrPolyApi.encoder_into_pb enc) ≤ 38752 := by
  rcases henc with ⟨msg, henc, rfl⟩
  rcases enc with ⟨idx, s⟩
  rcases henc with hpts | ⟨polys, hpolys, hlen16, hcoeff⟩
  · simp only at hpts
    subst hpts
    simp only [spqrPolyApi, protoPolyEncoderToPb, PolyEncoder.intoPb,
      CryptoVerification.SpqrV1.Top.StateSize.rawPolyEnc, List.map_nil, List.sum_nil, Nat.add_zero]
    have h1 := tbsz_sum_map_le
      ((Erasure.msgPoints msg).map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value)))
      (fun b => b.length + 22) 2422 ?_
    · rw [List.length_map, Erasure.EncoderCodec.msgPoints_length] at h1
      omega
    · intro b hb
      rcases List.mem_map.1 hb with ⟨pt, hpt, rfl⟩
      rcases List.mem_map.1 hpt with ⟨j, -, rfl⟩
      rw [Erasure.EncoderCodec.flatMap_u16ToBeBytes_length, List.length_map, List.length_range]
      have := tbsz_needed_le hlen j
      omega
  · simp only at hpolys
    subst hpolys
    simp only [spqrPolyApi, protoPolyEncoderToPb, PolyEncoder.intoPb,
      CryptoVerification.SpqrV1.Top.StateSize.rawPolyEnc, List.map_nil, List.sum_nil, Nat.zero_add]
    have h1 := tbsz_sum_map_le (polys.map Poly.serialize) (fun b => b.length + 22) 2422 ?_
    · rw [List.length_map, hlen16] at h1
      omega
    · intro b hb
      rcases List.mem_map.1 hb with ⟨p, hp, rfl⟩
      rcases List.getElem_of_mem hp with ⟨j, hj, rfl⟩
      have hcj := (hcoeff j hj).1
      have hser : (Poly.serialize polys[j]).length = 2 * polys[j].coefficients.length :=
        Erasure.EncoderCodec.flatMap_u16ToBeBytes_length polys[j].coefficients
      have := tbsz_needed_le hlen j
      omega

private theorem tbsz_sortedSetPt_tight_length_le {n : ℕ} {d : PolyDecoder}
    (hd : DecWFTight n d) (hn : n ≤ 576) (j : ℕ) (hj : j < d.pts.length) :
    d.pts[j].vec.length ≤ 72 := by
  let S := (d.pts[j].vec.map fun pt => pt.x.value.toNat).toFinset
  have hnec : d.necessaryPoints j ≤ 36 := by
    unfold PolyDecoder.necessaryPoints
    rw [hd.1.1]
    dsimp only
    split_ifs <;> omega
  have hsub_union : S ⊆ S.filter (· < d.necessaryPoints j) ∪ S.filter (d.necessaryPoints j ≤ ·) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hlt : x < d.necessaryPoints j
    · exact Or.inl ⟨hx, hlt⟩
    · exact Or.inr ⟨hx, by omega⟩
  have hsub_range : S.filter (· < d.necessaryPoints j) ⊆ Finset.range (d.necessaryPoints j) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact hx.2
  have hlt_card : (S.filter (· < d.necessaryPoints j)).card ≤ d.necessaryPoints j := by
    have hc := Finset.card_le_card hsub_range
    rwa [Finset.card_range] at hc
  have hge_card : (S.filter (d.necessaryPoints j ≤ ·)).card ≤ d.necessaryPoints j := hd.2 j hj
  have htot_card : S.card ≤
      (S.filter (· < d.necessaryPoints j)).card + (S.filter (d.necessaryPoints j ≤ ·)).card :=
    (Finset.card_le_card hsub_union).trans (Finset.card_union_le _ _)
  have hnd : (d.pts[j].vec.map fun pt => pt.x.value.toNat).Nodup := (hd.1.2.2 j hj).imp ne_of_lt
  have hlen : d.pts[j].vec.length = S.card := by
    dsimp [S]
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  omega

private theorem tbsz_rawPolyDec_tight_le {n : ℕ} {dec : PolyDecoder}
    (hdec : DecWFTight n dec) (hn : n ≤ 576) :
    CryptoVerification.SpqrV1.Top.StateSize.rawPolyDec (spqrPolyApi.decoder_into_pb dec) ≤ 4960 := by
  simp only [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb,
    CryptoVerification.SpqrV1.Top.StateSize.rawPolyDec]
  have h1 := tbsz_sum_map_le (dec.pts.map (fun s => s.vec.flatMap Pt.serialize))
    (fun b => b.length + 22) 310 ?_
  · rw [List.length_map, hdec.1.2.1] at h1
    omega
  · intro b hb
    rcases List.mem_map.1 hb with ⟨s, hs, rfl⟩
    rcases List.getElem_of_mem hs with ⟨j, hj, rfl⟩
    have hlen := tbsz_sortedSetPt_tight_length_le hdec hn j hj
    have hser := Erasure.DecoderCodec.length_flatMap_serialize dec.pts[j].vec
    omega

/-- Tight serialized braid size bound: on any `BOkTight` state, `rawV1State st.into_pb ≤ 46880`
(attained on `ct1Sampled`: `64 + 64 + 2080 + 960 + 38752 + 4960 = 46880` B). -/
theorem st_bSize_tight (F : ShaCompress) (st : St F) (h : BOkTight st) :
    rawV1State st.into_pb ≤ 46880 := by
  rcases h with ⟨hbok, htight⟩
  cases st with
  | keysUnsampled s =>
    have hauth := tbsz_rawAuth_of_authOk F hbok
    simp only [States.into_pb, Chunked.SendEk.KeysUnsampled.into_pb,
      Unchunked.SendEk.KeysUnsampled.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChKeysUnsampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcKeysUnsampled,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth]
    decide
  | keysSampled s =>
    rcases hbok with ⟨ha, ⟨hdk, hek⟩, henc⟩
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hencLe := tbsz_rawPolyEnc_le henc (by decide)
    simp only [States.into_pb, Chunked.SendEk.KeysSampled.into_pb,
      Unchunked.SendEk.HeaderSent.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChKeysSampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcHeaderSent,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, hdk, hek,
      DECAPSULATION_KEY_SIZE, ENCAPSULATION_KEY_SIZE]
    omega
  | headerSent s =>
    rcases hbok with ⟨ha, hdk, henc, _⟩
    have hdk : s.uc.dk.length = DECAPSULATION_KEY_SIZE := hdk
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hencLe := tbsz_rawPolyEnc_le henc (by decide)
    have hdecLe := tbsz_rawPolyDec_tight_le htight (by decide)
    simp only [States.into_pb, Chunked.SendEk.HeaderSent.into_pb,
      Unchunked.SendEk.EkSent.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChHeaderSent,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcEkSent,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, hdk,
      DECAPSULATION_KEY_SIZE]
    omega
  | ct1Received s =>
    rcases hbok with ⟨ha, ⟨hdk, hct1⟩, henc⟩
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hencLe := tbsz_rawPolyEnc_le henc (by decide)
    simp only [States.into_pb, Chunked.SendEk.Ct1Received.into_pb,
      Unchunked.SendEk.EkSentCt1Received.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChCt1Received,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcEkSentCt1Received,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, hdk, hct1,
      DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE]
    omega
  | ekSentCt1Received s =>
    rcases hbok with ⟨ha, ⟨hdk, hct1⟩, _⟩
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hdecLe := tbsz_rawPolyDec_tight_le htight (by decide)
    simp only [States.into_pb, Chunked.SendEk.EkSentCt1Received.into_pb,
      Unchunked.SendEk.EkSentCt1Received.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChEkSentCt1Received,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcEkSentCt1Received,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, hdk, hct1,
      DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE]
    omega
  | noHeaderReceived s =>
    rcases hbok with ⟨ha, _⟩
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hdecLe := tbsz_rawPolyDec_tight_le htight (by decide)
    simp only [States.into_pb, Chunked.SendCt.NoHeaderReceived.into_pb,
      Unchunked.SendCt.NoHeaderReceived.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChNoHeaderReceived,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcNoHeaderReceived,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth]
    omega
  | headerReceived s =>
    rcases hbok with ⟨ha, hhdr, _⟩
    have hhdr : s.uc.hdr.length = HEADER_SIZE := hhdr
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hdecLe := tbsz_rawPolyDec_tight_le htight (by decide)
    simp only [States.into_pb, Chunked.SendCt.HeaderReceived.into_pb,
      Unchunked.SendCt.HeaderReceived.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChHeaderReceived,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcHeaderReceived,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, hhdr, HEADER_SIZE]
    omega
  | ct1Sampled s =>
    rcases hbok with ⟨ha, ⟨hhdr, hes, hct1⟩, henc, _⟩
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hencLe := tbsz_rawPolyEnc_le henc (by decide)
    have hdecLe := tbsz_rawPolyDec_tight_le htight (by decide)
    simp only [States.into_pb, Chunked.SendCt.Ct1Sampled.into_pb,
      Unchunked.SendCt.Ct1Sent.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChCt1Sampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcCt1Sent,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, hhdr, hes, hct1,
      HEADER_SIZE, ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE]
    omega
  | ekReceivedCt1Sampled s =>
    rcases hbok with ⟨ha, ⟨hes, hct1, hek⟩, henc⟩
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hencLe := tbsz_rawPolyEnc_le henc (by decide)
    simp only [States.into_pb, Chunked.SendCt.EkReceivedCt1Sampled.into_pb,
      Unchunked.SendCt.Ct1SentEkReceived.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChEkReceivedCt1Sampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcCt1SentEkReceived,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, hes, hct1, hek,
      ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE, ENCAPSULATION_KEY_SIZE]
    omega
  | ct1Acknowledged s =>
    rcases hbok with ⟨ha, ⟨hhdr, hes, hct1⟩, _⟩
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hdecLe := tbsz_rawPolyDec_tight_le htight (by decide)
    simp only [States.into_pb, Chunked.SendCt.Ct1Acknowledged.into_pb,
      Unchunked.SendCt.Ct1Sent.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChCt1Acknowledged,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcCt1Sent,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, hhdr, hes, hct1,
      HEADER_SIZE, ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE]
    omega
  | ct2Sampled s =>
    rcases hbok with ⟨ha, henc⟩
    have hauth := tbsz_rawAuth_of_authOk F ha
    have hencLe := tbsz_rawPolyEnc_le henc (by decide)
    simp only [States.into_pb, Chunked.SendCt.Ct2Sampled.into_pb,
      Unchunked.SendCt.Ct2Sent.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChCt2Sampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcCt2Sent,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth]
    omega

end CryptoVerification.SpqrV1Sync.SendTotal
