/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Proofs.SpqrV1Sync.ChainSync
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

set_option autoImplicit false

/-!
# Receive-History Size Bound Under Key Lookup

Proves that `ChainEpochDirection.key` preserves `prev.data.length < 2 ^ 20` (`st_recvPrev`):
backward lookups swap-remove an entry, while forward lookups garbage-collect above `2201 * 36`
bytes down to at most `2001` entries (`≤ 72036` bytes).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.HMAC (toBEBytes)

private def cprev_encList (F : ShaCompress) (seed : Bytes) (L : List ℕ) : Bytes :=
  (L.map fun j => histEntry j (keyAt F seed (j - 1))).flatten

private theorem cprev_toBEBytes4_eq (x : BitVec 32) :
    toBEBytes 4 x =
      [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] := by
  simp [toBEBytes, List.ofFn_succ]

private theorem cprev_length_entry (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (histEntry j (keyAt F seed (j - 1))).length = 36 := by
  simp [histEntry, cprev_toBEBytes4_eq]

private theorem cprev_length_encList (F : ShaCompress) (seed : Bytes) :
    ∀ L : List ℕ, (cprev_encList F seed L).length = 36 * L.length
  | [] => rfl
  | x :: xs => by
    simp only [cprev_encList, List.map_cons, List.flatten_cons, List.length_append,
      cprev_length_entry, List.length_cons]
    have ih := cprev_length_encList F seed xs
    simp only [cprev_encList] at ih
    omega

private theorem cprev_encList_append (F : ShaCompress) (seed : Bytes) (L1 L2 : List ℕ) :
    cprev_encList F seed (L1 ++ L2) = cprev_encList F seed L1 ++ cprev_encList F seed L2 := by
  simp [cprev_encList]

private theorem cprev_encList_take (F : ShaCompress) (seed : Bytes) :
    ∀ (k : ℕ) (L : List ℕ), (cprev_encList F seed L).take (36 * k) = cprev_encList F seed (L.take k)
  | 0, _ => rfl
  | k + 1, [] => rfl
  | k + 1, x :: xs => by
    have hlen : (histEntry x (keyAt F seed (x - 1))).length = 36 := cprev_length_entry F seed x
    simp only [cprev_encList, List.map_cons, List.flatten_cons, List.take_succ_cons]
    rw [List.take_append, hlen, List.take_of_length_le (by rw [hlen]; omega),
      show 36 * (k + 1) - 36 = 36 * k by omega]
    exact congrArg (histEntry x (keyAt F seed (x - 1)) ++ ·) (cprev_encList_take F seed k xs)

private theorem cprev_encList_drop (F : ShaCompress) (seed : Bytes) :
    ∀ (k : ℕ) (L : List ℕ), (cprev_encList F seed L).drop (36 * k) = cprev_encList F seed (L.drop k)
  | 0, _ => rfl
  | k + 1, [] => rfl
  | k + 1, x :: xs => by
    have hlen : (histEntry x (keyAt F seed (x - 1))).length = 36 := cprev_length_entry F seed x
    simp only [cprev_encList, List.map_cons, List.flatten_cons]
    rw [List.drop_append, hlen, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show 36 * (k + 1) - 36 = 36 * k by omega]
    exact cprev_encList_drop F seed k xs

private theorem cprev_encList_tag (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) :
    ((cprev_encList F seed L).drop (36 * k)).take 4 = toBEBytes 4 (BitVec.ofNat 32 L[k]) := by
  rw [cprev_encList_drop, List.drop_eq_getElem_cons hk]
  simp only [cprev_encList, List.map_cons, List.flatten_cons, histEntry, List.append_assoc,
    cprev_toBEBytes4_eq]
  rfl

private def cprev_swapRemoveIdx (L : List ℕ) (k : ℕ) : List ℕ :=
  if k + 1 < L.length then
    L.take k ++ L.drop (L.length - 1) ++ (L.take (L.length - 1)).drop (k + 1)
  else
    L.take k

private theorem cprev_swapRemoveIdx_perm (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    List.Perm (L[k] :: cprev_swapRemoveIdx L k) L := by
  unfold cprev_swapRemoveIdx
  split_ifs with hk1
  · let n := L.length - 1
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

private theorem cprev_length_swapRemoveIdx (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (cprev_swapRemoveIdx L k).length = L.length - 1 := by
  have hp := (cprev_swapRemoveIdx_perm L k hk).length_eq
  simp only [List.length_cons] at hp
  omega

private theorem cprev_swapRemoveIdx_take (L : List ℕ) (k : ℕ) :
    (cprev_swapRemoveIdx L k).take k = L.take k := by
  unfold cprev_swapRemoveIdx
  split_ifs with hk1
  · rw [List.append_assoc, List.take_append_of_le_length (by simp; omega), List.take_take,
      Nat.min_self]
  · rw [List.take_take, Nat.min_self]

private theorem cprev_encList_remove (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) (params : ChainParamsPB) :
    ({ data := cprev_encList F seed L } : KeyHistory).remove (36 * k) params =
      { data := cprev_encList F seed (cprev_swapRemoveIdx L k) } := by
  unfold KeyHistory.remove cprev_swapRemoveIdx
  simp only [KeyHistory.KEY_SIZE, cprev_length_encList]
  by_cases hk1 : k + 1 < L.length
  · have hlt : 36 * k + (4 + 32) < 36 * L.length := by omega
    simp only [hlt, hk1, ↓reduceIte]
    have hnewEnd : 36 * L.length - (4 + 32) = 36 * (L.length - 1) := by omega
    have hidx1 : 36 * k + (4 + 32) = 36 * (k + 1) := by omega
    rw [hnewEnd, hidx1, cprev_encList_take, cprev_encList_take, cprev_encList_drop,
      cprev_encList_drop, ← cprev_encList_append, ← cprev_encList_append]
    congr 1
    apply List.take_of_length_le
    rw [cprev_length_encList]
    have hlen_sr := cprev_length_swapRemoveIdx L k hk
    unfold cprev_swapRemoveIdx at hlen_sr
    simp only [hk1, ↓reduceIte] at hlen_sr
    rw [hlen_sr]
  · have hnlt : ¬ (36 * k + (4 + 32) < 36 * L.length) := by omega
    simp only [hnlt, hk1, ↓reduceIte, cprev_encList_take]

private theorem cprev_gcLoop_bound (F : ShaCompress) (seed : Bytes) (horizon : BitVec 32)
    (hiBound : ℕ) (hhi32 : hiBound < 2 ^ 32) :
    ∀ (n : ℕ) (L : List ℕ) (k : ℕ),
      L.length - k ≤ n →
      L.Nodup →
      (∀ x ∈ L, x ≤ hiBound) →
      (∀ x ∈ L.take k, horizon.toNat ≤ x) →
      ∀ prevGc,
        KeyHistory.gcLoop { data := cprev_encList F seed L } (toBEBytes 4 horizon) dparams (36 * k) =
          .ok prevGc →
        ∃ L' : List ℕ, prevGc.data = cprev_encList F seed L' ∧ L'.Nodup ∧
          ∀ x ∈ L', horizon.toNat ≤ x ∧ x ≤ hiBound
  | 0, L, k, hle, hnodup, hhi, hpre, prevGc, hgc => by
    have hnlt : ¬ (36 * k < (cprev_encList F seed L).length) := by
      rw [cprev_length_encList]; omega
    rw [KeyHistory.gcLoop, dite_eq_right hnlt] at hgc
    injection hgc with hgc_eq
    subst hgc_eq
    have htake : L.take k = L := List.take_of_length_le (by omega)
    rw [htake] at hpre
    exact ⟨L, rfl, hnodup, fun x hx => ⟨hpre x hx, hhi x hx⟩⟩
  | n + 1, L, k, hle, hnodup, hhi, hpre, prevGc, hgc => by
    by_cases hk : k < L.length
    · have hk_bytes : 36 * k < (cprev_encList F seed L).length := by
        rw [cprev_length_encList]; omega
      have hnslice : ¬ ((cprev_encList F seed L).length < 36 * k + 4) := by
        rw [cprev_length_encList]; omega
      have hLk_le : L[k] ≤ hiBound := hhi L[k] (List.getElem_mem hk)
      rw [KeyHistory.gcLoop, dite_eq_left hk_bytes, ite_eq_right hnslice] at hgc
      dsimp only at hgc
      rw [cprev_encList_tag F seed L k hk, bytesLt_toBEBytes4] at hgc
      have hLk_toNat : (BitVec.ofNat 32 L[k]).toNat = L[k] := by
        simp only [BitVec.toNat_ofNat]; omega
      rw [hLk_toNat] at hgc
      by_cases hlt_hor : L[k] < horizon.toNat
      · simp only [hlt_hor, decide_true, ↓reduceIte, cprev_encList_remove F seed L k hk dparams] at hgc
        have hp := cprev_swapRemoveIdx_perm L k hk
        have hnodup' : (cprev_swapRemoveIdx L k).Nodup :=
          (List.nodup_cons.mp (hp.nodup_iff.mpr hnodup)).2
        have hlen' : (cprev_swapRemoveIdx L k).length = L.length - 1 :=
          cprev_length_swapRemoveIdx L k hk
        have hhi' : ∀ x ∈ cprev_swapRemoveIdx L k, x ≤ hiBound := fun x hx =>
          hhi x (hp.subset (List.mem_cons_of_mem _ hx))
        have hpre' : ∀ x ∈ (cprev_swapRemoveIdx L k).take k, horizon.toNat ≤ x := by
          rw [cprev_swapRemoveIdx_take L k]
          exact hpre
        exact cprev_gcLoop_bound F seed horizon hiBound hhi32 n (cprev_swapRemoveIdx L k) k
          (by omega) hnodup' hhi' hpre' prevGc hgc
      · simp only [hlt_hor, decide_false, Bool.false_eq_true, ↓reduceIte] at hgc
        have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
          simp only [KeyHistory.KEY_SIZE]; omega
        rw [hstep] at hgc
        have hpre' : ∀ x ∈ L.take (k + 1), horizon.toNat ≤ x := by
          rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
          intro x hx
          rcases List.mem_append.mp hx with hxk | hxeq
          · exact hpre x hxk
          · simp only [List.mem_singleton] at hxeq
            omega
        exact cprev_gcLoop_bound F seed horizon hiBound hhi32 n L (k + 1) (by omega)
          hnodup hhi hpre' prevGc hgc
    · have hnlt : ¬ (36 * k < (cprev_encList F seed L).length) := by
        rw [cprev_length_encList]; omega
      rw [KeyHistory.gcLoop, dite_eq_right hnlt] at hgc
      injection hgc with hgc_eq
      subst hgc_eq
      have htake : L.take k = L := List.take_of_length_le (by omega)
      rw [htake] at hpre
      exact ⟨L, rfl, hnodup, fun x hx => ⟨hpre x hx, hhi x hx⟩⟩

private theorem cprev_getLoop_length_lt (self : KeyHistory) (atIdx : BitVec 32) (want : Bytes)
    (params : ChainParamsPB) (i : Nat) (prev' : KeyHistory) (out : Bytes)
    (h : KeyHistory.getLoop self atIdx want params i = .ok (prev', out)) :
    prev'.data.length < self.data.length := by
  rw [KeyHistory.getLoop] at h
  by_cases hi : i < self.data.length
  · rw [dite_eq_left hi] at h
    by_cases hmatch : ((self.data.drop i).take 4 == want) = true
    · rw [ite_eq_left hmatch] at h
      injection h with hpair
      injection hpair with hprev _
      subst hprev
      exact KeyHistory.remove_length_lt self i params hi
    · rw [ite_eq_right hmatch] at h
      exact cprev_getLoop_length_lt self atIdx want params (i + KeyHistory.KEY_SIZE) prev' out h
  · rw [dite_eq_right hi] at h
    cases h
termination_by self.data.length - i
decreasing_by
  simp only [KeyHistory.KEY_SIZE]; omega

private theorem cprev_keyAdvanceLoop_bound (hkdf : HkdfFn) (atIdx : BitVec 32)
    (s1 : ChainEpochDirection) :
    ∀ (n : ℕ) (s : ChainEpochDirection),
      atIdx.toNat - s.ctr.toNat ≤ n →
      ChainEpochDirection.keyAdvanceLoop hkdf s atIdx dparams = .ok s1 →
      s.ctr.toNat < atIdx.toNat →
      s.ctr.toNat + 2000 < 2 ^ 32 →
      atIdx.toNat + 2000 ≤ 2 ^ 32
  | 0, s, hrem, _, hlo, _ => by omega
  | n + 1, s, hrem, h, hlo, hc => by
    rw [ChainEpochDirection.keyAdvanceLoop] at h
    by_cases hlt1 : s.ctr.toNat + 1 < atIdx.toNat
    · rw [dite_eq_left hlt1] at h
      split at h
      · cases h
      · rename_i next' ctr' k hnk
        have hctr' : ctr'.toNat = s.ctr.toNat + 1 :=
          ChainEpochDirection.nextKeyInternal_ctr hkdf s.next next' s.ctr ctr' k hnk
        dsimp only at h
        by_cases hov : ctr'.toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hov] at h; cases h
        · rw [ite_eq_right hov] at h
          have hc' : ctr'.toNat + 2000 < 2 ^ 32 := by
            rw [dparams_maxOoo] at hov
            simp only [BitVec.toNat_ofNat] at hov
            omega
          exact cprev_keyAdvanceLoop_bound hkdf atIdx s1 n _
            (by dsimp only; omega) h (by dsimp only; omega) (by dsimp only; exact hc')
    · omega

/-- Any successful `ChainEpochDirection.key` on a `RecvDirOk` direction preserves
`prev.data.length < 2 ^ 20`. -/
theorem st_recvPrev (F : ShaCompress) : RecvPrevStmt F := by
  intro seed R d d' idx out hseed hok hprev_lt hkey
  unfold ChainEpochDirection.key at hkey
  by_cases hlt : idx < d.ctr
  · rw [ite_eq_left hlt] at hkey
    cases hget : d.prev.get idx d.ctr dparams with
    | error e =>
      simp only [hget, bind, Except.bind] at hkey
      cases hkey
    | ok res =>
      rcases res with ⟨prev', out0⟩
      simp only [hget, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hkey
      rcases hkey with ⟨hd', _⟩
      subst hd'
      unfold KeyHistory.get at hget
      dsimp only at hget
      by_cases hal : (d.prev.data.length % KeyHistory.KEY_SIZE != 0) = true
      · rw [ite_eq_left hal] at hget; cases hget
      · rw [ite_eq_right hal] at hget
        by_cases hovf : idx.toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hovf] at hget; cases hget
        · rw [ite_eq_right hovf] at hget
          by_cases htrim_if : idx + dparams.maxOooKeysOrDefault < d.ctr
          · rw [ite_eq_left htrim_if] at hget; cases hget
          · rw [ite_eq_right htrim_if] at hget
            have hshr := cprev_getLoop_length_lt d.prev idx (toBEBytes 4 idx) dparams 0 prev' out0 hget
            dsimp only
            omega
  · rw [ite_eq_right hlt] at hkey
    by_cases heq : (idx == d.ctr) = true
    · rw [ite_eq_left heq] at hkey; cases hkey
    · rw [ite_eq_right heq] at hkey
      have hne_bv : idx ≠ d.ctr := by
        intro h; subst h; simp at heq
      have hgt : d.ctr.toNat < idx.toNat := by
        simp only [BitVec.lt_def] at hlt
        have : idx.toNat ≠ d.ctr.toNat := fun h => hne_bv (BitVec.eq_of_toNat_eq h)
        omega
      by_cases hjmp : idx - d.ctr > dparams.maxJumpOrDefault
      · rw [ite_eq_left hjmp] at hkey; cases hkey
      · rw [ite_eq_right hjmp] at hkey
        dsimp only at hkey
        by_cases hov : d.ctr.toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hov] at hkey; cases hkey
        · rw [ite_eq_right hov] at hkey
          have hctr_ov : d.ctr.toNat + 2000 < 2 ^ 32 := by
            rw [dparams_maxOoo] at hov
            simp only [BitVec.toNat_ofNat] at hov
            omega
          set self0 : ChainEpochDirection :=
            if idx > d.ctr + dparams.maxOooKeysOrDefault then
              { d with prev := d.prev.clear }
            else d
          have hself0_ctr : self0.ctr = d.ctr := by
            dsimp [self0]; split_ifs <;> rfl
          have hself0_next : self0.next = nextAt F seed self0.ctr.toNat := by
            rw [hself0_ctr]
            have : self0.next = d.next := by dsimp [self0]; split_ifs <;> rfl
            rw [this, hok.hnext]
          have hself0_prev : ∃ S₀ : Finset ℕ, HistRepr F seed S₀ self0.prev ∧
              ∀ i ∈ S₀, i ≤ self0.ctr.toNat := by
            dsimp [self0]
            split_ifs
            · exact ⟨∅, histRepr_empty F seed, by simp⟩
            · obtain ⟨S, hS, hS_props, _⟩ := hok.hprev
              exact ⟨S, hS, fun i hi => Nat.le_of_lt (hS_props i hi).2.1⟩
          obtain ⟨S₀, hS₀, hS₀_le⟩ := hself0_prev
          simp only [bind, Except.bind] at hkey
          cases hadv : ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith F) self0 idx dparams with
          | error e =>
            rw [hadv] at hkey
            cases hkey
          | ok self1 =>
            rw [hadv] at hkey
            dsimp only at hkey
            cases hgc : self1.prev.gc self1.ctr dparams with
            | error p =>
              rw [hgc] at hkey
              cases hkey
            | ok prevGc =>
              rw [hgc] at hkey
              dsimp only [ChainResult.ofPanic] at hkey
              cases hnk : ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) self1.next self1.ctr with
              | error p =>
                rw [hnk] at hkey
                cases hkey
              | ok nkRes =>
                rcases nkRes with ⟨next', ctr', ⟨_, outKey⟩⟩
                rw [hnk] at hkey
                simp only [pure, Except.pure, Except.ok.injEq,
                  Prod.mk.injEq] at hkey
                rcases hkey with ⟨hd', _⟩
                subst hd'
                dsimp only
                have hat : idx.toNat + 2000 ≤ 2 ^ 32 :=
                  cprev_keyAdvanceLoop_bound (spqrHkdfWith F) idx self1
                    (idx.toNat - self0.ctr.toNat) self0 (Nat.le_refl _) hadv
                    (by rw [hself0_ctr]; exact hgt) (by rw [hself0_ctr]; exact hctr_ov)
                obtain ⟨d₁, hadv_ok, hd1_ctr, _, hrepr1⟩ :=
                  keyAdvanceLoop_ok F seed hseed self0 S₀ hS₀ hS₀_le hself0_next idx.toNat
                    (by rw [hself0_ctr]; exact hgt) hat
                have hidx_bv : BitVec.ofNat 32 idx.toNat = idx := BitVec.eq_of_toNat_eq (by simp)
                rw [hidx_bv] at hadv_ok
                rw [hadv] at hadv_ok
                injection hadv_ok with hself1_eq
                subst hself1_eq
                unfold KeyHistory.gc at hgc
                by_cases htrim : self1.prev.data.length ≥ dparams.trimSize * KeyHistory.KEY_SIZE
                · rw [ite_eq_left htrim] at hgc
                  dsimp only at hgc
                  by_cases hunder : self1.ctr < dparams.maxOooKeysOrDefault
                  · rw [ite_eq_left hunder] at hgc; cases hgc
                  · rw [ite_eq_right hunder] at hgc
                    have hctr1_ge : 2000 ≤ self1.ctr.toNat := by
                      rw [dparams_maxOoo] at hunder
                      simp only [BitVec.lt_def, BitVec.toNat_ofNat] at hunder
                      omega
                    rcases hrepr1 with ⟨L, hLnodup, hLfin, hdata⟩
                    have hh_eq : self1.prev = { data := cprev_encList F seed L } := by
                      rcases hp : self1.prev with ⟨ddata⟩
                      have hdata' : ddata = cprev_encList F seed L := by
                        simpa [hp, cprev_encList] using hdata
                      rw [hdata']
                    have hL_le : ∀ x ∈ L, x ≤ self1.ctr.toNat := by
                      intro x hx
                      have hx_mem : x ∈ S₀ ∪ (Finset.Ioo self0.ctr.toNat idx.toNat).filter
                          (fun j => idx.toNat ≤ j + 2000) := hLfin ▸ List.mem_toFinset.mpr hx
                      rcases Finset.mem_union.mp hx_mem with hx0 | hx1
                      · have := hS₀_le x hx0
                        rw [hself0_ctr] at this
                        omega
                      · rw [Finset.mem_filter, Finset.mem_Ioo] at hx1
                        omega
                    rw [hh_eq] at hgc
                    change KeyHistory.gcLoop { data := cprev_encList F seed L }
                      (toBEBytes 4 (self1.ctr - dparams.maxOooKeysOrDefault)) dparams (36 * 0) =
                      .ok prevGc at hgc
                    have htake0 : ∀ x ∈ L.take 0,
                        (self1.ctr - dparams.maxOooKeysOrDefault).toNat ≤ x := by
                      intro x hx; cases hx
                    obtain ⟨L', hdata', hL'nodup, hL'bounds⟩ :=
                      cprev_gcLoop_bound F seed (self1.ctr - dparams.maxOooKeysOrDefault)
                        self1.ctr.toNat self1.ctr.isLt L.length L 0 (by omega)
                        hLnodup hL_le htake0 prevGc hgc
                    have hhor_eq : (self1.ctr - dparams.maxOooKeysOrDefault).toNat =
                        self1.ctr.toNat - 2000 := by
                      rw [dparams_maxOoo, BitVec.toNat_sub_of_le]
                      · simp only [BitVec.toNat_ofNat]
                      · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
                    have hsub_icc : L'.toFinset ⊆
                        Finset.Icc (self1.ctr.toNat - 2000) self1.ctr.toNat := by
                      intro x hx
                      rw [List.mem_toFinset] at hx
                      obtain ⟨hlo', hhi'⟩ := hL'bounds x hx
                      rw [hhor_eq] at hlo'
                      exact Finset.mem_Icc.mpr ⟨hlo', hhi'⟩
                    have hcard_le : L'.length ≤ 2001 := by
                      rw [← List.toFinset_card_of_nodup hL'nodup]
                      have hc := Finset.card_le_card hsub_icc
                      rw [Nat.card_Icc] at hc
                      omega
                    rw [hdata', cprev_length_encList]
                    omega
                · rw [ite_eq_right htrim] at hgc
                  injection hgc with hgc_eq
                  subst hgc_eq
                  rw [dparams_trimSize] at htrim
                  simp only [KeyHistory.KEY_SIZE] at htrim
                  omega

end CryptoVerification.SpqrV1Sync.SendTotal
