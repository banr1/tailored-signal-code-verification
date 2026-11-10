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
# Receive-Direction Key Lookup Under Arbitrary Indices

Proves that any successful `ChainEpochDirection.key` call on an honest `RecvDirOk` direction yields
a fresh positive message index, returns `keyAt seed (idx - 1)`, and preserves `RecvDirOk`
(`st_recvDir`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.HMAC (toBEBytes)

private def cdir_encList (F : ShaCompress) (seed : Bytes) (L : List ℕ) : Bytes :=
  (L.map fun j => histEntry j (keyAt F seed (j - 1))).flatten

private theorem cdir_toBEBytes4_eq (x : BitVec 32) :
    toBEBytes 4 x =
      [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] := by
  simp [toBEBytes, List.ofFn_succ]

private theorem cdir_length_entry (F : ShaCompress) (seed : Bytes) (j : ℕ) :
    (histEntry j (keyAt F seed (j - 1))).length = 36 := by
  simp [histEntry, cdir_toBEBytes4_eq]

private theorem cdir_length_encList (F : ShaCompress) (seed : Bytes) :
    ∀ L : List ℕ, (cdir_encList F seed L).length = 36 * L.length
  | [] => rfl
  | x :: xs => by
    simp only [cdir_encList, List.map_cons, List.flatten_cons, List.length_append,
      cdir_length_entry, List.length_cons]
    have ih := cdir_length_encList F seed xs
    simp only [cdir_encList] at ih
    omega

private theorem cdir_encList_drop (F : ShaCompress) (seed : Bytes) :
    ∀ (k : ℕ) (L : List ℕ), (cdir_encList F seed L).drop (36 * k) = cdir_encList F seed (L.drop k)
  | 0, _ => rfl
  | k + 1, [] => rfl
  | k + 1, x :: xs => by
    have hlen : (histEntry x (keyAt F seed (x - 1))).length = 36 := cdir_length_entry F seed x
    simp only [cdir_encList, List.map_cons, List.flatten_cons]
    rw [List.drop_append, hlen, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show 36 * (k + 1) - 36 = 36 * k by omega]
    exact cdir_encList_drop F seed k xs

private theorem cdir_encList_tag (F : ShaCompress) (seed : Bytes) (L : List ℕ) (k : ℕ)
    (hk : k < L.length) :
    ((cdir_encList F seed L).drop (36 * k)).take 4 = toBEBytes 4 (BitVec.ofNat 32 L[k]) := by
  rw [cdir_encList_drop, List.drop_eq_getElem_cons hk]
  simp only [cdir_encList, List.map_cons, List.flatten_cons, histEntry, List.append_assoc,
    cdir_toBEBytes4_eq]
  rfl

private theorem cdir_getLoop_not_mem (F : ShaCompress) (seed : Bytes) (L : List ℕ)
    (hlt : ∀ x ∈ L, x < 2 ^ 32) (idx : BitVec 32) (hnot : ∀ x ∈ L, x ≠ idx.toNat) :
    ∀ (rem k : ℕ), L.length - k = rem →
      KeyHistory.getLoop { data := cdir_encList F seed L } idx (toBEBytes 4 idx) dparams (36 * k) =
        .error (.err (.keyAlreadyRequested idx))
  | 0, k, hrem => by
    have hnlt : ¬ (36 * k < (cdir_encList F seed L).length) := by
      rw [cdir_length_encList]; omega
    rw [KeyHistory.getLoop, dite_eq_right hnlt]
  | rem + 1, k, hrem => by
    have hk : k < L.length := by omega
    have hk_bytes : 36 * k < (cdir_encList F seed L).length := by
      rw [cdir_length_encList]; omega
    have hLk_mem : L[k] ∈ L := List.getElem_mem hk
    have hLk32 : L[k] < 2 ^ 32 := hlt L[k] hLk_mem
    have hne : L[k] ≠ idx.toNat := hnot L[k] hLk_mem
    have hbeq : (toBEBytes 4 (BitVec.ofNat 32 L[k]) == toBEBytes 4 idx) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbytes
      have hbv := toBEBytes4_injective hbytes
      have hnat : (BitVec.ofNat 32 L[k]).toNat = idx.toNat := congrArg BitVec.toNat hbv
      simp only [BitVec.toNat_ofNat] at hnat
      omega
    rw [KeyHistory.getLoop, dite_eq_left hk_bytes, cdir_encList_tag F seed L k hk, hbeq]
    dsimp only [Bool.false_eq_true, ↓reduceIte]
    have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
      simp only [KeyHistory.KEY_SIZE]; omega
    rw [hstep]
    exact cdir_getLoop_not_mem F seed L hlt idx hnot rem (k + 1) (by omega)

private theorem cdir_keyAdvanceLoop_bound (hkdf : HkdfFn) (atIdx : BitVec 32)
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
          exact cdir_keyAdvanceLoop_bound hkdf atIdx s1 n _
            (by dsimp only; omega) h (by dsimp only; omega) (by dsimp only; exact hc')
    · omega

/-- Any successful `ChainEpochDirection.key` on a `RecvDirOk` direction returns the honest key at a
fresh index `idx ≥ 1` and preserves `RecvDirOk` for `insert idx.toNat R`. -/
theorem st_recvDir (F : ShaCompress) : RecvDirStmt F := by
  intro seed R d d' idx out hseed hok hkey
  have hkey_save := hkey
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
      rcases hkey with ⟨hd', rfl⟩
      have hlt_nat : idx.toNat < d.ctr.toNat := by simpa [BitVec.lt_def] using hlt
      have hget' := hget
      unfold KeyHistory.get at hget'
      dsimp only at hget'
      by_cases hal : (d.prev.data.length % KeyHistory.KEY_SIZE != 0) = true
      · rw [ite_eq_left hal] at hget'; cases hget'
      · rw [ite_eq_right hal] at hget'
        by_cases hovf : idx.toNat + dparams.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hovf] at hget'; cases hget'
        · rw [ite_eq_right hovf] at hget'
          by_cases htrim_if : idx + dparams.maxOooKeysOrDefault < d.ctr
          · rw [ite_eq_left htrim_if] at hget'; cases hget'
          · rw [ite_eq_right htrim_if] at hget'
            have hjb : idx.toNat + 2000 < 2 ^ 32 := by
              rw [dparams_maxOoo] at hovf
              simp only [BitVec.toNat_ofNat] at hovf
              omega
            have hctr_le : d.ctr.toNat ≤ idx.toNat + 2000 := by
              rw [dparams_maxOoo] at htrim_if
              simp only [BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_ofNat] at htrim_if
              omega
            obtain ⟨S, hS, hS_props, hS_comp⟩ := hok.hprev
            have hltS : ∀ i ∈ S, i < 2 ^ 32 := by
              intro i hi
              have := (hS_props i hi).2.1
              have := d.ctr.isLt
              omega
            have hjS : idx.toNat ∈ S := by
              by_contra hnotS
              rcases hS with ⟨L, _, hLfin, hdata⟩
              have hh_eq : d.prev = { data := cdir_encList F seed L } := by
                rcases hp : d.prev with ⟨ddata⟩
                have hdata' : ddata = cdir_encList F seed L := by
                  simpa [hp, cdir_encList] using hdata
                rw [hdata']
              have hLlt : ∀ x ∈ L, x < 2 ^ 32 := fun x hx =>
                hltS x (hLfin ▸ List.mem_toFinset.mpr hx)
              have hLnot : ∀ x ∈ L, x ≠ idx.toNat := by
                intro x hx heq
                exact hnotS (heq ▸ hLfin ▸ List.mem_toFinset.mpr hx)
              have herr := cdir_getLoop_not_mem F seed L hLlt idx hLnot L.length 0 (Nat.sub_zero _)
              rw [hh_eq] at hget'
              change KeyHistory.getLoop { data := cdir_encList F seed L } idx (toBEBytes 4 idx)
                dparams (36 * 0) = .ok (prev', out0) at hget'
              rw [herr] at hget'
              cases hget'
            obtain ⟨h1, _, hnotR⟩ := hS_props idx.toNat hjS
            obtain ⟨h', hget_ok, hrepr'⟩ :=
              histRepr_get F seed S d.prev hS hltS idx.toNat hjS d.ctr hjb hctr_le
            have hidx_bv : BitVec.ofNat 32 idx.toNat = idx := BitVec.eq_of_toNat_eq (by simp)
            rw [hidx_bv] at hget_ok
            rw [hget] at hget_ok
            injection hget_ok with hpair
            injection hpair with hprev_eq hout_eq
            subst hprev_eq
            subst hd'
            refine ⟨hnotR, h1, hout_eq, ?_⟩
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro j hj
              rcases Finset.mem_insert.mp hj with rfl | hjR
              · exact h1
              · exact hok.hpos j hjR
            · dsimp only
              have hctr_eq := hok.hctr
              rw [Finset.sup_insert, id_eq, hctr_eq]
              have hle_sup : idx.toNat ≤ R.sup id := by omega
              exact (Nat.max_eq_right hle_sup).symm
            · exact hok.hnext
            · refine ⟨S.erase idx.toNat, hrepr', ?_, ?_⟩
              · intro j hj
                rw [Finset.mem_erase] at hj
                obtain ⟨hj1, hjlt, hjnotR⟩ := hS_props j hj.2
                refine ⟨hj1, hjlt, ?_⟩
                simp [Finset.mem_insert, hj.1, hjnotR]
              · intro j hj1 hjlt hjnotIns hjwin
                rw [Finset.mem_insert, not_or] at hjnotIns
                rw [Finset.mem_erase]
                exact ⟨hjnotIns.1, hS_comp j hj1 hjlt hjnotIns.2 hjwin⟩
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
          have hjump_le : idx.toNat - d.ctr.toNat ≤ 25000 := by
            rw [dparams_maxJump] at hjmp
            have := idx.isLt
            simp only [gt_iff_lt, BitVec.lt_def, BitVec.toNat_sub_of_le (Nat.le_of_lt hgt),
              BitVec.toNat_ofNat] at hjmp
            omega
          set self0 : ChainEpochDirection :=
            if idx > d.ctr + dparams.maxOooKeysOrDefault then
              { d with prev := d.prev.clear }
            else d
          have hself0_ctr : self0.ctr = d.ctr := by
            dsimp [self0]; split_ifs <;> rfl
          simp only [bind, Except.bind] at hkey
          cases hadv : ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith F) self0 idx dparams with
          | error e =>
            rw [hadv] at hkey
            cases hkey
          | ok self1 =>
            have hb : idx.toNat + 2000 ≤ 2 ^ 32 :=
              cdir_keyAdvanceLoop_bound (spqrHkdfWith F) idx self1 (idx.toNat - self0.ctr.toNat)
                self0 (Nat.le_refl _) hadv (by rw [hself0_ctr]; exact hgt)
                (by rw [hself0_ctr]; exact hctr_ov)
            have hidx1 : 1 ≤ idx.toNat := by omega
            have hnew : idx.toNat ∉ R := by
              intro hmem
              have hle : idx.toNat ≤ R.sup id := Finset.le_sup (f := id) hmem
              rw [← hok.hctr] at hle
              omega
            have hjump : R.sup id < idx.toNat → idx.toNat - R.sup id ≤ 25000 := by
              intro _
              rw [← hok.hctr]
              exact hjump_le
            have htrim : idx.toNat < R.sup id → R.sup id ≤ idx.toNat + 2000 := by
              rw [← hok.hctr]
              intro hlt'; omega
            have hR : R.sup id + 2000 ≤ 2 ^ 32 := by
              rw [← hok.hctr]; omega
            obtain ⟨d₁, hkey_ok, hok₁⟩ :=
              recvDir_key F seed hseed R d hok idx.toNat hidx1 hnew hjump htrim hb hR
            have hidx_bv : BitVec.ofNat 32 idx.toNat = idx := BitVec.eq_of_toNat_eq (by simp)
            rw [hidx_bv] at hkey_ok
            rw [hkey_save] at hkey_ok
            injection hkey_ok with hpair
            injection hpair with hd1 hout1
            subst hd1
            exact ⟨hnew, hidx1, hout1, hok₁⟩

end CryptoVerification.SpqrV1Sync.SendTotal
