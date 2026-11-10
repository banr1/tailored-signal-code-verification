/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.ModelProofs.AdvanceAndFrame
public import Symbolic.Proofs.Refinement.Composed.Cli.Model

/-!
# Receiver-Chain Erasure and Execution Inversion Lemmas

Defines erased receiver chains (`eraseRecvChain`, `recChainOfErased`) and proves execution
inversion lemmas for `findReceiverChainKey`, `takeSkippedKey`, and `advanceChain` followed by
`setReceiverChainKey`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Proofs.libsignal.RngG.CliPure.R3

open DY DY.Libsignal DY.Libsignal.Rust
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement
open DY.Libsignal.Composed.Refinement (vec32)
open CryptoGames.LibsignalSession (ChainKey MessageKeyGenerator ReceiverChain PublicKey RatchetState
  TripleRatchet Mut maxMessageKeys ShaCompress)
open CryptoVerification.SessionModel (chainStepN skippedKeys)
open CryptoVerification.SessionModel.AdvanceAndFrame

theorem vec32_toList_of_length_eq {b : HwBytes} (hLen : b.length = 32) :
    (vec32 b).toList = b := by
  change (b ++ List.replicate 32 0).take 32 = b
  rw [List.take_append_of_le_length (Nat.le_of_eq hLen.symm),
      List.take_of_length_le (Nat.le_of_eq hLen)]

theorem publicKey_ext_bytes_toList {pk1 pk2 : PublicKey}
    (h : pk1.bytes.toList = pk2.bytes.toList) : pk1 = pk2 := by
  rcases pk1 with ⟨⟨l1, hl1⟩⟩
  rcases pk2 with ⟨⟨l2, hl2⟩⟩
  cases h
  rfl

theorem publicKey_eq_vec32_of_toList_eq {pk : PublicKey} {b : HwBytes}
    (h : pk.bytes.toList = b) :
    pk = ⟨vec32 b⟩ ∧ b.length = 32 := by
  have hLen : b.length = 32 := by
    rw [← h]
    exact pk.bytes.toList_length
  refine ⟨publicKey_ext_bytes_toList ?_, hLen⟩
  rw [h, vec32_toList_of_length_eq hLen]

/-- Clears cached `messageKeys` from a `ReceiverChain`. -/
def eraseRecvChain (rc : ReceiverChain) : ReceiverChain :=
  { rc with messageKeys := [] }

@[simp] theorem eraseRecvChain_idem (rc : ReceiverChain) :
    eraseRecvChain (eraseRecvChain rc) = eraseRecvChain rc := rfl

@[simp] theorem eraseRecvChain_senderRatchetKey (rc : ReceiverChain) :
    (eraseRecvChain rc).senderRatchetKey = rc.senderRatchetKey := rfl

@[simp] theorem eraseRecvChain_chainKey (rc : ReceiverChain) :
    (eraseRecvChain rc).chainKey = rc.chainKey := rfl

theorem findReceiverChainKey_ok_some
    (r : RatchetState) (their : PublicKey) (ck : ChainKey)
    (hFind : r.findReceiverChainKey their = .ok (some ck)) :
    ∃ ci : Nat, ∃ rc : ReceiverChain,
      r.findReceiverChainIndex their = some ci ∧
      r.receiverChains[ci]? = some rc ∧
      rc.senderRatchetKey = their ∧
      rc.chainKey = some ck := by
  unfold RatchetState.findReceiverChainKey at hFind
  cases hci : r.findReceiverChainIndex their with
  | none =>
    rw [hci] at hFind
    cases hFind
  | some ci =>
    obtain ⟨rc, hrc, hsrk_b⟩ := getElem?_of_findReceiverChainIndex r their ci hci
    have hsrk : rc.senderRatchetKey = their := beq_iff_eq.mp hsrk_b
    rw [hci] at hFind
    dsimp only at hFind
    rw [hrc] at hFind
    dsimp only at hFind
    cases hck : rc.chainKey with
    | none =>
      rw [hck] at hFind
      cases hFind
    | some ck' =>
      rw [hck] at hFind
      injection hFind with hOpt
      injection hOpt with hEq
      subst hEq
      exact ⟨ci, rc, rfl, hrc, hsrk, hck⟩

theorem findReceiverChainKey_ok_none
    (r : RatchetState) (their : PublicKey)
    (hFind : r.findReceiverChainKey their = .ok none) :
    r.findReceiverChainIndex their = none := by
  unfold RatchetState.findReceiverChainKey at hFind
  cases hci : r.findReceiverChainIndex their with
  | none => rfl
  | some ci =>
    rw [hci] at hFind
    dsimp only at hFind
    cases hrc : r.receiverChains[ci]? with
    | none =>
      rw [hrc] at hFind
      cases hFind
    | some rc =>
      rw [hrc] at hFind
      dsimp only at hFind
      cases hck : rc.chainKey with
      | none =>
        rw [hck] at hFind
        cases hFind
      | some ck' =>
        rw [hck] at hFind
        cases hFind

private theorem extractLsb'_zero_bytesToKey32_cons' (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons' (b : BitVec 8) (acc : BitVec 256) (j : ℕ)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32' (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h32 : j < 32) :
    (CryptoGames.HKDF.bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [CryptoGames.HKDF.bytesToKey32] using
        extractLsb'_zero_bytesToKey32_cons' b (CryptoGames.HKDF.bytesToKey32 rest)
    | succ j =>
      have hcons : CryptoGames.HKDF.bytesToKey32 (b :: rest) =
          (CryptoGames.HKDF.bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons' b (CryptoGames.HKDF.bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem bytesToKey32_keyToBytes32' (k : BitVec 256) :
    CryptoGames.HKDF.bytesToKey32 (CryptoGames.HMAC.keyToBytes32 k) = k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToKey32' (CryptoGames.HMAC.keyToBytes32 k) (i / 8)
      (by simp [CryptoGames.HMAC.keyToBytes32, hj]) hj)
  simp only [CryptoGames.HMAC.keyToBytes32, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr,
    decide_true, Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem keyToBytes32_inj' {a b : BitVec 256}
    (h : CryptoGames.HMAC.keyToBytes32 a = CryptoGames.HMAC.keyToBytes32 b) : a = b := by
  rw [← bytesToKey32_keyToBytes32' a, h, bytesToKey32_keyToBytes32']

/-- Record representation of an erased receiver chain. -/
def recChainOfErased (rc : ReceiverChain) : ChainRec :=
  { senderRatchetKey := rc.senderRatchetKey.serialize
    senderRatchetKeyPrivate := []
    chainKey := rc.chainKey.map fun ck => (ck.index, CryptoGames.HMAC.keyToBytes32 ck.key)
    messageKeys := [] }

theorem recChainOfErased_inj {a b : ReceiverChain}
    (h : recChainOfErased a = recChainOfErased b) :
    eraseRecvChain a = eraseRecvChain b := by
  rcases a with ⟨pa, ca, ma⟩
  rcases b with ⟨pb, cb, mb⟩
  unfold recChainOfErased at h
  dsimp only at h
  injection h with hp _ hc _
  have hpk : pa = pb := by
    apply publicKey_ext_bytes_toList
    simpa [PublicKey.serialize] using hp
  have hck : ca = cb := by
    cases ca with
    | none =>
      cases cb with
      | none => rfl
      | some _ => simp at hc
    | some ka =>
      cases cb with
      | none => simp at hc
      | some kb =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨hidx, hkey⟩ := hc
        rcases ka with ⟨ka1, ka2⟩
        rcases kb with ⟨kb1, kb2⟩
        dsimp only at hidx hkey
        rw [keyToBytes32_inj' hkey, hidx]
  subst hpk; subst hck
  rfl

theorem map_erase_eq_of_map_recChainOfErased {l1 l2 : List ReceiverChain}
    (h : (l1.map eraseRecvChain).map recChainOfErased = (l2.map eraseRecvChain).map recChainOfErased) :
    l1.map eraseRecvChain = l2.map eraseRecvChain := by
  induction l1 generalizing l2 with
  | nil => cases l2 with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a t ih =>
    cases l2 with
    | nil => simp at h
    | cons b u =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      obtain ⟨hab, htu⟩ := h
      refine ⟨?_, ih htu⟩
      have := recChainOfErased_inj hab
      simpa using this

theorem map_eraseRecvChain_set_messageKeys
    (rcs : List ReceiverChain) (ci : Nat) (ch : ReceiverChain)
    (mks : List MessageKeyGenerator) (hch : rcs[ci]? = some ch) :
    (rcs.set ci { ch with messageKeys := mks }).map eraseRecvChain = rcs.map eraseRecvChain := by
  exact map_set_of_eq eraseRecvChain rcs ci { ch with messageKeys := mks } ⟨ch, hch, rfl⟩

theorem takeSkippedKey_ok_some_inv
    {their : PublicKey} {counter : BitVec 32} {r1 r2 : RatchetState} {mkGen : MessageKeyGenerator}
    (hTake : Mut.exec (RatchetState.takeSkippedKey their counter) r1 = (.ok (some mkGen), r2)) :
    ∃ ci : Nat, ∃ ch : ReceiverChain, ∃ pos : Nat,
      r1.findReceiverChainIndex their = some ci ∧
      r1.receiverChains[ci]? = some ch ∧
      ch.senderRatchetKey = their ∧
      ch.messageKeys.findIdx? (fun mk => mk.counter == counter) = some pos ∧
      ch.messageKeys[pos]? = some mkGen ∧
      mkGen.counter = counter ∧
      mkGen ∈ ch.messageKeys ∧
      r2 = { r1 with
        receiverChains := r1.receiverChains.set ci
          { ch with messageKeys := ch.messageKeys.eraseIdx pos } } ∧
      r2.receiverChains.map eraseRecvChain = r1.receiverChains.map eraseRecvChain := by
  rcases takeSkippedKey_exec their counter r1 with ⟨st', hNone, _⟩ |
      ⟨k, ci, ch, pos, hci, hch, hpos, hk, hSome⟩
  · rw [hTake] at hNone
    cases hNone
  · rw [hTake] at hSome
    injection hSome with hOk hR2
    injection hOk with hK
    injection hK with hK'
    subst hK'
    obtain ⟨ch', hch', hsrk_b⟩ := getElem?_of_findReceiverChainIndex r1 their ci hci
    rw [hch] at hch'
    injection hch' with hchEq
    subst hchEq
    have hsrk : ch.senderRatchetKey = their := beq_iff_eq.mp hsrk_b
    obtain ⟨k', hk', hCnt⟩ := getElem?_of_findIdx? (fun mk => mk.counter == counter) ch.messageKeys pos hpos
    rw [hk] at hk'
    injection hk' with hkEq
    subst hkEq
    have hCntEq : mkGen.counter = counter := beq_iff_eq.mp hCnt
    have hMem : mkGen ∈ ch.messageKeys := mem_of_getElem?_some ch.messageKeys pos mkGen hk
    have hErase : r2.receiverChains.map eraseRecvChain = r1.receiverChains.map eraseRecvChain := by
      rw [hR2]
      exact map_eraseRecvChain_set_messageKeys r1.receiverChains ci ch (ch.messageKeys.eraseIdx pos) hch
    exact ⟨ci, ch, pos, hci, hch, hsrk, hpos, hk, hCntEq, hMem, hR2, hErase⟩

private theorem mem_of_mem_dropLast {α : Type} : ∀ {xs : List α} {x : α}, x ∈ xs.dropLast → x ∈ xs
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: bs, x, h => by
    simp only [List.dropLast, List.mem_cons] at h
    rcases h with rfl | h'
    · exact List.Mem.head _
    · exact List.Mem.tail a (mem_of_mem_dropLast h')

theorem advanceChain_exec_some_full (F : ShaCompress) (their : PublicKey)
    (c : BitVec 32) (n : Nat) (ck : ChainKey) (st : RatchetState) (ci : Nat) (ch : ReceiverChain)
    (hn : ck.index.toNat + n = c.toNat)
    (hci : st.findReceiverChainIndex their = some ci)
    (hch : st.receiverChains[ci]? = some ch) :
    ∃ mks' : List MessageKeyGenerator,
      (RatchetState.advanceChain F their c n ck).exec st =
        (.ok (chainStepN F n ck),
          { st with receiverChains := st.receiverChains.set ci { ch with messageKeys := mks' } }) ∧
      (∀ k ∈ mks', k ∈ skippedKeys F n ck ∨ k ∈ ch.messageKeys) := by
  induction n generalizing ck st ch with
  | zero =>
    refine ⟨ch.messageKeys, ?_, fun k hk => Or.inr hk⟩
    simp only [RatchetState.advanceChain, exec_pure, chainStepN]
    have hch_eq : { ch with messageKeys := ch.messageKeys } = ch := rfl
    rw [hch_eq, set_eq_self_of_getElem?_eq_some st.receiverChains ci ch hch]
  | succ m ih =>
    have hlt : ck.index < c := index_lt_of_add_succ_eq ck c m hn
    have hne : ck.index ≠ BitVec.allOnes 32 := index_ne_allOnes_of_add_succ_eq ck c m hn
    have hnext : ck.nextChainKey F = .ok (step1 F ck) := nextChainKey_eq_of_ne F ck hne
    let keys := if maxMessageKeys < (ck.messageKeys F :: ch.messageKeys).length then
      (ck.messageKeys F :: ch.messageKeys).dropLast else (ck.messageKeys F :: ch.messageKeys)
    let ch₁ : ReceiverChain := { ch with messageKeys := keys }
    let st₁ : RatchetState := { st with receiverChains := st.receiverChains.set ci ch₁ }
    have hstore : (RatchetState.storeSkippedKey their (ck.messageKeys F)).exec st = (.ok (), st₁) :=
      storeSkippedKey_exec_some their (ck.messageKeys F) st ci ch hci hch
    have hci₁ : st₁.findReceiverChainIndex their = some ci := by
      rw [findReceiverChainIndex_set_thm st their ci ch₁ ⟨ch, hch, rfl⟩, hci]
    have hch₁ : st₁.receiverChains[ci]? = some ch₁ :=
      getElem?_set_eq_of_some st.receiverChains ci ch ch₁ hch
    have hn₁ : (step1 F ck).index.toNat + m = c.toNat :=
      step1_index_toNat_add F ck c m hn
    obtain ⟨mks', hExec, hMem⟩ := ih (step1 F ck) st₁ ch₁ hn₁ hci₁ hch₁
    have hKeysSub : ∀ k ∈ keys, k = ck.messageKeys F ∨ k ∈ ch.messageKeys := by
      intro k hk
      dsimp only [keys] at hk
      split at hk
      · have hk' := mem_of_mem_dropLast hk
        exact List.mem_cons.mp hk'
      · exact List.mem_cons.mp hk
    refine ⟨mks', ?_, ?_⟩
    · simp only [RatchetState.advanceChain, hlt, ↓reduceIte, exec_bind, hstore, exec_liftE, hnext]
      rw [hExec]
      simp only [chainStepN, st₁, ch₁, set_set_eq]
      rfl
    · intro k hk
      rcases hMem k hk with hSkip | hKeys
      · left
        simp only [skippedKeys, List.mem_append, List.mem_singleton]
        exact Or.inl hSkip
      · rcases hKeysSub k hKeys with rfl | hOld
        · left
          simp [skippedKeys]
        · exact Or.inr hOld

/-- Inversion for `advanceChain` followed by `nextChainKey` and `setReceiverChainKey` when
`¬ (counter < ck.index)`. -/
theorem advanceChain_setReceiverChainKey_ok_inv
    {F : ShaCompress} {their : PublicKey} {counter : BitVec 32}
    {ck ck_adv ck_next : ChainKey} {r1 r_adv r2 : RatchetState}
    (hNotLt : ¬ (counter < ck.index))
    (hAdv :
      Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r1 =
        (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey F = .ok ck_next)
    (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2)) :
    let n := (counter - ck.index).toNat
    ck.index ≤ counter ∧
    counter ≠ BitVec.allOnes 32 ∧
    ck_adv = chainStepN F n ck ∧
    ck_adv.index = counter ∧
    ck_next = step1 F ck_adv ∧
    ck_next.index = counter + 1 ∧
    ∃ ci : Nat, ∃ ch : ReceiverChain, ∃ mks' : List MessageKeyGenerator,
      r1.findReceiverChainIndex their = some ci ∧
      r1.receiverChains[ci]? = some ch ∧
      ch.senderRatchetKey = their ∧
      r2 = { r1 with
        receiverChains := r1.receiverChains.set ci
          { ch with chainKey := some ck_next, messageKeys := mks' } } ∧
      (∀ k ∈ mks', k ∈ skippedKeys F n ck ∨ k ∈ ch.messageKeys) := by
  intro n
  have hLe : ck.index ≤ counter := BitVec.not_lt.mp hNotLt
  have hn : ck.index.toNat + n = counter.toNat := index_toNat_add_sub_eq ck counter hLe
  cases hci : r1.findReceiverChainIndex their with
  | none =>
    exfalso
    cases hn_eq : n with
    | zero =>
      have hAdv0 :
          Mut.exec (RatchetState.advanceChain F their counter 0 ck) r1 = (.ok ck, r1) := rfl
      rw [show (counter - ck.index).toNat = 0 from hn_eq, hAdv0] at hAdv
      injection hAdv with _ hRadv
      subst hRadv
      rw [setReceiverChainKey_exec_none their ck_next r1 hci] at hSet
      cases hSet
    | succ m =>
      have hn' : ck.index.toNat + (m + 1) = counter.toNat := by omega
      have hlt' : ck.index < counter := index_lt_of_add_succ_eq ck counter m hn'
      rw [show (counter - ck.index).toNat = m + 1 from hn_eq] at hAdv
      simp only [RatchetState.advanceChain, hlt', ↓reduceIte, exec_bind,
        storeSkippedKey_exec_none their _ r1 hci] at hAdv
      cases hAdv
  | some ci =>
    obtain ⟨ch, hch, hsrk_b⟩ := getElem?_of_findReceiverChainIndex r1 their ci hci
    have hsrk : ch.senderRatchetKey = their := beq_iff_eq.mp hsrk_b
    obtain ⟨mks', hAdvFull, hMksSub⟩ :=
      advanceChain_exec_some_full F their counter n ck r1 ci ch hn hci hch
    rw [hAdvFull] at hAdv
    injection hAdv with hCkAdv hRadv
    injection hCkAdv with hCkAdvEq
    have hCkAdvSymm : ck_adv = chainStepN F n ck := hCkAdvEq.symm
    have hIdx : ck_adv.index = counter := by
      rw [hCkAdvSymm]
      exact chainStepN_index_eq F n ck counter hn
    have hNeAllOnes : counter ≠ BitVec.allOnes 32 := by
      intro hAll
      simp only [ChainKey.nextChainKey, hIdx, hAll, ↓reduceIte] at hNext
      cases hNext
    have hNextEq : ck_next = step1 F ck_adv := by
      rw [nextChainKey_eq_of_ne F ck_adv (by rw [hIdx]; exact hNeAllOnes)] at hNext
      injection hNext with hEq
      exact hEq.symm
    have hNextIdx : ck_next.index = counter + 1 := by
      rw [hNextEq, step1, hIdx]
    let ch_mid : ReceiverChain := { ch with messageKeys := mks' }
    have hci_adv : r_adv.findReceiverChainIndex their = some ci := by
      rw [← hRadv, findReceiverChainIndex_set_thm r1 their ci ch_mid ⟨ch, hch, rfl⟩, hci]
    have hch_adv : r_adv.receiverChains[ci]? = some ch_mid := by
      rw [← hRadv]
      exact getElem?_set_eq_of_some r1.receiverChains ci ch ch_mid hch
    rw [setReceiverChainKey_exec_some their ck_next r_adv ci ch_mid hci_adv hch_adv] at hSet
    injection hSet with _ hR2
    have hR2Eq :
        r2 = { r1 with
          receiverChains := r1.receiverChains.set ci
            { ch with chainKey := some ck_next, messageKeys := mks' } } := by
      rw [← hR2, ← hRadv]
      simp only [ch_mid, set_set_eq]
    exact ⟨hLe, hNeAllOnes, hCkAdvSymm, hIdx, hNextEq, hNextIdx,
      ci, ch, mks', rfl, hch, hsrk, hR2Eq, hMksSub⟩

end Proofs.libsignal.RngG.CliPure.R3
