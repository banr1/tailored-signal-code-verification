/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.ModelDefs
public import Symbolic.Proofs.Refinement.RecordBytesBridge
import Symbolic.Proofs.RngG.R3ModelInv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure

/-!
# Preservation of Receiver-Chain Well-Formedness

Defines model-level (`ChainKeysWF`, `ChainsWFm`) and record-level (`RecordChainsWF3`)
receiver-chain well-formedness (distinct sender ratchet keys, distinct cached skipped-key counters
per chain, and cached counters strictly below the chain-key index) and proves preservation across
existing-chain and DH-ratchet `advanceChain` / `setReceiverChainKey` steps.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.RngG.R3

open CryptoGames.LibsignalSession (ChainKey MessageKeyGenerator ReceiverChain PublicKey RatchetState
  Crypto Mut maxMessageKeys ShaCompress)
open CryptoVerification.SessionModel (chainStepN)
open CryptoVerification.SessionModel.AdvanceAndFrame
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec receiverChainToChainRec)

/-- Per-chain well-formedness: cached counters `Nodup`, each below the chain-key index. -/
def ChainKeysWF (ch : ReceiverChain) : Prop :=
  (ch.messageKeys.map MessageKeyGenerator.counter).Nodup ∧
  ∀ k ∈ ch.messageKeys, ∃ ck, ch.chainKey = some ck ∧ k.counter < ck.index

/-- Model-level receiver-chain well-formedness: sender ratchet keys `Nodup`, every chain
`ChainKeysWF`. -/
def ChainsWFm (cs : List ReceiverChain) : Prop :=
  (cs.map ReceiverChain.senderRatchetKey).Nodup ∧ ∀ ch ∈ cs, ChainKeysWF ch

/-- Record-level receiver-chain well-formedness on `RecordRec`. -/
def RecordChainsWF3 (rec : DY.Libsignal.Rust.RecordRec) : Prop :=
  (rec.current.receiverChains.map DY.Libsignal.Rust.ChainRec.senderRatchetKey).Nodup ∧
  (∀ c ∈ rec.current.receiverChains, (c.messageKeys.map Prod.fst).Nodup) ∧
  ∀ c ∈ rec.current.receiverChains, ∀ k ∈ c.messageKeys, ∃ ck, c.chainKey = some ck ∧ k.1 < ck.1

theorem nodup_map_of_sublist {α β : Type} {f : α → β} {l₁ l₂ : List α}
    (hsub : l₁.Sublist l₂) (hnd : (l₂.map f).Nodup) : (l₁.map f).Nodup :=
  hnd.sublist (hsub.map f)

theorem nodup_map_set_of_eq' {α β : Type} (f : α → β) (xs : List α) (i : Nat) (x : α)
    (h : ∃ x₀ ∈ xs[i]?, f x₀ = f x) (hnd : (xs.map f).Nodup) : ((xs.set i x).map f).Nodup := by
  rw [map_set_of_eq f xs i x h]
  exact hnd

theorem bv32_toNat_lt_of_ne_allOnes {c : BitVec 32} (hc : c ≠ BitVec.allOnes 32) :
    c.toNat < 2 ^ 32 - 1 := by
  have h1 : c.toNat < 2 ^ 32 := c.isLt
  have h2 : c.toNat ≠ 2 ^ 32 - 1 := by
    intro h
    apply hc
    apply BitVec.eq_of_toNat_eq
    rw [h, BitVec.toNat_allOnes]
  omega

theorem bv32_lt_add_one_of_lt {a c : BitVec 32} (hc : c ≠ BitVec.allOnes 32) (h : a < c) :
    a < c + 1 := by
  have := bv32_toNat_lt_of_ne_allOnes hc
  bv_omega

/-- Advancing the chain for `their` from `ck` to `c` preserves `Nodup` of cached counters and
bounds all cached counters strictly below `c`. -/
theorem advanceChain_keysWF (F : ShaCompress) (their : PublicKey)
    (c : BitVec 32) (n : Nat) (ck : ChainKey) (st : RatchetState) (ci : Nat) (ch : ReceiverChain)
    (hn : ck.index.toNat + n = c.toNat)
    (hci : st.findReceiverChainIndex their = some ci)
    (hch : st.receiverChains[ci]? = some ch)
    (hnd : (ch.messageKeys.map MessageKeyGenerator.counter).Nodup)
    (hlt : ∀ k ∈ ch.messageKeys, k.counter < ck.index) :
    ∃ mks' : List MessageKeyGenerator,
      (RatchetState.advanceChain F their c n ck).exec st =
        (.ok (chainStepN F n ck),
          { st with receiverChains := st.receiverChains.set ci { ch with messageKeys := mks' } }) ∧
      (mks'.map MessageKeyGenerator.counter).Nodup ∧
      (∀ k ∈ mks', k.counter < c) := by
  induction n generalizing ck st ch with
  | zero =>
    refine ⟨ch.messageKeys, ?_, hnd, ?_⟩
    · simp only [RatchetState.advanceChain, exec_pure, chainStepN]
      have hch_eq : { ch with messageKeys := ch.messageKeys } = ch := rfl
      rw [hch_eq, set_eq_self_of_getElem?_eq_some st.receiverChains ci ch hch]
    · intro k hk
      have hidx : ck.index = c := BitVec.eq_of_toNat_eq (by omega)
      rw [← hidx]
      exact hlt k hk
  | succ m ih =>
    have hlt0 : ck.index < c := index_lt_of_add_succ_eq ck c m hn
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
    have hcnt : (ck.messageKeys F).counter = ck.index := rfl
    have hsub : keys.Sublist (ck.messageKeys F :: ch.messageKeys) := by
      dsimp only [keys]
      split
      · exact List.dropLast_sublist _
      · exact List.Sublist.refl _
    have hndFull : ((ck.messageKeys F :: ch.messageKeys).map MessageKeyGenerator.counter).Nodup := by
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hnd⟩
      intro hmem
      obtain ⟨k, hk, hkc⟩ := List.mem_map.mp hmem
      have := hlt k hk
      rw [hkc, hcnt] at this
      exact absurd this (BitVec.lt_irrefl _)
    have hnd₁ : (ch₁.messageKeys.map MessageKeyGenerator.counter).Nodup :=
      nodup_map_of_sublist hsub hndFull
    have hstepIdx : (step1 F ck).index.toNat = ck.index.toNat + 1 := by omega
    have hlt₁ : ∀ k ∈ ch₁.messageKeys, k.counter < (step1 F ck).index := by
      intro k hk
      have hk' : k ∈ ck.messageKeys F :: ch.messageKeys := hsub.subset hk
      rcases List.mem_cons.mp hk' with rfl | hold
      · rw [hcnt, BitVec.lt_def, hstepIdx]
        omega
      · have h1 := hlt k hold
        rw [BitVec.lt_def] at h1 ⊢
        rw [hstepIdx]
        omega
    obtain ⟨mks', hExec, hnd', hlt'⟩ := ih (step1 F ck) st₁ ch₁ hn₁ hci₁ hch₁ hnd₁ hlt₁
    refine ⟨mks', ?_, hnd', hlt'⟩
    simp only [RatchetState.advanceChain, hlt0, ↓reduceIte, exec_bind, hstore, exec_liftE, hnext]
    rw [hExec]
    simp only [chainStepN, st₁, ch₁, set_set_eq]
    rfl

theorem chainsWFm_advance_set
    {F : ShaCompress} {their : PublicKey} {counter : BitVec 32}
    {ck ck_adv ck_next : ChainKey} {r1 r_adv r2 : RatchetState}
    (hNotLt : ¬ (counter < ck.index))
    (hAdv :
      Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r1 =
        (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey F = .ok ck_next)
    (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2))
    (hwf : ChainsWFm r1.receiverChains)
    (hbound : ∀ ch ∈ r1.receiverChains, ch.senderRatchetKey = their →
      ∀ k ∈ ch.messageKeys, k.counter < ck.index) :
    ChainsWFm r2.receiverChains := by
  obtain ⟨hLe, hNeAll, _hCkAdv, _hIdx, _hNextEq, hNextIdx, ci, ch, _mks, hci, hch, hsrk, _hR2,
    _hMem⟩ := advanceChain_setReceiverChainKey_ok_inv hNotLt hAdv hNext hSet
  have hn : ck.index.toNat + (counter - ck.index).toNat = counter.toNat :=
    index_toNat_add_sub_eq ck counter hLe
  have hchMem : ch ∈ r1.receiverChains := mem_of_getElem?_some r1.receiverChains ci ch hch
  have hchWF := hwf.2 ch hchMem
  obtain ⟨mks', hExec, hnd', hlt'⟩ :=
    advanceChain_keysWF F their counter (counter - ck.index).toNat ck r1 ci ch hn hci hch
      hchWF.1 (hbound ch hchMem hsrk)
  rw [hExec] at hAdv
  injection hAdv with _ hRadv
  let ch_mid : ReceiverChain := { ch with messageKeys := mks' }
  have hci_adv : r_adv.findReceiverChainIndex their = some ci := by
    rw [← hRadv, findReceiverChainIndex_set_thm r1 their ci ch_mid ⟨ch, hch, rfl⟩, hci]
  have hch_adv : r_adv.receiverChains[ci]? = some ch_mid := by
    rw [← hRadv]
    exact getElem?_set_eq_of_some r1.receiverChains ci ch ch_mid hch
  rw [setReceiverChainKey_exec_some their ck_next r_adv ci ch_mid hci_adv hch_adv] at hSet
  injection hSet with _ hR2
  have hrcs : r2.receiverChains = r1.receiverChains.set ci
      { ch with chainKey := some ck_next, messageKeys := mks' } := by
    rw [← hR2, ← hRadv]
    simp only [ch_mid, set_set_eq]
  rw [hrcs]
  refine ⟨nodup_map_set_of_eq' ReceiverChain.senderRatchetKey r1.receiverChains ci _
    ⟨ch, hch, rfl⟩ hwf.1, ?_⟩
  intro rc hrc
  rcases mem_set_or r1.receiverChains ci _ rc hrc with rfl | hold
  · refine ⟨hnd', ?_⟩
    intro k hk
    refine ⟨ck_next, rfl, ?_⟩
    rw [hNextIdx]
    exact bv32_lt_add_one_of_lt hNeAll (hlt' k hk)
  · exact hwf.2 rc hold

theorem chainsWFm_existing
    {F : ShaCompress} {their : PublicKey} {counter : BitVec 32}
    {ck ck_adv ck_next : ChainKey} {r0 r_adv r2 : RatchetState}
    (hFind : r0.findReceiverChainKey their = .ok (some ck))
    (hNotLt : ¬ (counter < ck.index))
    (hAdv :
      Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r0 =
        (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey F = .ok ck_next)
    (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2))
    (hwf : ChainsWFm r0.receiverChains) :
    ChainsWFm r2.receiverChains := by
  obtain ⟨ci, rc, _hci, hrc, hsrk', hrck⟩ := findReceiverChainKey_ok_some r0 their ck hFind
  have hrcMem : rc ∈ r0.receiverChains := mem_of_getElem?_some r0.receiverChains ci rc hrc
  refine chainsWFm_advance_set hNotLt hAdv hNext hSet hwf ?_
  intro ch hch hsrk k hk
  have hchEq : ch = rc := by
    apply List.inj_on_of_nodup_map hwf.1 hch hrcMem
    rw [hsrk, hsrk']
  subst hchEq
  obtain ⟨ck', hck', hlt⟩ := (hwf.2 ch hch).2 k hk
  rw [hrck] at hck'
  injection hck' with hckEq
  subst hckEq
  exact hlt

theorem chainsWFm_ratchet
    {C : Crypto} {their : PublicKey} {coins : BitVec 256} {counter : BitVec 32}
    {ck ck_adv ck_next : ChainKey} {r0 r1 r_adv r2 : RatchetState}
    (hFind : r0.findReceiverChainKey their = .ok none)
    (hDh : Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1))
    (hNotLt : ¬ (counter < ck.index))
    (hAdv :
      Mut.exec (RatchetState.advanceChain C.F their counter (counter - ck.index).toNat ck) r1 =
        (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey C.F = .ok ck_next)
    (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2))
    (hwf : ChainsWFm r0.receiverChains) :
    ChainsWFm r2.receiverChains := by
  obtain ⟨_sc, _nrk, _frk, _sck, _hsc, _hrc1, _hrc2, hR1⟩ := dhRatchetStep_ok_inv hDh
  have hnone : r0.findReceiverChainIndex their = none := findReceiverChainKey_ok_none r0 their hFind
  have hnotin : ∀ ch ∈ r0.receiverChains, ch.senderRatchetKey ≠ their := by
    intro ch hch heq
    have hall := List.findIdx?_eq_none_iff.mp hnone ch hch
    simp [heq] at hall
  let newCh : ReceiverChain := ⟨their, some ck, []⟩
  have hsub : (RatchetState.evictReceiverChains (r0.receiverChains ++ [newCh])).Sublist
      (r0.receiverChains ++ [newCh]) := List.drop_sublist _ _
  have hwfApp : ChainsWFm (r0.receiverChains ++ [newCh]) := by
    refine ⟨?_, ?_⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨hwf.1, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp ha
      exact hnotin ch hch (hab.trans hb)
    · intro ch hch
      rcases List.mem_append.mp hch with hold | hnew
      · exact hwf.2 ch hold
      · rw [List.mem_singleton] at hnew
        subst hnew
        exact ⟨List.nodup_nil, fun k hk => absurd hk (List.not_mem_nil)⟩
  have hwf1 : ChainsWFm r1.receiverChains := by
    rw [hR1]
    exact ⟨nodup_map_of_sublist hsub hwfApp.1, fun ch hch => hwfApp.2 ch (hsub.subset hch)⟩
  refine chainsWFm_advance_set hNotLt hAdv hNext hSet hwf1 ?_
  intro ch hch hsrk k hk
  rw [hR1] at hch
  rcases List.mem_append.mp (hsub.subset hch) with hold | hnew
  · exact absurd hsrk (hnotin ch hold)
  · rw [List.mem_singleton] at hnew
    subst hnew
    exact absurd hk (List.not_mem_nil)

theorem publicKey_serialize_inj' : Function.Injective PublicKey.serialize := by
  intro a b h
  simp only [PublicKey.serialize, List.cons.injEq, true_and] at h
  exact publicKey_ext_bytes_toList h

theorem chainsWFm_of_recordChainsWF3
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hwf : RecordChainsWF3 (sessionToRecordRec s)) :
    ChainsWFm s.state.receiverChains := by
  obtain ⟨h1, h2, h3⟩ := hwf
  simp only [sessionToRecordRec, sessionToSessionRec, List.map_map, List.forall_mem_map] at h1 h2 h3
  refine ⟨?_, ?_⟩
  · have h1' : ((s.state.receiverChains.map ReceiverChain.senderRatchetKey).map
        PublicKey.serialize).Nodup := by
      simpa [receiverChainToChainRec, List.map_map, Function.comp_def] using h1
    exact h1'.of_map PublicKey.serialize
  · intro ch hch
    refine ⟨?_, ?_⟩
    · have := h2 ch hch
      simpa [receiverChainToChainRec, List.map_map, Function.comp_def] using this
    · intro k hk
      have := h3 ch hch (k.counter, k.seed)
        (by simp only [receiverChainToChainRec]; exact List.mem_map_of_mem hk)
      obtain ⟨ckr, hckr, hlt⟩ := this
      simp only [receiverChainToChainRec, Option.map_eq_some_iff] at hckr
      obtain ⟨ck, hck, rfl⟩ := hckr
      exact ⟨ck, hck, hlt⟩

theorem recordChainsWF3_of_chainsWFm
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hwf : ChainsWFm s.state.receiverChains) :
    RecordChainsWF3 (sessionToRecordRec s) := by
  obtain ⟨h1, h2⟩ := hwf
  simp only [RecordChainsWF3, sessionToRecordRec, sessionToSessionRec, List.map_map,
    List.forall_mem_map]
  refine ⟨?_, ?_, ?_⟩
  · have := h1.map publicKey_serialize_inj'
    simpa [receiverChainToChainRec, List.map_map, Function.comp_def] using this
  · intro ch hch
    simpa [receiverChainToChainRec, List.map_map, Function.comp_def] using (h2 ch hch).1
  · intro ch hch kr hkr
    simp only [receiverChainToChainRec, List.mem_map] at hkr
    obtain ⟨k, hk, rfl⟩ := hkr
    obtain ⟨ck, hck, hlt⟩ := (h2 ch hch).2 k hk
    exact ⟨(ck.index, CryptoGames.HMAC.keyToBytes32 ck.key),
      by simp [receiverChainToChainRec, hck], hlt⟩

end Proofs.libsignal.RngG.CliPure.R3
