/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Refinement.RecordBytesBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure

/-!
# Skipped-Key Removal Helpers on Receiver Chains

Proves list indexing and `Nodup` lemmas characterizing the remaining cached message keys in
receiver chains after `RatchetState.takeSkippedKey` succeeds.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.RngG.R3

open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.SessionModel.AdvanceAndFrame (mem_of_getElem?_some mem_of_mem_eraseIdx)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec
  receiverChainToChainRec)

theorem eraseIdx_counter_ne_of_nodup :
    ∀ {mks : List MessageKeyGenerator} {pos : Nat} {mkGen mk : MessageKeyGenerator},
      (mks.map MessageKeyGenerator.counter).Nodup →
      mks[pos]? = some mkGen → mk ∈ mks.eraseIdx pos → mk.counter ≠ mkGen.counter
  | [], _, _, _, _, hpos, _ => by simp at hpos
  | x :: xs, 0, mkGen, mk, hnd, hpos, hmem => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hpos; subst hpos
    simp only [List.eraseIdx_zero] at hmem
    obtain ⟨hx_not_mem, _⟩ := List.nodup_cons.mp hnd
    intro hEq; exact hx_not_mem (by rw [← hEq]; exact List.mem_map_of_mem hmem)
  | x :: xs, pos + 1, mkGen, mk, hnd, hpos, hmem => by
    simp only [List.getElem?_cons_succ] at hpos
    simp only [List.eraseIdx_cons_succ, List.mem_cons] at hmem
    obtain ⟨hx_not_mem, hnd_xs⟩ := List.nodup_cons.mp hnd
    rcases hmem with rfl | hmem_xs
    · intro hEq; have hmkGen_mem : mkGen ∈ xs := List.mem_of_getElem? hpos
      exact hx_not_mem (by rw [hEq]; exact List.mem_map_of_mem hmkGen_mem)
    · exact eraseIdx_counter_ne_of_nodup hnd_xs hpos hmem_xs

theorem mem_set_eq_or_exists_getElem?_ne {α : Type} :
    ∀ (l : List α) (i : Nat) (x y : α),
      y ∈ l.set i x →
      y = x ∨ ∃ j, j ≠ i ∧ l[j]? = some y
  | [], _, _, _, h => by simp at h
  | a :: l, 0, x, y, h => by
    simp only [List.set, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl rfl
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem h
      exact Or.inr ⟨j + 1, Nat.succ_ne_zero j, by simp [hj]⟩
  | a :: l, i + 1, x, y, h => by
    simp only [List.set, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr ⟨0, (Nat.succ_ne_zero i).symm, rfl⟩
    · rcases mem_set_eq_or_exists_getElem?_ne l i x y h with rfl | ⟨j, hj_ne, hj⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨j + 1, fun hEq => hj_ne (Nat.succ.inj hEq), by simp [hj]⟩

theorem map_getElem?_ne_of_nodup {α β : Type} (f : α → β) :
    ∀ {l : List α} {i j : Nat} {a b : α},
      (l.map f).Nodup → l[i]? = some a → l[j]? = some b → j ≠ i → f b ≠ f a
  | [], _, _, _, _, _, hi, _, _ => by simp at hi
  | _ :: _, 0, 0, _, _, _, _, _, hne => absurd rfl hne
  | x :: xs, 0, j + 1, a, b, hnd, hi, hj, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
    simp only [List.getElem?_cons_succ] at hj
    obtain ⟨hx_not_mem, _⟩ := List.nodup_cons.mp hnd
    intro hEq
    exact hx_not_mem (by rw [← hEq]; exact List.mem_map_of_mem (List.mem_of_getElem? hj))
  | x :: xs, i + 1, 0, a, b, hnd, hi, hj, _ => by
    simp only [List.getElem?_cons_succ] at hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
    obtain ⟨hx_not_mem, _⟩ := List.nodup_cons.mp hnd
    intro hEq
    exact hx_not_mem (by rw [hEq]; exact List.mem_map_of_mem (List.mem_of_getElem? hi))
  | _ :: xs, i + 1, j + 1, _, _, hnd, hi, hj, hne => by
    simp only [List.getElem?_cons_succ] at hi hj
    obtain ⟨_, hnd_xs⟩ := List.nodup_cons.mp hnd
    exact map_getElem?_ne_of_nodup f hnd_xs hi hj (fun h => hne (congrArg Nat.succ h))

theorem publicKey_serialize_inj {pk1 pk2 : PublicKey}
    (h : pk1.serialize = pk2.serialize) : pk1 = pk2 := by
  simp only [PublicKey.serialize, List.cons.injEq, true_and] at h
  exact publicKey_ext_bytes_toList h

/-- Every cached key remaining after `takeSkippedKey pk counter` comes from an earlier receiver chain
and differs from `(pk.serialize, counter)` in either counter or sender ratchet key. -/
theorem takeSkippedKey_remaining_counter_ne_or_srk_ne
    {s s' : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    {pk : PublicKey} {counter : BitVec 32} {mkGen : MessageKeyGenerator} {r2 : RatchetState}
    (hTake : Mut.exec (RatchetState.takeSkippedKey pk counter) (ratchetStateOf s.state) =
      (.ok (some mkGen), r2))
    (hs' : s'.state.receiverChains = r2.receiverChains)
    (hSrkNodup : (s.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup)
    (hMksNodup : ∀ ch ∈ s.state.receiverChains,
      (ch.messageKeys.map MessageKeyGenerator.counter).Nodup)
    {c_k : ChainRec} (hc_k : c_k ∈ (sessionToRecordRec s').current.receiverChains)
    {k : BitVec 32 × HwBytes} (hk : k ∈ c_k.messageKeys) :
    ∃ c_old ∈ (sessionToRecordRec s).current.receiverChains,
      c_old.senderRatchetKey = c_k.senderRatchetKey ∧
      k ∈ c_old.messageKeys ∧
      (UInt32.ofBitVec k.1 ≠ UInt32.ofBitVec counter ∨
        c_old.senderRatchetKey ≠ pk.serialize) := by
  obtain ⟨ci, ch, pos, _, hch, hsrk, _, hpos, hCnt, _, hR2, _⟩ := takeSkippedKey_ok_some_inv hTake
  have hchMem : ch ∈ s.state.receiverChains := mem_of_getElem?_some s.state.receiverChains ci ch hch
  simp only [sessionToRecordRec, sessionToSessionRec, hs', hR2, List.mem_map] at hc_k
  rcases hc_k with ⟨rc', hrc', rfl⟩
  simp only [receiverChainToChainRec, List.mem_map] at hk
  rcases hk with ⟨mk, hmk, rfl⟩
  rcases mem_set_eq_or_exists_getElem?_ne s.state.receiverChains ci
      { ch with messageKeys := ch.messageKeys.eraseIdx pos } rc' hrc' with rfl | ⟨cj, hcj_ne, hcj⟩
  · have hmk_old : mk ∈ ch.messageKeys := mem_of_mem_eraseIdx ch.messageKeys pos mk hmk
    have hne_bv : mk.counter ≠ counter := by
      rw [← hCnt]; exact eraseIdx_counter_ne_of_nodup (hMksNodup ch hchMem) hpos hmk
    have hne_u32 : UInt32.ofBitVec mk.counter ≠ UInt32.ofBitVec counter :=
      fun h => hne_bv (congrArg UInt32.toBitVec h)
    refine ⟨receiverChainToChainRec ch, ?_, rfl, ?_, Or.inl hne_u32⟩
    · simp only [sessionToRecordRec, sessionToSessionRec]; exact List.mem_map_of_mem hchMem
    · simp only [receiverChainToChainRec, List.mem_map]; exact ⟨mk, hmk_old, rfl⟩
  · have hrc_old : rc' ∈ s.state.receiverChains := List.mem_of_getElem? hcj
    have hsrk_ne : rc'.senderRatchetKey ≠ pk := by
      rw [← hsrk]
      exact map_getElem?_ne_of_nodup ReceiverChain.senderRatchetKey hSrkNodup hch hcj hcj_ne
    have hser_ne : (receiverChainToChainRec rc').senderRatchetKey ≠ pk.serialize := by
      intro hEq
      exact hsrk_ne (publicKey_serialize_inj hEq)
    refine ⟨receiverChainToChainRec rc', ?_, rfl, ?_, Or.inr hser_ne⟩
    · simp only [sessionToRecordRec, sessionToSessionRec]; exact List.mem_map_of_mem hrc_old
    · simp only [receiverChainToChainRec, List.mem_map]; exact ⟨mk, hmk, rfl⟩

end Proofs.libsignal.RngG.CliPure.R3
