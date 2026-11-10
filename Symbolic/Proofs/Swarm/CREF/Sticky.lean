/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape

/-!
# Stability of `ModelAcceptsTermAfterCoinSplit` Under Appended Events

Proves `sticky_acceptsVia_append_iff`: once the hardware event suffix `τ₂` contains an
initial non-`rng` `.accept` event, appending further events `τ'` leaves
`ModelAcceptsTermAfterCoinSplit` invariant because the pinned accept index lies inside `τ₂`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

private theorem sticky_lt_of_rngPin {τ₂ τ' : List MachineEvent} {k : Nat}
    (hacc : ∃ pt, (τ₂.filter fun e => eventKind e != .rng).head? = some (.accept pt))
    (hpin : ((τ₂ ++ τ').take k).all (fun ev => eventKind ev == .rng) = true) :
    k < τ₂.length := by
  by_contra hk
  rw [List.take_append, List.take_of_length_le (by omega), List.all_append,
    Bool.and_eq_true] at hpin
  obtain ⟨pt, hpt⟩ := hacc
  have hnil : τ₂.filter (fun e => eventKind e != .rng) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simpa using List.all_eq_true.1 hpin.1 a ha
  rw [hnil] at hpt
  simp at hpt

/-- When the first non-`rng` event of `τ₂` is an `.accept` event, `ModelAcceptsTermAfterCoinSplit`
is invariant under appending trailing hardware events `τ'`. -/
theorem sticky_acceptsVia_append_iff {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {τ₁ : List MachineEvent} {e : MachineEvent} {τ₂ τ' : List MachineEvent} {t : DY.Bytes}
    (hacc : ∃ pt, (τ₂.filter fun e => eventKind e != .rng).head? = some (.accept pt)) :
    ModelAcceptsTermAfterCoinSplit interpretation r S who ok g ms τ₁ e (τ₂ ++ τ') t ↔
      ModelAcceptsTermAfterCoinSplit interpretation r S who ok g ms τ₁ e τ₂ t := by
  constructor
  · rintro ⟨ext, m, msgIdx, k, pt, g₁, hkn, hd, ha, hσ, hm, hk, hpin, hok⟩
    have hlt := sticky_lt_of_rngPin hacc hpin
    rw [List.take_append_of_le_length (by omega)] at hpin
    rw [List.getElem?_append_left hlt] at hk
    rw [List.take_append_of_le_length (by omega)] at hok
    exact ⟨ext, m, msgIdx, k, pt, g₁, hkn, hd, ha, hσ, hm, hk, hpin, hok⟩
  · rintro ⟨ext, m, msgIdx, k, pt, g₁, hkn, hd, ha, hσ, hm, hk, hpin, hok⟩
    have hlt : k < τ₂.length := (List.getElem?_eq_some_iff.mp hk).1
    have he1 : (τ₂ ++ τ').take k = τ₂.take k := List.take_append_of_le_length (Nat.le_of_lt hlt)
    have he2 : (τ₂ ++ τ').take (k + 1) = τ₂.take (k + 1) := List.take_append_of_le_length hlt
    exact ⟨ext, m, msgIdx, k, pt, g₁, hkn, hd, ha, hσ, hm,
      (List.getElem?_append_left hlt).trans hk, he1.symm ▸ hpin, he2.symm ▸ hok⟩

end Symbolic.Swarm.CREF
