/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs

/-!
# Decomposition of `seedSession` into Protobuf Fields

Proves `seedSession_eq_fields`, expressing `seedSession f` as the concatenation of `SeedField.enc`
over `seedFields f`, together with tag case-analysis and monotonicity lemmas for combining per-tag
`SessionStructure::merge_field` contracts.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open CryptoVerification.E2E.Record

theorem seedSlice_length {f : List (BitVec 8)} {o n : Nat} (h : o + n ≤ f.length) :
    (seedSlice f o n).length = n := by
  simp only [seedSlice, List.length_take, List.length_drop]
  omega

theorem seedU32_lt (f : List (BitVec 8)) (o : Nat) : seedU32 f o < 2 ^ 32 := by
  have h0 := (f.getD o 0).isLt
  have h1 := (f.getD (o + 1) 0).isLt
  have h2 := (f.getD (o + 2) 0).isLt
  have h3 := (f.getD (o + 3) 0).isLt
  simp only [seedU32]
  omega

/-- `ChainV.enc` matches `pbChain` when any present private key is nonempty and the chain index fits
in 32 bits. -/
theorem seedChain_enc {pub key : List (BitVec 8)} {priv : Option (List (BitVec 8))} {index : Nat}
    (hpriv : ∀ p, priv = some p → p ≠ []) (hidx : index < 2 ^ 32) :
    (seedChain pub priv key index).enc = pbChain pub priv key index := by
  have hi : (BitVec.ofNat 32 index).toNat = index := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hidx
  cases priv with
  | none => simp [seedChain, ChainV.enc, pbChain, hi]
  | some p => simp [seedChain, ChainV.enc, pbChain, hi, hpriv p rfl]

/-- `seedSession f` equals `(seedFields f).flatMap SeedField.enc`. -/
theorem seedSession_eq_fields {f : List (BitVec 8)} (hf : SeedOk f) :
    seedSession f = (seedFields f).flatMap SeedField.enc := by
  have hlen := hf.1
  have hp : seedSlice f 129 32 ≠ [] := by
    intro h
    have := seedSlice_length (f := f) (o := 129) (n := 32) (by omega)
    rw [h] at this
    simp at this
  have hc1 : (seedChain (seedSlice f 97 32) (some (seedSlice f 129 32)) (seedSlice f 161 32)
      (seedU32 f 193)).enc =
      pbChain (seedSlice f 97 32) (some (seedSlice f 129 32)) (seedSlice f 161 32)
        (seedU32 f 193) :=
    seedChain_enc (by rintro p ⟨⟩; exact hp) (seedU32_lt f 193)
  have hc2 : (seedChain (seedSlice f 198 32) none (seedSlice f 230 32) (seedU32 f 262)).enc =
      pbChain (seedSlice f 198 32) none (seedSlice f 230 32) (seedU32 f 262) :=
    seedChain_enc (by rintro p ⟨⟩) (seedU32_lt f 262)
  simp only [seedSession, seedFields, List.flatMap_append, List.append_assoc]
  split_ifs <;>
    simp [SeedField.enc, SeedField.payload, SeedField.tag, SeedField.wt, pbBytes, pbVarint,
      pbVarintBody, hc1, hc2]

/-! ## Relocatable `[LibsignalPlacement]` Field Dispatch Helpers -/

section Placed

open Arm64 ProofLib Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Every `SeedField` has tag in `{1, 2, 3, 4, 6, 7, 9}`. -/
theorem seedField_tag_cases (fl : SeedField) :
    fl.tag = 1 ∨ (fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4) ∨
      fl.tag = 6 ∨ fl.tag = 7 ∨ fl.tag = 9 := by
  cases fl <;> simp [SeedField.tag]

theorem mergeFieldSeedPlacedOk_mono [LibsignalPlacement]
    {P Q : SeedField → Prop} {H : String → Option (State → State)}
    (hPQ : ∀ fl, P fl → Q fl) (hQ : MergeFieldSeedPlacedOk Q H) :
    MergeFieldSeedPlacedOk P H := by
  refine subroutine_ok_mono hQ (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  obtain ⟨hcrl, hraw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldSeedPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcrl, ?_⟩
  dsimp only [mergeFieldSeedRawSpec] at hraw ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hraw ⊢
  obtain ⟨⟨h0, h1, h2, h3, h4, hP, hrest⟩, hsp⟩ := hraw
  exact ⟨⟨h0, h1, h2, h3, h4, hPQ x.fld hP, hrest⟩, hsp⟩

/-- Combine the per-tag `[LibsignalPlacement]` `merge_field` seed contracts (tags `1`, `2|3|4`,
`6`, `7`, `9`) into the unrestricted `MergeFieldSeedPlacedOk (fun _ => True) H`. -/
theorem mergeFieldSeedPlacedOk_of_tags [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h1 : MergeFieldSeedPlacedOk (fun fl => fl.tag = 1) H)
    (h234 : MergeFieldSeedPlacedOk (fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4) H)
    (h6 : MergeFieldSeedPlacedOk (fun fl => fl.tag = 6) H)
    (h7 : MergeFieldSeedPlacedOk (fun fl => fl.tag = 7) H)
    (h9 : MergeFieldSeedPlacedOk (fun fl => fl.tag = 9) H) :
    MergeFieldSeedPlacedOk (fun _ => True) H := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hrepl : ∀ (P : SeedField → Prop), P x.fld →
      (s0.mem ⊨ (mergeFieldSeedPlacedSpec P).pre x s0 ∗ R) := fun P hP => by
    obtain ⟨hcrl, hraw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
    dsimp only [mergeFieldSeedPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    dsimp only [mergeFieldSeedRawSpec] at hraw ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hraw ⊢
    obtain ⟨⟨h0, ht, hw, hb, hd, _, hrest⟩, hmem⟩ := hraw
    exact ⟨⟨h0, ht, hw, hb, hd, hP, hrest⟩, hmem⟩
  rcases seedField_tag_cases x.fld with ht1 | ht234 | ht6 | ht7 | ht9
  · exact subroutine_ok.mono_outcome h1 x R s0 hpc hrun (hrepl _ ht1) hsp fun _ hout => hout
  · exact subroutine_ok.mono_outcome h234 x R s0 hpc hrun (hrepl _ ht234) hsp fun _ hout => hout
  · exact subroutine_ok.mono_outcome h6 x R s0 hpc hrun (hrepl _ ht6) hsp fun _ hout => hout
  · exact subroutine_ok.mono_outcome h7 x R s0 hpc hrun (hrepl _ ht7) hsp fun _ hout => hout
  · exact subroutine_ok.mono_outcome h9 x R s0 hpc hrun (hrepl _ ht9) hsp fun _ hout => hout

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
