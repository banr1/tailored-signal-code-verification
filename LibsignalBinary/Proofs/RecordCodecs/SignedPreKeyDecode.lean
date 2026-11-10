/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Nonempty

/-!
# Verification of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`

Proves `signedDecode_ok_of_deps`, `signedDecode_ok_of_deps_x`, and `signedDecode_placed_ok_of_deps`
(Block `562`): on non-empty slices (`0 < x.bytes.length`), the 206-instruction inner decoder
satisfies `signedDecodeSpec` (`SignedPreKeyRecordStructure.decode`). On `x.bytes = []`, LLVM IPSCCP
constant-folded `+0x048` into an unconditional branch to `decode_varint`, returning
`Err(UnexpectedEof)` (`EmptyDisproof.signedDecode_empty_disproof`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- The CLI-local `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>` meets
`signedDecodeSpec` at any 4 KiB-aligned image base, given the hooks (`SignedHooks`) and the
ported callees (`SignedPortDeps`). -/
theorem signedDecode_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooks img.base A ext) (d : SignedPortDeps img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName)
      (signedDecodeSpec A img) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ => ?_
  have hne : x.bytes ≠ [] := by
    have h := hpre
    dsimp only [signedDecodeSpec, Spec.inImage] at h
    simp only [sepConj_assoc, satisfies_pure_sepConj] at h
    rcases h with ⟨_, ⟨_, _, _, hpos, _⟩, _⟩
    intro hnil
    simp [hnil] at hpos
  exact signedDecode_outcome_of_nonempty hH d hb hne hpc hrun hpre hsp

/-- X-form (`AllocContractsX` / `SignedHooksX` / `SignedPortDepsX`):
`<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>` meets `signedDecodeSpecX` at any
4 KiB-aligned image base. -/
theorem signedDecode_ok_of_deps_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooksX img A ext) (d : SignedPortDepsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName)
      (signedDecodeSpecX A img) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ => ?_
  have hne : x.bytes ≠ [] := by
    have h := hpre
    dsimp only [signedDecodeSpecX, Spec.inImage] at h
    simp only [sepConj_assoc, satisfies_pure_sepConj] at h
    rcases h with ⟨_, ⟨_, _, _, hpos, _⟩, _⟩
    intro hnil
    simp [hnil] at hpos
  exact signedDecode_outcome_of_nonempty_x hH d hb hne hpc hrun hpre hsp

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block `562`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

/-- Relocatable `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>` (block `562`) meets
`signedDecodePlacedSpec`, given `SignedHooksPlaced` and `SignedPortDepsPlaced`. -/
theorem signedDecode_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_562 H) (blkPl_562).base (signedDecodePlacedSpec A) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ => ?_
  have hne : x.bytes ≠ [] := by
    obtain ⟨_, hraw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
    dsimp only [signedDecodeRawSpec] at hraw
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hraw
    rcases hraw with ⟨⟨_, _, _, hpos, _⟩, _⟩
    intro hnil
    simp [hnil] at hpos
  exact signedDecode_placed_outcome_of_nonempty hH d hne hpc hrun hpre hsp

end Placed

end CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode
