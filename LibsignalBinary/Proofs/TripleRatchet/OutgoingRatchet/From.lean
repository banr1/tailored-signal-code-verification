/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Decode
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Frame
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case1
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case3
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case4

/-!
# Verification of `OutgoingTripleRatchet::from_session_state`

Combines the four branch proofs (`Case1`–`Case4`) into `otrFrom_ok_ext`, `otrFrom_ok`, and
`otrFrom_placed_ok` for `<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

/-! ## Top-level `otrFrom_ok` theorem -/

theorem otrFrom_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hDeser : DeserializeExtOk img.base ext)
    (hRemIk : RemoteIdentityKeyExtOk img A ext)
    (hDropSpe : DropSpeExtOk img A ext) :
    OtrFromExtOk img A ext := by
  apply subroutine_ok_of_cases4
    (P₁ := fun x => x.st.senderChain = none)
    (P₂ := fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)
    (P₃ := fun x => ∃ sc, x.st.senderChain = some sc ∧
      ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = none)
    (P₄ := fun x => ∃ sc rem, x.st.senderChain = some sc ∧
      ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)
  · intro x
    cases hsc : x.st.senderChain with
    | none => exact Or.inl rfl
    | some sc =>
      by_cases hver : 256 ≤ x.st.version.toNat
      · exact Or.inr (Or.inl ⟨sc, rfl, hver⟩)
      · cases hrem : x.st.remoteIdentity with
        | none => exact Or.inr (Or.inr (Or.inl ⟨sc, rfl, hver, rfl⟩))
        | some rem => exact Or.inr (Or.inr (Or.inr ⟨sc, rem, rfl, hver, rfl⟩))
  · exact otrFrom_case1_ok_ext himg
  · exact otrFrom_case2_ok_ext himg hA hDeser
  · exact otrFrom_case3_ok_ext himg hA hDeser hRemIk
  · exact otrFrom_case4_ok_ext himg hDeser hRemIk hDropSpe

theorem otrFrom_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    (hDeser : DeserializeOk img.base C ctl abs)
    (hRemIk : RemoteIdentityKeyOk img C A ctl abs)
    (hDropSpe : DropSpeOk img C A ctl abs) :
    OtrFromOk img C A ctl abs :=
  otrFrom_ok_ext himg (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA) hDeser hRemIk hDropSpe

/-! ## Relocatable `[LibsignalPlacement]` `otrFrom_placed_ok` theorem -/

theorem otrFrom_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_19).rebase (blkPl_19).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec)
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromPlacedSpec A) := by
  apply subroutine_ok_of_cases4_placed
    (P₁ := fun x => x.st.senderChain = none)
    (P₂ := fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)
    (P₃ := fun x => ∃ sc, x.st.senderChain = some sc ∧
      ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = none)
    (P₄ := fun x => ∃ sc rem, x.st.senderChain = some sc ∧
      ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = some rem)
  · intro x
    cases hsc : x.st.senderChain with
    | none => exact Or.inl rfl
    | some sc =>
      by_cases hver : 256 ≤ x.st.version.toNat
      · exact Or.inr (Or.inl ⟨sc, rfl, hver⟩)
      · cases hrem : x.st.remoteIdentity with
        | none => exact Or.inr (Or.inr (Or.inl ⟨sc, rfl, hver, rfl⟩))
        | some rem => exact Or.inr (Or.inr (Or.inr ⟨sc, rem, rfl, hver, rfl⟩))
  · exact otrFrom_case1_placed_ok
  · exact otrFrom_case2_placed_ok_of_contracts hdealloc hdeser
  · exact otrFrom_case3_placed_ok_of_contracts hdealloc hdeser hremIk
  · exact otrFrom_case4_placed_ok_of_contracts hdeser hremIk hdropSpe

theorem otrFrom_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromPlacedSpec A) :=
  otrFrom_placed_ok_of_contracts
    (ls_hook_ok_of_mem h_dealloc)
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_placed_ok H)
    hremIk hdropSpe

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
