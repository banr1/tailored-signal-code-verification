/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.VarintKey
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `PreKeyRecord::deserialize` Tag Varint Decode

`RustCliAllocBudget`-threaded relocatable key-varint decode CPS lemmas for
`PreKeyRecord::deserialize` (Block `65`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.VarintKeyBudget

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget

theorem pkAdvanceCursor_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (sliceCursorAt (sp' + 40#64) (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (noPanicQp s0)) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (sliceCursorAfter (sp' + 40#64) ptr bs rest ∗ R)
      (pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 ptr bs out)
      (noPanicQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt (sp' + 40#64) ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 40#64) (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepWPp_frame_noPanic h
    (fun sf Pf hqm =>
      pkEpiloguePostPlaced_append_prefix A lim st fuel maxLen s0 sp' x19 ptr bs k hkl out sf Pf hqm)

end LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.VarintKeyBudget
