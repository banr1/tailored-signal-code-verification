/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common

/-!
# In-Image Verification of `drop_glue::<SignalProtocolError> [local#2]`

Proves `drop_spe_ok` for `core::ptr::drop_glue::<SignalProtocolError> [local#2]` on
`tripleRatchetProgAt`.
-/

@[expose] public section

abbrev dropSpe2Name : String :=
  "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open DropGlueFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `drop_spe_ok` (`drop_glue::<SignalProtocolError> [local#2]`) -/

private theorem rodata_0x3f000_eq_spe2 :
    (libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 28 = speJumpTable := by
  rfl_kernel

private theorem rodata_speJumpTable_intro_spe2 {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) (secLen := 28) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x3f000_eq_spe2] at h

private theorem SepWP.intro_rodata_speJumpTable_spe2 {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWP prog target_pc s
      (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (rodata_speJumpTable_intro_spe2 himg hro hm)

private theorem speJumpTable_byte_spe2 (base : BitVec 64) (i : Nat) (off : BitVec 64) (b : BitVec 8)
    (hoff : bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44)) + BitVec.ofNat 64 i = off)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails ((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) ((base + off) ↦₈ᵣ b) := by
  have h : ((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) =
      ((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable.take i) ∗
        ((((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗
         (((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) + BitVec.ofNat 64 i + 1#64) ↦ᵣ
           speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h, BitVec.add_assoc base (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) (BitVec.ofNat 64 i), hoff]
  exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem SepWP.false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

private theorem speJumpTable_adrp_eq_spe2 {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))) :
    (entry + 40#64 &&& 18446744073709547520#64) = base + (bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40))) := by
  subst he
  have hadd : base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")) + 40#64 = base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40)) := by
    rw [BitVec.add_assoc]; rfl
  rw [hadd, adrp_page_of_aligned hb]
  rfl

end CryptoVerification.LibsignalTripleRatchet.Getters
