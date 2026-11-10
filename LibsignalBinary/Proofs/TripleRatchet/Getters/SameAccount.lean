/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<IdentityKey>::is_same_account`

Verifies `<libsignal_protocol::identity_key::IdentityKey>::is_same_account` against
`isSameAccountSpec` on `tripleRatchetProgAt` and under `[LibsignalPlacement]`, given
`<PublicKey as PartialEq>::eq`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

private theorem publicKey_beq_false_of_ne {ik1 ik2 : IdentityKey} (h : ik1 ≠ ik2) :
    (ik1.publicKey == ik2.publicKey) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply h
  cases ik1; cases ik2
  cases heq
  rfl

private theorem memRegion_16_eq_stackFrameFor_eq (sp : BitVec 64) :
    memRegion (sp - 16#64) 16 =
      stackFrameFor libsignalSessionImage
        "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp := by
  rw [show (16 : Nat) = 8 * 2 by rfl, memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold
  simp only [stackFrameFor, libsignalSessionCode_frameBytes_0x3ecd4, reduceStackFrameAt]

private theorem memRegion_48_eq_stackFrameFor_ct_eq (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 =
      stackFrameFor libsignalSessionImage
        "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp := by
  rw [show (48 : Nat) = 8 * 6 by rfl, memRegion_cells (sp - 48#64) 6 (by decide)]
  cells_unfold
  simp only [stackFrameFor, libsignalSessionCode_frameBytes_0x3eda8, reduceStackFrameAt]

private def publicKeyEqMemSpec :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗
    memRegion (sp - 16#64 - 48#64) 48
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗
    memRegion (sp - 16#64 - 48#64) 48

private theorem publicKeyEqMem_ok_at_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (hEq : PublicKeyEqOkExt b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName + bv% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" - ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"))
      publicKeyEqMemSpec := by
  have hEq' := hEq
  unfold PublicKeyEqOkExt at hEq'
  rw [Program.fnAddr_rel (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
    (k := num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" - ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")) rfl] at hEq'
  refine subroutine_ok_map hEq' ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [publicKeyEqSpec, publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpre
  · intro sf hpost
    simpa only [publicKeyEqSpec, publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpost

private theorem stackAt_isSameAccount_split (sp : BitVec 64) :
    stackAt sp isSameAccountStack =
      memRegion (sp - 80#64 - 16#64) 16 ∗
      memRegion (sp - 80#64 - 16#64 - 48#64) 48 ∗
      memRegion (sp - 80#64) 32 ∗
      cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountStack]
  have h144 : sp - 80#64 - 16#64 - 48#64 = sp - 144#64 := by bv_omega
  have h96 : sp - 80#64 - 16#64 = sp - 96#64 := by bv_omega
  rw [h144, h96,
      show (80 + 64 : Nat) = 144 from rfl,
      show BitVec.ofNat 64 144 = 144#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 48) (k := 96)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 16) (k := 80)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 32) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      (memRegion_cells (sp - 48#64) 6 (by decide) :
        memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]
  ac_rfl

theorem is_same_account_ok_ext (b : BitVec 64) (ext : String → Option (State → State))
    (hEq : PublicKeyEqOkExt b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName)
      isSameAccountSpec := by
  simp only [isSameAccountSpec]
  have hEq' := publicKeyEqMem_ok_at_ext b ext hEq
  simp only [publicKeyEqMemSpec] at hEq'
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")) 192
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨localIkA, localIk, remoteIkA, remoteIk⟩ := x
  dsimp only at *
  subst h_1 h_2
  rw [stackAt_isSameAccount_split s0.sp]
  cells_unfold
  wp_pull_exists
  have hne := publicKey_beq_false_of_ne h
  wp_steps
  wp_apply
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at *
  wp_steps
  wp_done

theorem is_same_account_ok_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hEq : PublicKeyEqOk_trap b C abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr isSameAccountName)
      isSameAccountSpec :=
  is_same_account_ok_ext b (trTrapExterns C abs) hEq

theorem is_same_account_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEq : PublicKeyEqOk b C ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr isSameAccountName)
      isSameAccountSpec :=
  is_same_account_ok_ext b _ hEq

/-! ## Relocatable `[LibsignalPlacement]` Contract -/

private theorem publicKeyEqMem_placed_ok_of_eq [LibsignalPlacement] {H : String → Option (State → State)}
    (hEq : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqSpec)) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec) := by
  refine subroutine_ok_map hEq ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [withLsCodeLoaded, publicKeyEqSpec, publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpre
  · intro sf hpost
    simpa only [withLsCodeLoaded, publicKeyEqSpec, publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpost

theorem is_same_account_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (hEq : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqSpec)) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl isSameAccountSpec) := by
  simp only [withLsCodeLoaded, isSameAccountSpec]
  have hEq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec) :=
    publicKeyEqMem_placed_ok_of_eq hEq
  have hEq' := ls_subroutine_ok_of_block (callerProg := (blkPC_17).rebase (blkPl_17).base H) hEq0
  simp only [withLsCodeLoaded, publicKeyEqMemSpec] at hEq'
  wp_init x s0
  obtain ⟨localIkA, localIk, remoteIkA, remoteIk⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 .x0 = localIkA := by assumption
  have hx2 : s0.readReg64 .x2 = remoteIkA := by assumption
  have hne0 : localIk ≠ remoteIk := by assumption
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst hx0 hx2
  rw [stackAt_isSameAccount_split s0.sp]
  cells_unfold
  wp_pull_exists
  have hne := publicKey_beq_false_of_ne hne0
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 212)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  wp_apply
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at *
  wp_steps
  wp_done

end CryptoVerification.LibsignalTripleRatchet.Getters
