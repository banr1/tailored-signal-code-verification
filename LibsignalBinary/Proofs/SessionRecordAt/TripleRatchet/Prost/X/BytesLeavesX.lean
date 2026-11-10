/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.BytesCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `bytes::Bytes` Leaf Contracts

Contracts for `<Bytes as From<Vec<u8>>>::from` (`0x423cc`) and the `Bytes` vtable `drop` dispatch
(`static_drop`, `promotable_even_drop`, `promotable_odd_drop`) at stack budget
`bytesVtableDropStackX = extHookStack + 48`, both on `contractProg img.base ext` and under
relocatable `[LibsignalPlacement]` (blocks `250`, `224`, `237`, `236`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_BytesLeavesX : True := trivial

/-! ## 1. `<Bytes as From<Vec<u8>>>::from` (`0x423cc`) -/

private theorem adrp_staticX {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")) + 176#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_reloc% (ls_off% "bytes::bytes::static_clone") - page% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 176))) = b + bv% (ls_reloc% (ls_off% "bytes::bytes::static_clone")) := by
  revert hb; bv_kernel

private theorem adrp_oddX {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")) + 204#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE" - page% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 204))) = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE") := by
  revert hb; bv_kernel

private theorem adrp_evenX {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")) + 60#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE" - page% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 60))) = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE") := by
  revert hb; bv_kernel

theorem bytesFromVec_base_okX {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    subroutine_ok (contractProg b ext)
      ((contractProg b ext).fnAddr bytesFromVecName)
      (bytesFromVecSpec A b) := by
  unfold bytesFromVecSpec vecU8At vecHeader bytesAt bytesHeader bytesBoxU8Buf bytesFromVecStack
  simp only [memRegion_32_eq_pointsTo64, stackAt_48_eq_cells]
  cells_unfold
  have hfn := (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")
  tripleRatchet_fetches b (Rust.withPanics ext) hfn (num% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")) 252
  wp_init x s0
  have hadrp_static :
      (((contractProg b ext).fnAddr bytesFromVecName + 176#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_reloc% (ls_off% "bytes::bytes::static_clone") - page% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 176))) = b + bv% (ls_reloc% (ls_off% "bytes::bytes::static_clone")) := by
    dsimp only [contractProg]
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")]
    exact adrp_staticX hb
  have hadrp_odd :
      (((contractProg b ext).fnAddr bytesFromVecName + 204#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE" - page% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 204))) = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE") := by
    dsimp only [contractProg]
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")]
    exact adrp_oddX hb
  have hadrp_even :
      (((contractProg b ext).fnAddr bytesFromVecName + 60#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE" - page% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 60))) = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE") := by
    dsimp only [contractProg]
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")]
    exact adrp_evenX hb
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨v, out, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcap_eq : BitVec.ofNat 64 bs.length = cap := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ‹cap.toNat = bs.length›]
  have hif : (if cap = 0 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
    rw [‹cap.toNat = bs.length›]
    by_cases hbs : bs = []
    · subst hbs
      have hc0 : cap = 0 := by rw [← hcap_eq]; rfl
      simp [hc0]
    · have hc0 : cap ≠ 0 := by
        intro hc
        have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
        have h0 : cap.toNat = 0 := by simp [hc]
        omega
      simp only [hbs, hc0, ↓reduceIte, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  rw [hif, hcap_eq]
  wp_steps
  wp_if hlen0
  · have hbs_len0 : bs.length = 0 := by
      rw [← ‹cap.toNat = bs.length›, hlen0]; rfl
    wp_steps
    rw [bytesVtable_eq_off]
    simp only [hbs_len0, bytesPtr, bytesData, ite_true, ← hadrp_static]
    wp_done
  · have hbs_len_ne : bs.length ≠ 0 := by
      intro h0
      apply hlen0
      rw [← hcap_eq, h0]
    wp_steps
    wp_if hodd
    · have hodd64 : (ptr &&& 1#64) ≠ 0#64 := getLsbD_zero_iff.mp hodd
      wp_steps
      rw [bytesVtable_eq_off]
      simp only [hbs_len_ne, hodd64, bytesPtr, bytesData, ite_false, ← hadrp_odd]
      wp_done
    · have heven : (ptr &&& 1#64) = 0#64 := not_getLsbD_zero_iff.mp hodd
      wp_steps
      rw [bytesVtable_eq_off]
      simp only [hbs_len_ne, heven, bytesPtr, bytesData, ite_false, ite_true,
        ← hadrp_even]
      wp_done

/-- `<Bytes as From<Vec<u8>>>::from` meets `(bytesFromVecSpec A img.base).inImage img` on
`contractProg img.base ext`. -/
theorem bytesFromVec_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img) :=
  subroutine_ok_inImage img (bytesFromVec_base_okX (ProofLib.ObjectLoad.base_aligned_of_loads himg))

/-! ## 2. Vtable `drop` specs at `bytesVtableDropStackX = extHookStack + 48` -/

/-- Budget of the `Bytes` vtable `drop` functions with X externs: the 48-byte frame of
`promotable_{even,odd}_drop` on top of the `__rust_dealloc` tail call (`extHookStack`). -/
abbrev bytesVtableDropStackX : Nat := extHookStack + 48

def promotableEvenDropSpecX (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp bytesVtableDropStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp bytesVtableDropStackX

def promotableOddDropSpecX (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp bytesVtableDropStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp bytesVtableDropStackX

def bytesVtableDropSpecX (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) : Spec Unit where
  pre := fun _ s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp bytesVtableDropStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp bytesVtableDropStackX

/-! ## 3. `__rust_dealloc` tail call after a popped 48-byte frame -/

private theorem stackAt_vtX_cells (sp : BitVec 64) :
    stackAt sp bytesVtableDropStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem stackAt_vtX_comm (sp : BitVec 64) :
    stackAt sp bytesVtableDropStackX =
      stackAt (sp - BitVec.ofNat 64 extHookStack) 48 ∗ stackAt sp extHookStack := by
  unfold stackAt
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 (48 + extHookStack)) 48 extHookStack (by decide)
  have h0 : extHookStack + 48 = 48 + extHookStack := rfl
  have h1 : sp - BitVec.ofNat 64 (48 + extHookStack) =
      sp - BitVec.ofNat 64 extHookStack - 48#64 := by bv_lin
  have h2 : sp - BitVec.ofNat 64 (48 + extHookStack) + 48#64 =
      sp - BitVec.ofNat 64 extHookStack := by bv_lin
  rw [bytesVtableDropStackX, h0, hsplit, h2, h1]

private theorem pointsTo64_entails_existsX (a v : BitVec 64) {R Q : SepProp}
    (h : R ⊢ Q) : ((a ↦₆₄ v) ∗ R) ⊢ ∃∗ x, (a ↦₆₄ x) ∗ Q :=
  Entails.trans (sepConj_mono_right h) (Entails.sepExists_intro (P := fun x => (a ↦₆₄ x) ∗ Q) v)

private theorem pointsTo64_6_entails_cellsX (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5)) ⊢ cells base 6 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_existsX _ v0
    (pointsTo64_entails_existsX _ v1
      (pointsTo64_entails_existsX _ v2
        (pointsTo64_entails_existsX _ v3
          (pointsTo64_entails_existsX _ v4
            (Entails.sepExists_intro (P := fun x => (base + 40#64) ↦₆₄ x) v5)))))

private abbrev DeallocTailGhostX :=
  BitVec 64 × List (BitVec 8) × Nat ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

/-- `__rust_dealloc` called by a tail `b` after popping a 48-byte frame (`extHookStack`). -/
private def rustDeallocTailSpecX (A : RustAlloc) (img : Obj.Image) : Spec DeallocTailGhostX where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5) s =>
    ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab ∧ LayoutOk bs.length align ∧
      s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) extHookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp bytesVtableDropStackX

private theorem dealloc_tail_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff "__rustc::__rust_dealloc") :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocTailSpecX A img) := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, align, v0, v1, v2, v3, v4, v5⟩ R s0 hpc hrun hpre hsp => ?_
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cellsX (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  unfold rustDeallocTailSpecX at hpre
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hF, hsym, hlay, hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h1 : s0.mem ⊨
      (A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - 48#64) extHookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hmem
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hbs_mem (sepConj_mono_right hcells)))
  rw [← stackAt_vtX_cells, stackAt_vtX_comm] at h1
  have hpre' : s0.mem ⊨ ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
      (p, bs.length, align) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 extHookStack) 48 ∗ R) := by
    unfold Spec.inImage Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack
    dsimp only
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2, hlay⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) h1
    ac_rfl
  refine (hA.dealloc_ok_at name k hk).mono_outcome (p, bs.length, align)
    (stackAt (s0.sp - BitVec.ofNat 64 extHookStack) 48 ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTailSpecX
    unfold Spec.inImage Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack at hpost
    dsimp only at hpost ⊢
    rw [stackAt_vtX_comm]
    refine Satisfies.mono (Entails.of_eq ?_) hpost
    ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, False.elim (not_satisfies_false_sepConj hpost)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, False.elim (not_satisfies_false_sepConj hpost)⟩))
  · exact False.elim (not_satisfies_false_sepConj hpost)

/-! ## 4. `static_drop`, `promotable_even_drop`, `promotable_odd_drop` on `contractProg` -/

private theorem or_one_and_not_oneX {ptr : BitVec 64} (h : (ptr &&& 1#64) = 0#64) :
    (ptr ||| 1#64) &&& (-2#64) = ptr := by
  bv_bits

private theorem odd_drop_addX {off len : Nat} (hoff : off ≤ len) :
    BitVec.ofNat 64 off + BitVec.ofNat 64 (len - off) = BitVec.ofNat 64 len := by
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le hoff]

private theorem ult_ofNat_falseX {off len : Nat} (hoff : off ≤ len) (hlen : len < 2 ^ 63) :
    (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 off) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : off < 2 ^ 64)]
  omega

theorem bytesStaticDrop_base_okX {b : BitVec 64} {ext : String → Option (State → State)} :
    subroutine_ok (contractProg b ext)
      ((contractProg b ext).fnAddr bytesStaticDropName) bytesStaticDropSpec := by
  unfold bytesStaticDropSpec
  have hfn := (ls_lemma% fnOff "bytes::bytes::static_drop")
  tripleRatchet_fetches b (Rust.withPanics ext) hfn (num% (ls_off% "bytes::bytes::static_drop")) 4
  clear hfn
  dsimp only [contractProg, bytesStaticDropName] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr "bytes::bytes::static_drop" = entry
  wp_init x s0
  examples_hide_fetches
  wp_steps
  wp_done

theorem promotableEvenDrop_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr promotableEvenDropName)
      ((promotableEvenDropSpecX A).inImage img) := by
  unfold promotableEvenDropSpecX Spec.inImage bytesBoxU8Buf
  have hfn := (ls_lemma% fnOff "bytes::bytes::promotable_even_drop")
  have hdealloc := dealloc_tail_okX hA promotableEvenDropName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "bytes::bytes::promotable_even_drop")) (by simp only [arm64_norm])
  tripleRatchet_fetches img.base (Rust.withPanics ext) hfn (num% (ls_off% "bytes::bytes::promotable_even_drop")) 240
  clear hfn
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_vtX_cells]
  cells_unfold
  dsimp only [contractProg, promotableEvenDropName] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr "bytes::bytes::promotable_even_drop" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos ‹0 < bs.length›
  simp only [hbs_ne, ↓reduceIte]
  have hand : (ptr ||| 1#64) &&& (-2#64) = ptr := or_one_and_not_oneX ‹(ptr &&& 1#64) = 0#64›
  have hlay : LayoutOk bs.length 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "bytes::bytes::promotable_even_drop")) hinv0
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_addX ‹off ≤ bs.length›,
      ult_ofNat_falseX ‹off ≤ bs.length› ‹bs.length < 2 ^ 63›] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    have hadd_even' : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_addX ‹off ≤ bs.length›]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, (1 : Nat) = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

theorem promotableOddDrop_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr promotableOddDropName)
      ((promotableOddDropSpecX A).inImage img) := by
  unfold promotableOddDropSpecX Spec.inImage bytesBoxU8Buf
  have hfn := (ls_lemma% fnOff "bytes::bytes::promotable_odd_drop")
  have hdealloc := dealloc_tail_okX hA promotableOddDropName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "bytes::bytes::promotable_odd_drop")) (by simp only [arm64_norm])
  tripleRatchet_fetches img.base (Rust.withPanics ext) hfn (num% (ls_off% "bytes::bytes::promotable_odd_drop")) 236
  clear hfn
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_vtX_cells]
  cells_unfold
  dsimp only [contractProg, promotableOddDropName] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr "bytes::bytes::promotable_odd_drop" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos ‹0 < bs.length›
  simp only [hbs_ne, ↓reduceIte]
  have hlsb0 : ptr.getLsbD 0 = true := getLsbD_zero_iff.mpr ‹(ptr &&& 1#64) ≠ 0#64›
  have hlay : LayoutOk bs.length 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "bytes::bytes::promotable_odd_drop")) hinv0
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_addX ‹off ≤ bs.length›,
      ult_ofNat_falseX ‹off ≤ bs.length› ‹bs.length < 2 ^ 63›] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    have hadd_odd : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_addX ‹off ≤ bs.length›]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, (1 : Nat) = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

/-! ## 5. Unified vtable `drop` dispatch on `contractProg` -/

/-- The vtable `drop` dispatch (`bytesDropFnAddr img.base ptr bs.length`) meets
`(bytesVtableDropSpecX A ptr bs off).inImage img` on `contractProg img.base ext`. -/
theorem bytesVtableDrop_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok (contractProg img.base ext)
      (bytesDropFnAddr img.base ptr bs.length)
      ((bytesVtableDropSpecX A ptr bs off).inImage img) := by
  refine subroutine_ok_outcome_intro fun _ R s0 hpc hrun hpre hsp => ?_
  unfold Spec.inImage at hpre
  dsimp only at hpre
  by_cases hbs : bs = []
  · subst hbs
    have haddr : bytesDropFnAddr img.base ptr ([] : List (BitVec 8)).length =
        (contractProg img.base ext).fnAddr bytesStaticDropName := by
      unfold bytesDropFnAddr contractProg
      simp only [List.length_nil, ↓reduceIte, Program.fnAddr_rebase]
    rw [haddr] at hpc
    unfold bytesVtableDropSpecX bytesBoxU8Buf at hpre
    simp only [↓reduceIte, sepConj_emp, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, _, _, hmem⟩
    have hpre_static : s0.mem ⊨ bytesStaticDropSpec.pre () s0 ∗
        (A.pool ∗ (stackAt s0.sp bytesVtableDropStackX ∗ R)) := by
      unfold bytesStaticDropSpec
      simpa only [emp_sepConj] using hmem
    refine (bytesStaticDrop_base_okX (b := img.base) (ext := ext)).mono_outcome
      () (A.pool ∗ (stackAt s0.sp bytesVtableDropStackX ∗ R)) s0 hpc hrun hpre_static hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      unfold Spec.inImage bytesVtableDropSpecX
      unfold bytesStaticDropSpec at hpost
      dsimp only at hpost ⊢
      simpa only [sepConj_assoc] using hpost
    · exact Or.inr (Or.inl ⟨hpan, False.elim (not_satisfies_false_sepConj hpost)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex, False.elim (not_satisfies_false_sepConj hpost)⟩))
    · exact False.elim (not_satisfies_false_sepConj hpost)
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_ne : bs.length ≠ 0 := by omega
    by_cases heven : (ptr &&& 1#64) = 0#64
    · have haddr : bytesDropFnAddr img.base ptr bs.length =
          (contractProg img.base ext).fnAddr promotableEvenDropName := by
        unfold bytesDropFnAddr contractProg
        simp only [hlen_ne, heven, ↓reduceIte, Program.fnAddr_rebase]
      rw [haddr] at hpc
      have hpre_even :
          s0.mem ⊨ ((promotableEvenDropSpecX A).inImage img).pre (ptr, bs, off) s0 ∗ R := by
        unfold bytesVtableDropSpecX bytesData bytesPtr at hpre
        unfold Spec.inImage promotableEvenDropSpecX
        dsimp only
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc,
          satisfies_pure_sepConj] at hpre
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre with ⟨hinv, ⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨hinv, ⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact (promotableEvenDrop_okX hA).mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_even hsp fun _ hout => hout
    · have haddr : bytesDropFnAddr img.base ptr bs.length =
          (contractProg img.base ext).fnAddr promotableOddDropName := by
        unfold bytesDropFnAddr contractProg
        simp only [hlen_ne, heven, ↓reduceIte, Program.fnAddr_rebase]
      rw [haddr] at hpc
      have hpre_odd :
          s0.mem ⊨ ((promotableOddDropSpecX A).inImage img).pre (ptr, bs, off) s0 ∗ R := by
        unfold bytesVtableDropSpecX bytesData bytesPtr at hpre
        unfold Spec.inImage promotableOddDropSpecX
        dsimp only
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc,
          satisfies_pure_sepConj] at hpre
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre with ⟨hinv, ⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨hinv, ⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact (promotableOddDrop_okX hA).mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_odd hsp fun _ hout => hout

/-! ## Relocatable `[LibsignalPlacement]` Proofs (Blocks `250`, `224`, `237`, `236`) -/

section Placed

open CryptoVerification

/-- Relocatable `<Bytes as From<Vec<u8>>>::from` (Block `250`) meets `bytesFromVecPlacedSpec A`. -/
theorem bytesFromVec_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} :
    subroutine_ok ((blkPC_250).rebase (blkPl_250).base H) (blkPl_250).base
      (bytesFromVecPlacedSpec A) :=
  bytesFromVec_placed_ok H

theorem bytesFromVec_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain (bytesFromVec_placed_ok H))

/-- Relocatable `bytes::bytes::static_drop` (Block `224`) meets `bytesStaticDropSpec`. -/
theorem bytesStaticDrop_placed_okX [LibsignalPlacement] {H : LibsignalHooks} :
    subroutine_ok ((blkPC_224).rebase (blkPl_224).base H) (blkPl_224).base
      bytesStaticDropSpec :=
  bytesStaticDrop_placed_ok H

private def rustDeallocTailRawSpecX (A : RustAlloc) : Spec DeallocTailGhostX where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5) s =>
    ⌜LayoutOk bs.length align ∧
      s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) extHookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp bytesVtableDropStackX

private theorem dealloc_tail_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustDeallocTailRawSpecX A)) := by
  refine Proofs.libsignal.Hooks2.subroutine_ok_withLsCl_map'
    (hA.dealloc (callerProg := callerProg))
    fun ⟨p, bs, align, v0, v1, v2, v3, v4, v5⟩ R s0 hpre => ?_
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cellsX (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  unfold rustDeallocTailRawSpecX at hpre
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hlay, hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h1 : s0.mem ⊨
      (A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - 48#64) extHookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hmem
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hbs_mem (sepConj_mono_right hcells)))
  rw [← stackAt_vtX_cells, stackAt_vtX_comm] at h1
  refine ⟨(p, bs.length, align), stackAt (s0.sp - BitVec.ofNat 64 extHookStack) 48 ∗ R, ?_, ?_⟩
  · unfold Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack
    dsimp only
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlay⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  · intro sf hpost
    unfold rustDeallocTailRawSpecX
    unfold Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack at hpost
    dsimp only at hpost ⊢
    rw [stackAt_vtX_comm]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Relocatable `bytes::bytes::promotable_even_drop` (Block `237`) meets
`withLsCodeLoaded lsmpl (promotableEvenDropSpecX A)`. -/
theorem promotableEvenDrop_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (withLsCodeLoaded lsmpl (promotableEvenDropSpecX A)) := by
  unfold withLsCodeLoaded promotableEvenDropSpecX bytesBoxU8Buf
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_vtX_cells]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos ‹0 < bs.length›
  simp only [hbs_ne, ↓reduceIte]
  have hand : (ptr ||| 1#64) &&& (-2#64) = ptr := or_one_and_not_oneX ‹(ptr &&& 1#64) = 0#64›
  have hlay : LayoutOk bs.length 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩
  apply sepWP_seq_lscl (mid := lsρ lsRustDeallocSym) ‹_›
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_addX ‹off ≤ bs.length›,
      ult_ofNat_falseX ‹off ≤ bs.length› ‹bs.length < 2 ^ 63›] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl1
    have hdealloc := lscall_of_withLsCl
      (dealloc_tail_placed_okX (callerProg := (blkPC_237).rebase (blkPl_237).base H) hA) hcl1
    have hadd_even' : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_addX ‹off ≤ bs.length›]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, (1 : Nat) = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

/-- Relocatable `bytes::bytes::promotable_odd_drop` (Block `236`) meets
`withLsCodeLoaded lsmpl (promotableOddDropSpecX A)`. -/
theorem promotableOddDrop_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (withLsCodeLoaded lsmpl (promotableOddDropSpecX A)) := by
  unfold withLsCodeLoaded promotableOddDropSpecX bytesBoxU8Buf
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_vtX_cells]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos ‹0 < bs.length›
  simp only [hbs_ne, ↓reduceIte]
  have hlsb0 : ptr.getLsbD 0 = true := getLsbD_zero_iff.mpr ‹(ptr &&& 1#64) ≠ 0#64›
  have hlay : LayoutOk bs.length 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩
  apply sepWP_seq_lscl (mid := lsρ lsRustDeallocSym) ‹_›
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_addX ‹off ≤ bs.length›,
      ult_ofNat_falseX ‹off ≤ bs.length› ‹bs.length < 2 ^ 63›] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl1
    have hdealloc := lscall_of_withLsCl
      (dealloc_tail_placed_okX (callerProg := (blkPC_236).rebase (blkPl_236).base H) hA) hcl1
    have hadd_odd : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_addX ‹off ≤ bs.length›]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, (1 : Nat) = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

/-- Unified relocatable vtable `drop` dispatch (`bytesPlacedDropFnAddr ptr bs.length`)
across blocks `224`, `237`, and `236` under `Stage1X.AllocContractsPlaced A H`. -/
theorem bytesVtableDrop_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCodeLoaded lsmpl (bytesVtableDropSpecX A ptr bs off)) := by
  refine subroutine_ok_outcome_intro fun _ R s0 hpc hrun hpre hsp => ?_
  by_cases hbs : bs = []
  · subst hbs
    have haddr : bytesPlacedDropFnAddr ptr ([] : List (BitVec 8)).length = (blkPl_224).base := rfl
    rw [haddr] at hpc
    have hstatic := ls_subroutine_ok_of_callee (callerProg := callerProg)
      (subroutine_ok_withLsCodeLoaded_of_plain (bytesStaticDrop_placed_ok H))
    have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
    unfold bytesVtableDropSpecX bytesBoxU8Buf at hpre0
    simp only [↓reduceIte, sepConj_emp, sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨_, _, hmem⟩
    have hpre_static : s0.mem ⊨ (withLsCodeLoaded lsmpl bytesStaticDropSpec).pre () s0 ∗
        (A.pool ∗ (stackAt s0.sp bytesVtableDropStackX ∗ R)) := by
      dsimp only [withLsCodeLoaded, bytesStaticDropSpec]
      rw [emp_sepConj, satisfies_pure_sepConj]
      exact ⟨hcl, hmem⟩
    refine hstatic.mono_outcome () (A.pool ∗ (stackAt s0.sp bytesVtableDropStackX ∗ R)) s0 hpc hrun hpre_static hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, bytesVtableDropSpecX]
      dsimp only [withLsCodeLoaded, bytesStaticDropSpec] at hpost
      simpa only [sepConj_assoc] using hpost
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_ne : bs.length ≠ 0 := by omega
    by_cases heven : (ptr &&& 1#64) = 0#64
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = (blkPl_237).base := by
        unfold bytesPlacedDropFnAddr
        simp only [hlen_ne, heven, ↓reduceIte]
        rfl
      rw [haddr] at hpc
      have heven_cl := ls_subroutine_ok_of_callee (callerProg := callerProg)
        (promotableEvenDrop_placed_okX hA)
      have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
      have hpre_even :
          s0.mem ⊨ (withLsCodeLoaded lsmpl (promotableEvenDropSpecX A)).pre (ptr, bs, off) s0 ∗ R := by
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecX, bytesData, bytesPtr] at hpre0
        dsimp only [withLsCodeLoaded, promotableEvenDropSpecX]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        refine ⟨hcl, ?_⟩
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpre0
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre0 with ⟨⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact heven_cl.mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_even hsp fun _ hout => hout
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = (blkPl_236).base := by
        unfold bytesPlacedDropFnAddr
        simp only [hlen_ne, heven, ↓reduceIte]
        rfl
      rw [haddr] at hpc
      have hodd_cl := ls_subroutine_ok_of_callee (callerProg := callerProg)
        (promotableOddDrop_placed_okX hA)
      have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
      have hpre_odd :
          s0.mem ⊨ (withLsCodeLoaded lsmpl (promotableOddDropSpecX A)).pre (ptr, bs, off) s0 ∗ R := by
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecX, bytesData, bytesPtr] at hpre0
        dsimp only [withLsCodeLoaded, promotableOddDropSpecX]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        refine ⟨hcl, ?_⟩
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpre0
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre0 with ⟨⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact hodd_cl.mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_odd hsp fun _ hout => hout

theorem bytesVtableDrop_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCl lsmpl (bytesVtableDropSpecX A ptr bs off)) :=
  ls_subroutine_ok_cl_of_withLsCodeLoaded (bytesVtableDrop_placed_okX hA ptr bs off)

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X

