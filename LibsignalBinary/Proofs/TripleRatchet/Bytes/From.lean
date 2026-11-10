/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.BytesCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.CodeLayout -- shake: keep

/-!
# Verification of `<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from`

Verifies `<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from` (`0x423cc`,
Block `250`, 63 instructions, 48-byte stack frame) when `cap = len` across the empty
(`STATIC_VTABLE`), even-pointer (`PROMOTABLE_EVEN_VTABLE`), and odd-pointer
(`PROMOTABLE_ODD_VTABLE`) cases.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Decoded Instructions of `Bytes::from(Vec<u8>)` (`0x423cc..0x424c4`) -/

gen_decodes libsignalSessionCode_tree libsignalTripleRatchetBin [(ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from") → (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" + 248)]

/-- Add instruction-fetch hypotheses for a function in `libsignalSessionCode`. -/
elab "tripleRatchet_fetches " b:term:max H:term:max hfn:term:max off:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat off "tripleRatchet_fetches "))
  let k0Lit := Syntax.mkNumLit "0"
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "tripleRatchet_fetches "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalTripleRatchetBin $b $H $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

/-! ## 2. Memory Region and Buffer Equivalence Helpers -/

theorem stackAt_48_eq_cells (sp : BitVec 64) : stackAt sp 48 = cells (sp - 48#64) 6 := by
  simpa using ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)

theorem memRegion_32_eq_pointsTo64 (out : BitVec 64) :
    memRegion out 32 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (out ↦₆₄ v0) ∗ ((out + 8#64) ↦₆₄ v1) ∗
          ((out + 16#64) ↦₆₄ v2) ∗ ((out + 24#64) ↦₆₄ v3) := by
  rw [show (32 : Nat) = 8 * 4 from rfl, ProofLib.memRegion_cells out 4 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem getLsbD_zero_iff {ptr : BitVec 64} :
    ptr.getLsbD 0 = true ↔ (ptr &&& 1#64) ≠ 0#64 := by
  constructor <;> intro h <;> revert h <;> bv_kernel

theorem not_getLsbD_zero_iff {ptr : BitVec 64} :
    ¬ ptr.getLsbD 0 = true ↔ (ptr &&& 1#64) = 0#64 := by
  constructor <;> intro h <;> revert h <;> bv_kernel

private theorem adrp_static {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")) + 176#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_reloc% (ls_off% "bytes::bytes::static_clone") - page% (ls_off% "<bytes::bytes_mut::BytesMut as bytes::buf::buf_mut::BufMut>::put_slice" + 108))) = b + bv% (ls_reloc% (ls_off% "bytes::bytes::static_clone")) := by
  revert hb; bv_kernel

private theorem adrp_odd {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")) + 204#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE" - page% (ls_off% "<bytes::bytes_mut::BytesMut as bytes::buf::buf_mut::BufMut>::put_slice" + 108))) = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE") := by
  revert hb; bv_kernel

private theorem adrp_even {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")) + 60#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE" - page% (ls_off% "<bytes::bytes_mut::BytesMut as bytes::buf::buf_mut::BufMut>::put_slice" + 108))) = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE") := by
  revert hb; bv_kernel

theorem subroutine_ok_inImage {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout

/-! ## 3. Verification of `<Bytes as From<Vec<u8>>>::from` (`0x423cc`) -/

theorem bytesFromVec_base_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr bytesFromVecName)
      (bytesFromVecSpec A b) := by
  unfold bytesFromVecSpec vecU8At vecHeader bytesAt bytesHeader bytesBoxU8Buf bytesFromVecStack
  simp only [memRegion_32_eq_pointsTo64, stackAt_48_eq_cells]
  cells_unfold
  have hfn := (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")
  tripleRatchet_fetches b (Rust.withPanics ext) hfn (num% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")) 252
  wp_init x s0
  have hadrp_static :
      (((tripleRatchetProgAtExt b ext).fnAddr bytesFromVecName + 176#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_reloc% (ls_off% "bytes::bytes::static_clone") - page% (ls_off% "<bytes::bytes_mut::BytesMut as bytes::buf::buf_mut::BufMut>::put_slice" + 108))) = b + bv% (ls_reloc% (ls_off% "bytes::bytes::static_clone")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")]
    exact adrp_static hb
  have hadrp_odd :
      (((tripleRatchetProgAtExt b ext).fnAddr bytesFromVecName + 204#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE" - page% (ls_off% "<bytes::bytes_mut::BytesMut as bytes::buf::buf_mut::BufMut>::put_slice" + 108))) = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")]
    exact adrp_odd hb
  have hadrp_even :
      (((tripleRatchetProgAtExt b ext).fnAddr bytesFromVecName + 60#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE" - page% (ls_off% "<bytes::bytes_mut::BytesMut as bytes::buf::buf_mut::BufMut>::put_slice" + 108))) = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")]
    exact adrp_even hb
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
  · -- Branch `cap = 0#64` (`bs = []`)
    have hbs_len0 : bs.length = 0 := by
      rw [← ‹cap.toNat = bs.length›, hlen0]; rfl
    wp_steps
    rw [bytesVtable_eq_off]
    simp only [hbs_len0, bytesPtr, bytesData, ite_true, ← hadrp_static]
    wp_done
  · -- Branch `cap ≠ 0#64` (`bs ≠ []`)
    have hbs_len_ne : bs.length ≠ 0 := by
      intro h0
      apply hlen0
      rw [← hcap_eq, h0]
    wp_steps
    wp_if hodd
    · -- Subbranch: `ptr.getLsbD 0 = true` (`(ptr &&& 1#64) ≠ 0#64`, odd pointer)
      have hodd64 : (ptr &&& 1#64) ≠ 0#64 := getLsbD_zero_iff.mp hodd
      wp_steps
      rw [bytesVtable_eq_off]
      simp only [hbs_len_ne, hodd64, bytesPtr, bytesData, ite_false, ← hadrp_odd]
      wp_done
    · -- Subbranch: `¬ ptr.getLsbD 0 = true` (`(ptr &&& 1#64) = 0#64`, even pointer)
      have heven : (ptr &&& 1#64) = 0#64 := not_getLsbD_zero_iff.mp hodd
      wp_steps
      rw [bytesVtable_eq_off]
      simp only [hbs_len_ne, heven, bytesPtr, bytesData, ite_false, ite_true,
        ← hadrp_even]
      wp_done

theorem bytesFromVec_base_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr bytesFromVecName)
      (bytesFromVecSpec A b) :=
  bytesFromVec_base_ok_ext hb

theorem bytesFromVecOk_ext {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} :
    BytesFromVecOkExt img b A ext := by
  intro himg hb
  subst hb
  exact subroutine_ok_inImage img (bytesFromVec_base_ok_ext (base_aligned_of_loads himg))

/-- `<Bytes as From<Vec<u8>>>::from` meets `bytesFromVecSpec` on `tripleRatchetProgAt b C ctl abs`
    under the triple-ratchet hypotheses (`BytesFromVecOk`). -/
theorem bytesFromVecOk {img : Obj.Image} {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)} :
    BytesFromVecOk img b C A ctl S abs :=
  fun _ himg hb => bytesFromVecOk_ext himg hb

/-! ## 4. Relocatable `[LibsignalPlacement]` Contract (Block `250`) -/

theorem bytesFromVec_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_250).rebase (blkPl_250).base H) (blkPl_250).base
      (bytesFromVecPlacedSpec A) := by
  unfold bytesFromVecPlacedSpec vecU8At vecHeader bytesPlacedAt bytesHeader bytesBoxU8Buf bytesFromVecStack
  simp only [memRegion_32_eq_pointsTo64, stackAt_48_eq_cells]
  cells_unfold
  wp_init x s0
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
    simp only [bytesPlacedVtable, staticVtablePlacedAddr, staticVtableSym,
      hbs_len0, bytesPtr, bytesData, ite_true]
    wp_done
  · have hbs_len_ne : bs.length ≠ 0 := by
      intro h0
      apply hlen0
      rw [← hcap_eq, h0]
    wp_steps
    wp_if hodd
    · have hodd64 : (ptr &&& 1#64) ≠ 0#64 := getLsbD_zero_iff.mp hodd
      wp_steps
      simp only [bytesPlacedVtable, promotableOddVtablePlacedAddr, promotableOddVtableName,
        hbs_len_ne, hodd64, bytesPtr, bytesData, ite_false]
      wp_done
    · have heven : (ptr &&& 1#64) = 0#64 := not_getLsbD_zero_iff.mp hodd
      wp_steps
      simp only [bytesPlacedVtable, promotableEvenVtablePlacedAddr, promotableEvenVtableName,
        hbs_len_ne, heven, bytesPtr, bytesData, ite_false, ite_true]
      wp_done

theorem bytesStaticClone_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_226).rebase (blkPl_226).base H) (blkPl_226).base
      bytesStaticClonePlacedSpec := by
  unfold bytesStaticClonePlacedSpec bytesHeader
  simp only [memRegion_32_eq_pointsTo64]
  wp_init x s0
  obtain ⟨out, ptr, len⟩ := x
  dsimp only at *
  apply blkPC_226_pairStep_0x0 _ _ rfl (by simp [*]) (by assumption)
  wp_steps
  wp_done

end CryptoVerification.LibsignalTripleRatchet
