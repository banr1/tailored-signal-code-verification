/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs
public import LibsignalBinary.Proofs.SpqrV1.Chain.SpqrChainCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Auth.SpqrAuthCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Verification of `<spqr::chain::ChainEpochDirection>::next_key_internal`

Proves fixed-image (`nextKeyInternal_ok_ext_x`, `nextKeyInternal_ok_ext`) and relocatable
`[LibsignalPlacement]` (`nextKeyInternal_placed_ok`) contracts for
`<spqr::chain::ChainEpochDirection>::next_key_internal` (`0x5fd94`, Block `362`, 68 instructions),
and defines the relocatable call invariant `LsCallInv`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Keys

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x5a99c → 0x5aaa8]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace NextKeyInternalFacts

theorem nextKeyInternal_fnOff : libsignalSessionCode.fnOff nextKeyInternalName = 0x5a99c :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5a99c

theorem sliceConcat_fnOff : libsignalSessionCode.fnOff sliceConcatName = 0x5eab8 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5eab8

theorem hkdfToSlice_fnOff : libsignalSessionCode.fnOff hkdfToSliceName = 0x5de8c :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5de8c

theorem dealloc_fnOff : libsignalSessionCode.fnOff deallocName =
    num% (ls_off% "__rustc::__rust_dealloc") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_dealloc")

/-- Introduce two `.rodata` slices into a `subroutine_ok` proof for `spec.inImage img`. -/
theorem subroutine_ok_inImage_rodata2_keep {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {roAddr1 roAddr2 : BitVec 64} {roBytes1 roBytes2 : List (BitVec 8)}
    {spec : Spec α}
    (hro1 : ∀ {s : State} (_ : img.FrozenLoaded s) {P : SepProp},
      (s.mem ⊨ P) → (s.mem ⊨ (roAddr1 ↦ᵣ roBytes1) ∗ P))
    (hro2 : ∀ {s : State} (_ : img.FrozenLoaded s) {P : SepProp},
      (s.mem ⊨ P) → (s.mem ⊨ (roAddr2 ↦ᵣ roBytes2) ∗ P))
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
          (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ spec.pre x s
        post := fun x s0 sf =>
          (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, hpre⟩
  have hpre' : s0.mem ⊨
      (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ spec.pre x s0) ∗ R := by
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hL, hro1 hL.1 (hro2 hL.1 hpre)⟩
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only at hq
    rw [sepConj_assoc, sepConj_assoc] at hq
    exact Satisfies.of_sep_right (Satisfies.of_sep_right hq)
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- `.rodata` slice at `0x839e0` (`ls_xref% 0x5fde8 0x5fdec`, 31 bytes): `chainNextInfo`. -/
theorem rodata_chainNextInfo {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x5a9f0 0x5a9f4)) ↦ᵣ chainNextInfo) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x5a9f0 0x5a9f4)) (n := 31) (bs := chainNextInfo)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- `.rodata` slice at `0x83798` (`ls_xref% 0x5fe14 0x5fe18`, 32 bytes): `List.replicate 32 0#8`. -/
theorem rodata_zeros32 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x5aa1c 0x5aa20)) ↦ᵣ List.replicate 32 0#8) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x5aa1c 0x5aa20)) (n := 32) (bs := List.replicate 32 0#8)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- Big-endian 4-byte encoding via `rev32_64` matches `toBEBytes 4`. -/
theorem unpack32_rev32_eq_toBEBytes (v : BitVec 32) :
    unpack32 (BitVec.truncate 32 (rev32_64 (v.zeroExtend 64))) = toBEBytes 4 v := by
  have hr : BitVec.truncate 32 (rev32_64 (v.zeroExtend 64)) =
      v.extractLsb' 0 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 24 8 := by
    simp only [rev32_64]; bv_bits
  rw [hr]
  dsimp only [unpack32, toBEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr]
  generalize v.extractLsb' 0 8 = b0
  generalize v.extractLsb' 8 8 = b1
  generalize v.extractLsb' 16 8 = b2
  generalize v.extractLsb' 24 8 = b3
  refine List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits, rfl⟩⟩⟩⟩

theorem pointsTo32_rev32_eq_toBEBytes (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ BitVec.truncate 32 (rev32_64 (v.zeroExtend 64))) = (a ↦ₛ toBEBytes 4 v) := by
  rw [pointsTo32_eq_pointsToBytes, unpack32_rev32_eq_toBEBytes]

@[simp] theorem toBEBytes_4_length (v : BitVec 32) :
    (toBEBytes 4 v).length = 4 := by
  simp [toBEBytes]

@[simp] theorem chainNextInfo_length :
    chainNextInfo.length = 31 := by decide

theorem list_eq_take_append_drop_take_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    bs = bs.take 32 ++ (bs.drop 32).take 32 := by
  have hd : bs.drop 32 = (bs.drop 32).take 32 := by
    symm
    apply List.take_of_length_le
    simp [h]
  rw [← hd, List.take_append_drop]

theorem take_32_length_of_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    (bs.take 32).length = 32 := by
  simp [h]

theorem drop_32_take_32_length_of_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    ((bs.drop 32).take 32).length = 32 := by
  simp [h]

theorem memRegion_4_eq_pointsTo32 (a : BitVec 64) :
    memRegion a 4 = ∃∗ v : BitVec 32, (a ↦₃₂ v) :=
  memRegion_four a

theorem pointsTo32_entails_memRegion_4 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ memRegion a 4 := by
  rw [memRegion_4_eq_pointsTo32]
  exact Entails.sepExists_right v (Entails.refl _)

/-- Split `stackAt sp nextKeyInternalStackX` (`176 + extHookStack` bytes) into its frame regions. -/
theorem stackAt_nextKeyInternalX_split (sp : BitVec 64) :
    stackAt sp nextKeyInternalStackX =
      stackAt (sp - 176#64) extHookStack ∗
        (∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64, ∃∗ g3 : BitVec 64,
         ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64, ∃∗ g6 : BitVec 64, ∃∗ g7 : BitVec 64,
          ((sp - 176#64) ↦₆₄ g0) ∗ ((sp - 168#64) ↦₆₄ g1) ∗
          ((sp - 160#64) ↦₆₄ g2) ∗ ((sp - 152#64) ↦₆₄ g3) ∗
          ((sp - 144#64) ↦₆₄ g4) ∗ ((sp - 136#64) ↦₆₄ g5) ∗
          ((sp - 128#64) ↦₆₄ g6) ∗ ((sp - 120#64) ↦₆₄ g7)) ∗
        memRegion (sp - 112#64) 24 ∗
        (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
          ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
          ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3)) ∗
        memRegion (sp - 56#64) 4 ∗
        (∃∗ b0 : BitVec 32, (sp - 52#64) ↦₃₂ b0) ∗
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
         ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
          ((sp - 48#64) ↦₆₄ c0) ∗ ((sp - 40#64) ↦₆₄ c1) ∗
          ((sp - 32#64) ↦₆₄ c2) ∗ ((sp - 24#64) ↦₆₄ c3) ∗
          ((sp - 16#64) ↦₆₄ c4) ∗ ((sp - 8#64) ↦₆₄ c5)) := by
  change memRegion (sp - BitVec.ofNat 64 16560) 16560 =
    memRegion (sp - 176#64 - BitVec.ofNat 64 16384) 16384 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16560) (n := 16384) (k := 176)
      (b' := sp - 176#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 176#64) (n := 64) (k := 112)
      (b' := sp - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 112#64) (n := 24) (k := 88)
      (b' := sp - 88#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 88#64) (n := 32) (k := 56)
      (b' := sp - 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 56#64) (n := 4) (k := 52)
      (b' := sp - 52#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 52#64) (n := 4) (k := 48)
      (b' := sp - 48#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16560) 16384 ∗
    (memRegion (sp - 176#64) (8 * 8) ∗
      (memRegion (sp - 112#64) 24 ∗
        (memRegion (sp - 88#64) (8 * 4) ∗
          (memRegion (sp - 56#64) 4 ∗
            (memRegion (sp - 52#64) 4 ∗ memRegion (sp - 48#64) (8 * 6)))))) = _
  rw [ProofLib.memRegion_cells (sp - 176#64) 8 (by decide),
    ProofLib.memRegion_cells (sp - 88#64) 4 (by decide),
    memRegion_4_eq_pointsTo32 (sp - 52#64),
    ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]
  have hsub : sp - 176#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16560 := by bv_kernel
  have hc8 : cells (sp - 176#64) 8 =
      (∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64, ∃∗ g3 : BitVec 64,
       ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64, ∃∗ g6 : BitVec 64, ∃∗ g7 : BitVec 64,
        ((sp - 176#64) ↦₆₄ g0) ∗ ((sp - 168#64) ↦₆₄ g1) ∗
        ((sp - 160#64) ↦₆₄ g2) ∗ ((sp - 152#64) ↦₆₄ g3) ∗
        ((sp - 144#64) ↦₆₄ g4) ∗ ((sp - 136#64) ↦₆₄ g5) ∗
        ((sp - 128#64) ↦₆₄ g6) ∗ ((sp - 120#64) ↦₆₄ g7)) := by
    cells_unfold
  have hc4 : cells (sp - 88#64) 4 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
        ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
        ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3)) := by
    cells_unfold
  have hc6 : cells (sp - 48#64) 6 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
       ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ c0) ∗ ((sp - 40#64) ↦₆₄ c1) ∗
        ((sp - 32#64) ↦₆₄ c2) ∗ ((sp - 24#64) ↦₆₄ c3) ∗
        ((sp - 16#64) ↦₆₄ c4) ∗ ((sp - 8#64) ↦₆₄ c5)) := by
    cells_unfold
  rw [hsub, hc8, hc4, hc6]

/-- Fold 8 64-bit cells at `sp - 176#64` into `memRegion (sp - 176#64) 64`. -/
theorem cells8_entails_memRegion_64 (sp : BitVec 64) (g0 g1 g2 g3 g4 g5 g6 g7 : BitVec 64) :
    ((sp - 176#64) ↦₆₄ g0) ∗ ((sp - 168#64) ↦₆₄ g1) ∗
      ((sp - 160#64) ↦₆₄ g2) ∗ ((sp - 152#64) ↦₆₄ g3) ∗
      ((sp - 144#64) ↦₆₄ g4) ∗ ((sp - 136#64) ↦₆₄ g5) ∗
      ((sp - 128#64) ↦₆₄ g6) ∗ ((sp - 120#64) ↦₆₄ g7) ⊢
      memRegion (sp - 176#64) 64 := by
  change _ ⊢ memRegion (sp - 176#64) (8 * 8)
  rw [ProofLib.memRegion_cells (sp - 176#64) 8 (by decide)]
  cells_unfold
  exact Entails.sepExists_right g0
    (Entails.sepExists_right g1
      (Entails.sepExists_right g2
        (Entails.sepExists_right g3
          (Entails.sepExists_right g4
            (Entails.sepExists_right g5
              (Entails.sepExists_right g6
                (Entails.sepExists_right g7 (Entails.refl _))))))))

/-- Split `memRegion out 36` into a 32-bit cell at `out` and four 64-bit cells at `out + 4..28`. -/
theorem memRegion_36_out_split (out : BitVec 64) :
    memRegion out 36 =
      (∃∗ v0 : BitVec 32, out ↦₃₂ v0) ∗
        (∃∗ v1 : BitVec 64, (out + 4#64) ↦₆₄ v1) ∗
        (∃∗ v2 : BitVec 64, (out + 12#64) ↦₆₄ v2) ∗
        (∃∗ v3 : BitVec 64, (out + 20#64) ↦₆₄ v3) ∗
        (∃∗ v4 : BitVec 64, (out + 28#64) ↦₆₄ v4) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 4) (k := 32)
      (b' := out + 4#64) rfl (by bv_omega) (by decide),
    memRegion_4_eq_pointsTo32 out, memRegion_32_cells (out + 4#64)]
  have h12 : out + 4#64 + 8#64 = out + 12#64 := by bv_kernel
  have h20 : out + 4#64 + 16#64 = out + 20#64 := by bv_kernel
  have h28 : out + 4#64 + 24#64 = out + 28#64 := by bv_kernel
  rw [h12, h20, h28]

/-- Rejoin the `next_key_internal` stack frame back into `stackAt sp nextKeyInternalStackX`. -/
theorem rejoin_stack_nextKeyInternalX (sp : BitVec 64)
    (g0 g1 g2 g3 g4 g5 g6 g7 : BitVec 64)
    (v0 v1 v2 : BitVec 64)
    (s0 s1 s2 s3 : BitVec 64)
    {beBytes : List (BitVec 8)} (hbe : beBytes.length = 4)
    (c0 c1 c2 c3 c4 c5 : BitVec 64) :
    stackAt (sp - 176#64) extHookStack ∗
      ((sp - 176#64) ↦₆₄ g0) ∗ ((sp - 168#64) ↦₆₄ g1) ∗
      ((sp - 160#64) ↦₆₄ g2) ∗ ((sp - 152#64) ↦₆₄ g3) ∗
      ((sp - 144#64) ↦₆₄ g4) ∗ ((sp - 136#64) ↦₆₄ g5) ∗
      ((sp - 128#64) ↦₆₄ g6) ∗ ((sp - 120#64) ↦₆₄ g7) ∗
      ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
      ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
      ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
      memRegion (sp - 56#64) 4 ∗
      ((sp - 52#64) ↦ₛ beBytes) ∗
      ((sp - 48#64) ↦₆₄ c0) ∗ ((sp - 40#64) ↦₆₄ c1) ∗
      ((sp - 32#64) ↦₆₄ c2) ∗ ((sp - 24#64) ↦₆₄ c3) ∗
      ((sp - 16#64) ↦₆₄ c4) ∗ ((sp - 8#64) ↦₆₄ c5) ⊢
      stackAt sp nextKeyInternalStackX := by
  have heq : stackAt sp nextKeyInternalStackX =
      stackAt (sp - 176#64) extHookStack ∗
        cells (sp - 176#64) 15 ∗
        memRegion (sp - 56#64) 4 ∗
        memRegion (sp - 52#64) 4 ∗
        cells (sp - 48#64) 6 := by
    change memRegion (sp - BitVec.ofNat 64 16560) 16560 =
      memRegion (sp - 176#64 - BitVec.ofNat 64 16384) 16384 ∗ _
    rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16560) (n := 16384) (k := 176)
        (b' := sp - 176#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 176#64) (n := 120) (k := 56)
        (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 4) (k := 52)
        (b' := sp - 52#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 52#64) (n := 4) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide)]
    change memRegion (sp - BitVec.ofNat 64 16560) 16384 ∗
      (memRegion (sp - 176#64) (8 * 15) ∗
        (memRegion (sp - 56#64) 4 ∗
          (memRegion (sp - 52#64) 4 ∗ memRegion (sp - 48#64) (8 * 6)))) = _
    rw [ProofLib.memRegion_cells (sp - 176#64) 15 (by decide),
      ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]
    have hsub : sp - 176#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16560 := by bv_kernel
    rw [hsub]
  rw [heq]
  have hc15 :
      (((sp - 176#64) ↦₆₄ g0) ∗ ((sp - 168#64) ↦₆₄ g1) ∗
       ((sp - 160#64) ↦₆₄ g2) ∗ ((sp - 152#64) ↦₆₄ g3) ∗
       ((sp - 144#64) ↦₆₄ g4) ∗ ((sp - 136#64) ↦₆₄ g5) ∗
       ((sp - 128#64) ↦₆₄ g6) ∗ ((sp - 120#64) ↦₆₄ g7) ∗
       ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
       ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
       ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3)) ⊢ cells (sp - 176#64) 15 := by
    cells_unfold
    exact Entails.sepExists_right g0 (Entails.sepExists_right g1 (Entails.sepExists_right g2
      (Entails.sepExists_right g3 (Entails.sepExists_right g4 (Entails.sepExists_right g5
        (Entails.sepExists_right g6 (Entails.sepExists_right g7 (Entails.sepExists_right v0
          (Entails.sepExists_right v1 (Entails.sepExists_right v2 (Entails.sepExists_right s0
            (Entails.sepExists_right s1 (Entails.sepExists_right s2
              (Entails.sepExists_right s3 (Entails.refl _)))))))))))))))
  have hmbe : ((sp - 52#64) ↦ₛ beBytes) ⊢ memRegion (sp - 52#64) 4 :=
    hbe ▸ pointsToBytes_entails_memRegion (sp - 52#64) beBytes
  have hc6 :
      (((sp - 48#64) ↦₆₄ c0) ∗ ((sp - 40#64) ↦₆₄ c1) ∗
       ((sp - 32#64) ↦₆₄ c2) ∗ ((sp - 24#64) ↦₆₄ c3) ∗
       ((sp - 16#64) ↦₆₄ c4) ∗ ((sp - 8#64) ↦₆₄ c5)) ⊢ cells (sp - 48#64) 6 := by
    cells_unfold
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4
        (Entails.sepExists_right c5 (Entails.refl _))))))
  have hgroup :
      stackAt (sp - 176#64) extHookStack ∗
        ((sp - 176#64) ↦₆₄ g0) ∗ ((sp - 168#64) ↦₆₄ g1) ∗
        ((sp - 160#64) ↦₆₄ g2) ∗ ((sp - 152#64) ↦₆₄ g3) ∗
        ((sp - 144#64) ↦₆₄ g4) ∗ ((sp - 136#64) ↦₆₄ g5) ∗
        ((sp - 128#64) ↦₆₄ g6) ∗ ((sp - 120#64) ↦₆₄ g7) ∗
        ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
        ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
        ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3) ∗
        memRegion (sp - 56#64) 4 ∗
        ((sp - 52#64) ↦ₛ beBytes) ∗
        ((sp - 48#64) ↦₆₄ c0) ∗ ((sp - 40#64) ↦₆₄ c1) ∗
        ((sp - 32#64) ↦₆₄ c2) ∗ ((sp - 24#64) ↦₆₄ c3) ∗
        ((sp - 16#64) ↦₆₄ c4) ∗ ((sp - 8#64) ↦₆₄ c5) =
      stackAt (sp - 176#64) extHookStack ∗
        (((sp - 176#64) ↦₆₄ g0) ∗ ((sp - 168#64) ↦₆₄ g1) ∗
         ((sp - 160#64) ↦₆₄ g2) ∗ ((sp - 152#64) ↦₆₄ g3) ∗
         ((sp - 144#64) ↦₆₄ g4) ∗ ((sp - 136#64) ↦₆₄ g5) ∗
         ((sp - 128#64) ↦₆₄ g6) ∗ ((sp - 120#64) ↦₆₄ g7) ∗
         ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v2) ∗
         ((sp - 88#64) ↦₆₄ s0) ∗ ((sp - 80#64) ↦₆₄ s1) ∗
         ((sp - 72#64) ↦₆₄ s2) ∗ ((sp - 64#64) ↦₆₄ s3)) ∗
        memRegion (sp - 56#64) 4 ∗
        ((sp - 52#64) ↦ₛ beBytes) ∗
        (((sp - 48#64) ↦₆₄ c0) ∗ ((sp - 40#64) ↦₆₄ c1) ∗
         ((sp - 32#64) ↦₆₄ c2) ∗ ((sp - 24#64) ↦₆₄ c3) ∗
         ((sp - 16#64) ↦₆₄ c4) ∗ ((sp - 8#64) ↦₆₄ c5)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono hc15 (sepConj_mono_right (sepConj_mono hmbe hc6)))

/-- Unpack a non-empty `vecU8 A v bs` (`0 < bs.length`) into its header and live buffer. -/
theorem vecU8_nonempty_entails (A : RustAlloc) (v : BitVec 64) {bs : List (BitVec 8)}
    (hpos : 0 < bs.length) :
    vecU8 A v bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
  simp only [vecU8, vecU8At, vecHeader, sepConj_assoc]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [show (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  have hcap_pos : 0 < cap.toNat := Nat.lt_of_lt_of_le hpos hle
  have hcap_ne : cap ≠ 0 := by
    intro h0; subst h0; simp at hcap_pos
  have hlayout : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
  simp only [hcap_ne, ↓reduceIte]
  exact Entails.pure_right ⟨hcap_ne, hlayout, hptr, hle⟩ (Entails.refl _)

/-- Rejoin `(ptr ↦ₛ bs) ∗ memRegion (ptr + bs.length) (cap - bs.length)` into `memRegion ptr cap`. -/
theorem pointsToBytes_memRegion_entails (ptr : BitVec 64) {bs : List (BitVec 8)} {cap : Nat}
    (hle : bs.length ≤ cap) (hlayout : LayoutOk cap 1) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length) ⊢
      memRegion ptr cap := by
  have h1 : (ptr ↦ₛ bs) ⊢ memRegion ptr bs.length := pointsToBytes_entails_memRegion ptr bs
  have hcap_le : cap ≤ 2 ^ 64 := by
    have := hlayout.2.2
    omega
  have h2 : memRegion ptr bs.length ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length) = memRegion ptr cap := by
    have hsplit := ProofLib.memRegion_split ptr bs.length (cap - bs.length)
      (by rw [Nat.add_sub_of_le hle]; exact hcap_le)
    rw [Nat.add_sub_of_le hle] at hsplit
    exact hsplit.symm
  rw [← h2]
  exact sepConj_mono_left h1

theorem SepWP.pure_left_focus {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop} (φ : Prop)
    (hf : P = ⌜φ⌝ ∗ P')
    (h : φ → SepWP prog pc s P' post) :
    SepWP prog pc s P post := by
  unfold SepWP
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact (h hm.1).elim hm.2 hL

theorem onPanic_entails_of_trace_eq {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem SepWPp.call_allowPanic_inImage_ret {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧
      (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call_wpp_frozen hcall (x := x) (F := F) hF.1 hF.2 hpc hrun hsp_align hlr
    (fun R' hm => by
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF.1, hF.2⟩, hpre R' hm⟩)
    (fun sf code R' _ hpost => by
      dsimp only [Spec.inImage] at hpost
      rw [hexit_eq.1] at hpost
      exact not_satisfies_false_sepConj hpost)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    (fun sm hpcm hrunm hspm hcsm hfz_m hsym_m =>
      SepWPp.of_sepWP_ret (hnext sm hpcm hrunm hspm hcsm ⟨hfz_m, hsym_m⟩))
    (fun sf R' _ hpost => by
      dsimp only [Spec.inImage] at hpost
      rw [hexit_eq.2] at hpost
      exact (not_satisfies_false_sepConj hpost).elim)

open Lean Elab Tactic in
elab "wpp_call_inImage_ret " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_inImage_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_inImage_ret: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_entails_of_trace_eq (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

end NextKeyInternalFacts

open NextKeyInternalFacts
open AgreeStateSimp

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_4_length chainNextInfo_length
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  nextKeyInternal_fnOff sliceConcat_fnOff hkdfToSlice_fnOff dealloc_fnOff
  libsignalSessionCode_fnOff_0x5a99c
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")

theorem exists_unpack64_of_length_64_split {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs.take 32) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ (bs.drop 32).take 32) =
          (a ↦₆₄ w4) ∗ ((a + 8#64) ↦₆₄ w5) ∗ ((a + 16#64) ↦₆₄ w6) ∗ ((a + 24#64) ↦₆₄ w7)) := by
  have h1 : (bs.take 32).length = 32 := by simp [h]
  have h2 : (bs.drop 32).length = 32 := by simp [h]
  have hdrop_take : (bs.drop 32).take 32 = bs.drop 32 := List.take_of_length_le (by omega)
  obtain ⟨w0, w1, w2, w3, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w4, w5, w6, w7, _, hp2⟩ := exists_unpack64_of_length_32 h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_, hp1, fun a => by rw [hdrop_take, hp2]⟩
  conv_lhs => rw [← List.take_append_drop 32 bs]
  rw [pointsToBytes_append, h1, hp1, hp2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

set_option maxHeartbeats 1600000 in
theorem nextKeyInternal_ok_of_contracts_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext)
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    NextKeyInternalOkX img hkdf A ext := by
  unfold NextKeyInternalOkX tripleRatchetProgAtExt
  refine subroutine_ok_inImage_rodata2_keep (rodata_chainNextInfo himg) (rodata_zeros32 himg) ?_
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff nextKeyInternalName = 0x5a99c :=
    nextKeyInternal_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5a99c 272
  have h_concat := sub_ok_at_rebase (name := nextKeyInternalName) (callee := sliceConcatName)
    (k := num% (0x5eab8 - 0x5a99c)) (by rw [nextKeyInternal_fnOff, sliceConcat_fnOff]) hconcat
  have h_hkdf := sub_ok_at_rebase (name := nextKeyInternalName) (callee := hkdfToSliceName)
    (k := num% (0x5de8c - 0x5a99c)) (by rw [nextKeyInternal_fnOff, hkdfToSlice_fnOff]) hhkdf
  have h_dealloc := sub_ok_at_rebase (name := nextKeyInternalName) (callee := deallocName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x5a99c))
    (by rw [nextKeyInternal_fnOff, dealloc_fnOff]) hdealloc
  have hadrp1 : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      nextKeyInternalName + 84#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x5a9f0 0x5a9f4 - 0x5a000) =
      img.base + bv% (ls_xref% 0x5a9f0 0x5a9f4) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  have hadrp2 : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      nextKeyInternalName + 128#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x5aa1c 0x5aa20 - 0x5a000) =
      img.base + bv% (ls_xref% 0x5aa1c 0x5aa20) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear himg hconcat hhkdf hdealloc hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      nextKeyInternalName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨out, nextA, next, ctrA, ctr⟩
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_3 h_4 h_6
  refine SepWPp.rw_pre (by
    rw [stackAt_nextKeyInternalX_split s0.sp,
      memRegion_36_out_split (s0.readReg64 (.gpr 0#5))]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5eab8 - 0x5a99c)) hinv0 ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (pointsTo32_rev32_eq_toBEBytes (s0.sp - 52#64) (ctr + 1#32))) (by sep_focus) ?_
  refine SepWP.fold (cells8_entails_memRegion_64 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_ret h_concat
    (⟨s0.sp - 112#64, s0.sp - 88#64, false, s0.sp - 52#64, toBEBytes 4 (ctr + 1#32),
      true, img.base + bv% (ls_xref% 0x5a9f0 0x5a9f4), chainNextInfo⟩ : SliceConcat2Ghost)
    hinv1
  have hinfo_pos : 0 < (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length := by simp
  refine SepWP.fold (vecU8_nonempty_entails A (s0.sp - 112#64) hinfo_pos) (by sep_focus) ?_
  sep_elim_exists
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_ne, hlayout, hptr_ne, hle⟩
  have ⟨hpos1, hpow1, hisize⟩ := hlayout
  apply SepWP.seq_inImage (mid := entry + bv% (0x5de8c - 0x5a99c)) hF_sf
  wp_steps
  have hstack_sf : stackAt (s0.sp - 176#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 176#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have ⟨hF2, hsym2⟩ := hinv2
  have hnext_lt : next.length < 2 ^ 63 := by omega
  have hinfo_ge : 32 ≤ (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length := by simp
  have hinfo_lt : (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length < 55 := by simp
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x5a99c)) hinv2
  wp_call h_hkdf
    (⟨true, img.base + bv% (ls_xref% 0x5aa1c 0x5aa20), List.replicate 32 0#8,
      false, s0.readReg64 (.gpr 1#5), next,
      false, _, toBEBytes 4 (ctr + 1#32) ++ chainNextInfo,
      s0.sp - 176#64, 64⟩ : HkdfToSliceGhost)
  wp_steps
  refine SepWP.fold (pointsToBytes_memRegion_entails _ hle hlayout) (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rintro ⟨hF3, hsym3⟩
  wp_call h_dealloc (_, _, 1)
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm_all, hokm_take, hokm_drop⟩ :=
    exists_unpack64_of_length_64_split ‹List.length (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64) = 64›
  obtain ⟨n0, n1, n2, n3, -, hnext_cells⟩ := exists_unpack64_of_length_32 ‹next.length = 32›
  have hokm_sp := hokm_all (s0.sp - 176#64)
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hokm_sp
  refine SepWP.fold (Entails.of_eq hokm_sp) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hnext_cells (s0.readReg64 (.gpr 1#5)))) (by sep_focus) ?_
  wp_steps
  have hokm_out := (hokm_drop (s0.readReg64 (.gpr 0#5) + 4#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hokm_out
  refine SepWP.fold (Entails.of_eq hokm_out) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hokm_take (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hstack_sf.trans hstack_sf1).symm) (by sep_focus) ?_
  have hbe_len : (toBEBytes 4 (ctr + 1#32)).length = 4 := by simp
  refine SepWP.fold (rejoin_stack_nextKeyInternalX s0.sp w0 w1 w2 w3 w4 w5 w6 w7 _ _ _ _ _ _ _ hbe_len _ _ _ _ _ _) (by sep_focus) ?_
  have hkey_len :
      (List.take 32
        (List.drop 32
          (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64))).length = 32 := by
    rw [List.length_take_of_le (by
      rw [List.length_drop, ‹List.length (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64) = 64›])]
  dsimp only [nextKeyOutAt, nextKeyOut, nextKeyNext, ChainEpochDirection.nextKeyInternal, sepConj_assoc]
  wp_done

theorem nextKeyInternal_ok_ext_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext)
    (hA : AllocContractsX img A ext) :
    NextKeyInternalOkX img hkdf A ext :=
  nextKeyInternal_ok_of_contracts_x himg hconcat hhkdf hA.dealloc

/-! ## Contract-Backed (`*Ext`) Proofs (`nextKeyInternalStackExt = 17792` B) -/

private theorem stackAt_nextKeyInternalExt_eq (sp : BitVec 64) :
    stackAt sp nextKeyInternalStackExt =
      memRegion (sp - 17792#64) 1232 ∗ stackAt sp nextKeyInternalStackX := by
  change memRegion (sp - BitVec.ofNat 64 17792) 17792 =
    memRegion (sp - 17792#64) 1232 ∗ memRegion (sp - BitVec.ofNat 64 16560) 16560
  exact ProofLib.memRegion_split' (b := sp - 17792#64) (n := 1232) (k := 16560)
    (b' := sp - 16560#64) rfl (by bv_omega) (by decide)

private theorem stackAt_hkdfToSliceExt_eq (sp sp' : BitVec 64) (hsp : sp' = sp - 176#64) :
    memRegion (sp - 17792#64) 1232 ∗ stackAt sp' extHookStack =
      stackAt sp' hkdfToSliceStackExt := by
  subst hsp
  change memRegion (sp - 17792#64) 1232 ∗ memRegion (sp - 176#64 - BitVec.ofNat 64 16384) 16384 =
    memRegion (sp - 176#64 - BitVec.ofNat 64 17616) 17616
  have h1 : sp - 176#64 - BitVec.ofNat 64 17616 = sp - 17792#64 := by bv_kernel
  have h2 : sp - 176#64 - BitVec.ofNat 64 16384 = sp - 16560#64 := by bv_kernel
  rw [h1, h2]
  exact (ProofLib.memRegion_split' (b := sp - 17792#64) (n := 1232) (k := 16384)
    (b' := sp - 16560#64) rfl (by bv_omega) (by decide)).symm

set_option maxHeartbeats 1600000 in
theorem nextKeyInternal_ok_of_contracts_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    NextKeyInternalOkExt img hkdf A ext := by
  unfold NextKeyInternalOkExt tripleRatchetProgAtExt
  refine subroutine_ok_inImage_rodata2_keep (rodata_chainNextInfo himg) (rodata_zeros32 himg) ?_
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff nextKeyInternalName = 0x5a99c :=
    nextKeyInternal_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5a99c 272
  have h_concat := sub_ok_at_rebase (name := nextKeyInternalName) (callee := sliceConcatName)
    (k := num% (0x5eab8 - 0x5a99c)) (by rw [nextKeyInternal_fnOff, sliceConcat_fnOff]) hconcat
  have h_hkdf := sub_ok_at_rebase (name := nextKeyInternalName) (callee := hkdfToSliceName)
    (k := num% (0x5de8c - 0x5a99c)) (by rw [nextKeyInternal_fnOff, hkdfToSlice_fnOff]) hhkdf
  have h_dealloc := sub_ok_at_rebase (name := nextKeyInternalName) (callee := deallocName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x5a99c))
    (by rw [nextKeyInternal_fnOff, dealloc_fnOff]) hdealloc
  have hadrp1 : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      nextKeyInternalName + 84#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x5a9f0 0x5a9f4 - 0x5a000) =
      img.base + bv% (ls_xref% 0x5a9f0 0x5a9f4) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  have hadrp2 : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      nextKeyInternalName + 128#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x5aa1c 0x5aa20 - 0x5a000) =
      img.base + bv% (ls_xref% 0x5aa1c 0x5aa20) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear himg hconcat hhkdf hdealloc hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      nextKeyInternalName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨out, nextA, next, ctrA, ctr⟩
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_3 h_4 h_6
  refine SepWPp.rw_pre (by
    rw [stackAt_nextKeyInternalExt_eq s0.sp, stackAt_nextKeyInternalX_split s0.sp,
      memRegion_36_out_split (s0.readReg64 (.gpr 0#5))]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5eab8 - 0x5a99c)) hinv0 ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (pointsTo32_rev32_eq_toBEBytes (s0.sp - 52#64) (ctr + 1#32))) (by sep_focus) ?_
  refine SepWP.fold (cells8_entails_memRegion_64 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_ret h_concat
    (⟨s0.sp - 112#64, s0.sp - 88#64, false, s0.sp - 52#64, toBEBytes 4 (ctr + 1#32),
      true, img.base + bv% (ls_xref% 0x5a9f0 0x5a9f4), chainNextInfo⟩ : SliceConcat2Ghost)
    hinv1
  have hinfo_pos : 0 < (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length := by simp
  refine SepWP.fold (vecU8_nonempty_entails A (s0.sp - 112#64) hinfo_pos) (by sep_focus) ?_
  sep_elim_exists
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_ne, hlayout, hptr_ne, hle⟩
  have ⟨hpos1, hpow1, hisize⟩ := hlayout
  apply SepWP.seq_inImage (mid := entry + bv% (0x5de8c - 0x5a99c)) hF_sf
  wp_steps
  have hstack_ext := stackAt_hkdfToSliceExt_eq s0.sp sf.sp ‹sf.sp = s0.sp - 176#64›
  refine SepWP.fold (Entails.of_eq hstack_ext) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have ⟨hF2, hsym2⟩ := hinv2
  have hnext_lt : next.length < 2 ^ 63 := by omega
  have hinfo_ge : 32 ≤ (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length := by simp
  have hinfo_lt : (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length < 55 := by simp
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x5a99c)) hinv2
  wp_call h_hkdf
    (⟨true, img.base + bv% (ls_xref% 0x5aa1c 0x5aa20), List.replicate 32 0#8,
      false, s0.readReg64 (.gpr 1#5), next,
      false, _, toBEBytes 4 (ctr + 1#32) ++ chainNextInfo,
      s0.sp - 176#64, 64⟩ : HkdfToSliceGhost)
  wp_steps
  refine SepWP.fold (pointsToBytes_memRegion_entails _ hle hlayout) (by sep_focus) ?_
  have hstack_unsplit :
      stackAt sf.sp hkdfToSliceStackExt =
        memRegion (s0.sp - 17792#64) 1232 ∗ stackAt sf_1.sp extHookStack := by
    rw [← hstack_ext, ‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_unsplit) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rintro ⟨hF3, hsym3⟩
  wp_call h_dealloc (_, _, 1)
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm_all, hokm_take, hokm_drop⟩ :=
    exists_unpack64_of_length_64_split ‹List.length (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64) = 64›
  obtain ⟨n0, n1, n2, n3, -, hnext_cells⟩ := exists_unpack64_of_length_32 ‹next.length = 32›
  have hokm_sp := hokm_all (s0.sp - 176#64)
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hokm_sp
  refine SepWP.fold (Entails.of_eq hokm_sp) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hnext_cells (s0.readReg64 (.gpr 1#5)))) (by sep_focus) ?_
  wp_steps
  have hokm_out := (hokm_drop (s0.readReg64 (.gpr 0#5) + 4#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hokm_out
  refine SepWP.fold (Entails.of_eq hokm_out) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hokm_take (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  have hstack_back : stackAt sf_1.sp extHookStack = stackAt (s0.sp - 176#64) extHookStack := by
    rw [‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 176#64›]
  refine SepWP.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
  have hbe_len : (toBEBytes 4 (ctr + 1#32)).length = 4 := by simp
  refine SepWP.fold (rejoin_stack_nextKeyInternalX s0.sp w0 w1 w2 w3 w4 w5 w6 w7 _ _ _ _ _ _ _ hbe_len _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalExt_eq s0.sp).symm) (by sep_focus) ?_
  have hkey_len :
      (List.take 32
        (List.drop 32
          (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64))).length = 32 := by
    rw [List.length_take_of_le (by
      rw [List.length_drop, ‹List.length (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64) = 64›])]
  dsimp only [nextKeyOutAt, nextKeyOut, nextKeyNext, ChainEpochDirection.nextKeyInternal, sepConj_assoc]
  wp_done

theorem nextKeyInternal_ok_ext_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hA : AllocContractsX img A ext) :
    NextKeyInternalOkExt img hkdf A ext :=
  nextKeyInternal_ok_of_contracts_ext himg hconcat hhkdf hA.dealloc

abbrev nextKeyInternal_ok_ext := @nextKeyInternal_ok_ext_ext

/-! ## Relocatable `[LibsignalPlacement]` Call Invariant and Block `362` Contract -/

namespace NextKeyInternalFacts

/-- Combined `.rodata` + unmutated-block code-loaded call invariant for `[LibsignalPlacement]`. -/
def LsCallInv (pl : Obj.MultiPlacement) (m : Memory) : Prop :=
  LibsignalRoLoaded pl m ∧ LibsignalCodeLoaded pl m

theorem LsCallInv.of_keepsFrozen {pl : Obj.MultiPlacement} {m m' : Memory}
    (h : LsCallInv pl m) (hk : m.KeepsFrozen m') : LsCallInv pl m' :=
  ⟨libsignalRoLoaded_of_keepsFrozen h.1 hk, h.2.of_keepsFrozen hk⟩

theorem LsCallInv.of_steps {pl : Obj.MultiPlacement} {prog : Program} {s s' : State}
    (h : LsCallInv pl s.mem) (hs : Steps prog s s') : LsCallInv pl s'.mem :=
  h.of_keepsFrozen (Steps.keepsFrozen hs)

/-- Wrap `spec` with `⌜LsCallInv pl s.mem⌝` in `pre` (relocatable counterpart of `Spec.inImage`). -/
def withLsCallInv {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜LsCallInv pl s.mem⌝ ∗ spec.pre x s }

theorem subroutine_ok_withLsCallInv_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCallInv pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      dsimp only [withLsCallInv] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hp.2)
    (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsCallInv_of_withLsCodeLoaded {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsCallInv pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      dsimp only [withLsCallInv, withLsCodeLoaded] at hp ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hp.1.2, hp.2⟩)
    (fun _ _ _ _ hq => hq)

theorem ls_subroutine_ok_callInv_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCallInv lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCallInv lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by
    dsimp only [withLsCallInv] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1.2
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

theorem subroutine_ok_withLsCallInv_rodata1_keep {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {addr : BitVec 64} {bs : List (BitVec 8)}
    (hro : ∀ {m : Memory}, LsCallInv pl m → ∀ {P : SepProp}, (m ⊨ P) → m ⊨ (addr ↦ᵣ bs) ∗ P)
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜LsCallInv pl s.mem⌝ ∗ (addr ↦ᵣ bs) ∗ spec.pre x s
        post := fun x s0 sf => (addr ↦ᵣ bs) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (withLsCallInv pl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [withLsCallInv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, hpre⟩
  have hpre' : s0.mem ⊨
      (⌜LsCallInv pl s0.mem⌝ ∗ (addr ↦ᵣ bs) ∗ spec.pre x s0) ∗ R := by
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hL, hro hL hpre⟩
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only at hq
    rw [sepConj_assoc] at hq
    exact Satisfies.of_sep_right hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem subroutine_ok_withLsCallInv_rodata2_keep {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {roAddr1 roAddr2 : BitVec 64} {roBytes1 roBytes2 : List (BitVec 8)}
    {spec : Spec α}
    (hro1 : ∀ {m : Memory}, LsCallInv pl m → ∀ {P : SepProp}, (m ⊨ P) → m ⊨ (roAddr1 ↦ᵣ roBytes1) ∗ P)
    (hro2 : ∀ {m : Memory}, LsCallInv pl m → ∀ {P : SepProp}, (m ⊨ P) → m ⊨ (roAddr2 ↦ᵣ roBytes2) ∗ P)
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜LsCallInv pl s.mem⌝ ∗
          (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ spec.pre x s
        post := fun x s0 sf =>
          (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (withLsCallInv pl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [withLsCallInv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, hpre⟩
  have hpre' : s0.mem ⊨
      (⌜LsCallInv pl s0.mem⌝ ∗
        (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ spec.pre x s0) ∗ R := by
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hL, hro1 hL (hro2 hL hpre)⟩
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only at hq
    rw [sepConj_assoc, sepConj_assoc] at hq
    exact Satisfies.of_sep_right (Satisfies.of_sep_right hq)
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem rodata_chainNextInfo_placed [LibsignalPlacement] {m : Memory}
    (hF : LsCallInv lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ "spqr:.rodata..Lanon.161") ↦ᵣ chainNextInfo) ∗ P :=
  lsro_intro_chk hF.1 (by decide +kernel) hP

theorem rodata_zeros32_placed [LibsignalPlacement] {m : Memory}
    (hF : LsCallInv lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ "spqr:.rodata.cst32+0x0") ↦ᵣ List.replicate 32 0#8) ∗ P :=
  lsro_intro_chk hF.1 (by decide +kernel) hP

theorem SepWP.seq_lsCallInv {prog : Program} {pl : Obj.MultiPlacement}
    {mid target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LsCallInv pl sm.mem → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  SepWP.seq_frozen (fun _ _ hf hkf => LsCallInv.of_keepsFrozen hf hkf) hF h

theorem SepWPp.of_sepWP_lsCallInv {prog : Program} {pl : Obj.MultiPlacement}
    {mid target_pc : BitVec 64} {s : State} {P : SepProp}
    {post post_err : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LsCallInv pl sm.mem → SepWPp prog target_pc sm Pm post post_err)) :
    SepWPp prog target_pc s P post post_err :=
  SepWPp.seq_frozen (fun _ _ hf hkf => LsCallInv.of_keepsFrozen hf hkf) hF h

theorem SepWPp.call_allowPanic_lsCallInv_mid {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCallInv pl spec))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧
      (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsCallInv pl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  have hpre_inv : s.mem ⊨ (withLsCallInv pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCallInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hF, hpre R' hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre_inv hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      (hnext sm hpcm hrunm hspm hcsm (hF.of_steps hsteps))
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · dsimp only [withLsCallInv] at hpost
    rw [hexit_eq.1] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCallInv] at hpost
    rw [hexit_eq.2] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem SepWPp.call_allowPanic_lsCallInv_ret {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCallInv pl spec))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧
      (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsCallInv pl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  have hpre_inv : s.mem ⊨ (withLsCallInv pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCallInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hF, hpre R' hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre_inv hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      (SepWPp.of_sepWP_ret (hnext sm hpcm hrunm hspm hcsm (hF.of_steps hsteps)))
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · dsimp only [withLsCallInv] at hpost
    rw [hexit_eq.1] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCallInv] at hpost
    rw [hexit_eq.2] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

open Lean Elab Tactic in
elab "wpp_call_lsCallInv_ret " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_lsCallInv_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_lsCallInv_ret: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_entails_of_trace_eq (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

end NextKeyInternalFacts

set_option maxHeartbeats 1600000 in
/-- Relocatable `<spqr::chain::ChainEpochDirection>::next_key_internal` (Block `362`) meets
`withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)` under `[LibsignalPlacement]`. -/
theorem nextKeyInternal_placed_ok [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat2Spec A)))
    (h_hkdf : subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (hkdfToSliceSpqrSpec hkdf)))
    (h_dealloc : subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack)) :
    subroutine_ok ((blkPC_362).rebase (blkPl_362).base H) (blkPl_362).base
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)) := by
  refine subroutine_ok_withLsCallInv_rodata2_keep
    rodata_chainNextInfo_placed rodata_zeros32_placed ?_
  wpp_init x s0
  rcases x with ⟨out, nextA, next, ctrA, ctr⟩
  dsimp only [nextKeyInternalSpecX] at *
  have hinv0 : LsCallInv lsmpl s0.mem := h_1
  subst h_2 h_3 h_5
  refine SepWPp.rw_pre (by
    rw [stackAt_nextKeyInternalX_split s0.sp,
      memRegion_36_out_split (s0.readReg64 (.gpr 0#5))]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 386) hinv0 ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (pointsTo32_rev32_eq_toBEBytes (s0.sp - 52#64) (ctr + 1#32))) (by sep_focus) ?_
  refine SepWP.fold (cells8_entails_memRegion_64 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  change subroutine_ok _ _ (withLsCallInv lsmpl (sliceConcat2Spec A)) at h_concat
  wpp_call_lsCallInv_ret h_concat
    (⟨s0.sp - 112#64, s0.sp - 88#64, false, s0.sp - 52#64, toBEBytes 4 (ctr + 1#32),
      true, lsρ "spqr:.rodata..Lanon.161", chainNextInfo⟩ : SliceConcat2Ghost)
    hinv1
  have hinfo_pos : 0 < (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length := by simp
  refine SepWP.fold (vecU8_nonempty_entails A (s0.sp - 112#64) hinfo_pos) (by sep_focus) ?_
  sep_elim_exists
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_ne, hlayout, hptr_ne, hle⟩
  have ⟨hpos1, hpow1, hisize⟩ := hlayout
  apply SepWP.seq_lsCallInv (mid := lsmpl.base 379) hF_sf
  wp_steps
  have hstack_sf : stackAt (s0.sp - 176#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 176#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have ⟨hro2, hcl2⟩ := hinv2
  have hnext_lt : next.length < 2 ^ 63 := by omega
  have hinfo_ge : 32 ≤ (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length := by simp
  have hinfo_lt : (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo).length < 55 := by simp
  wp_call h_hkdf
    (⟨true, lsρ "spqr:.rodata.cst32+0x0", List.replicate 32 0#8,
      false, s0.readReg64 (.gpr 1#5), next,
      false, _, toBEBytes 4 (ctr + 1#32) ++ chainNextInfo,
      s0.sp - 176#64, 64⟩ : HkdfToSliceGhost)
  wp_steps
  refine SepWP.fold (pointsToBytes_memRegion_entails _ hle hlayout) (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  wp_call h_dealloc (_, _, 1)
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm_all, hokm_take, hokm_drop⟩ :=
    exists_unpack64_of_length_64_split ‹List.length (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64) = 64›
  obtain ⟨n0, n1, n2, n3, -, hnext_cells⟩ := exists_unpack64_of_length_32 ‹next.length = 32›
  have hokm_sp := hokm_all (s0.sp - 176#64)
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hokm_sp
  refine SepWP.fold (Entails.of_eq hokm_sp) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hnext_cells (s0.readReg64 (.gpr 1#5)))) (by sep_focus) ?_
  wp_steps
  have hokm_out := (hokm_drop (s0.readReg64 (.gpr 0#5) + 4#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hokm_out
  refine SepWP.fold (Entails.of_eq hokm_out) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hokm_take (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hstack_sf.trans hstack_sf1).symm) (by sep_focus) ?_
  have hbe_len : (toBEBytes 4 (ctr + 1#32)).length = 4 := by simp
  refine SepWP.fold (rejoin_stack_nextKeyInternalX s0.sp w0 w1 w2 w3 w4 w5 w6 w7 _ _ _ _ _ _ _ hbe_len _ _ _ _ _ _) (by sep_focus) ?_
  have hkey_len :
      (List.take 32
        (List.drop 32
          (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64))).length = 32 := by
    rw [List.length_take_of_le (by
      rw [List.length_drop, ‹List.length (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64) = 64›])]
  dsimp only [nextKeyOutAt, nextKeyOut, nextKeyNext, ChainEpochDirection.nextKeyInternal, sepConj_assoc]
  wp_done

end CryptoVerification.SpqrV1.ChainProofs
