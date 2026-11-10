/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Auth.SpqrAuthCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Verification of `<spqr::chain::Chain>::new`

Proves fixed-image (`chainNew_ok_ext_x`) and relocatable `[LibsignalPlacement]`
(`chainNew_placed_ok`) contracts for `<spqr::chain::Chain>::new` (`0x5fea4`, Block `363`,
116 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.CodeLayout

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x5aaac → 0x5ac78]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace ChainNewFacts

theorem chainNew_fnOff : libsignalSessionCode.fnOff chainNewName = 0x5aaac :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5aaac
theorem vecDequeGrow_fnOff : libsignalSessionCode.fnOff vecDequeGrowName = 0x5a544 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5a544
theorem shim_fnOff :
    libsignalSessionCode.fnOff shimName = num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
theorem alloc_fnOff :
    libsignalSessionCode.fnOff allocName = num% (ls_off% "__rustc::__rust_alloc") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_alloc")
theorem handleError_fnOff :
    libsignalSessionCode.fnOff handleErrorName = num% (ls_off% "alloc::raw_vec::handle_error") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "alloc::raw_vec::handle_error")

theorem rodata_zeros32_new {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x5aae8 0x5aaec)) ↦ᵣ List.replicate 32 0#8) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x5aae8 0x5aaec)) (n := 32) (bs := List.replicate 32 0#8)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_chainStartInfo {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x5aaf0 0x5aaf4)) ↦ᵣ chainStartInfo) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x5aaf0 0x5aaf4)) (n := 33) (bs := chainStartInfo)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_chainStartInfo_placed [LibsignalPlacement]
    {m : Memory} (hF : NextKeyInternalFacts.LsCallInv lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ "spqr:.rodata..Lanon.167") ↦ᵣ chainStartInfo) ∗ P :=
  lsro_intro_chk hF.1 (by decide +kernel) hP

@[simp] theorem chainStartInfo_length : chainStartInfo.length = 33 := by decide

/-- Split `stackAt sp chainNewStackX` (`224 + 16384 = 16608` bytes) into `stackAt (sp - 224#64) extHookStack`
and 28 8-byte stack slots in `[sp - 224#64, sp)`. -/
theorem stackAt_chainNewX_split (sp : BitVec 64) :
    stackAt sp chainNewStackX =
      stackAt (sp - 224#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 224#64) ↦₆₄ v0) ∗ ((sp - 216#64) ↦₆₄ v1) ∗ ((sp - 208#64) ↦₆₄ v2) ∗
        ((sp - 200#64) ↦₆₄ v3) ∗ ((sp - 192#64) ↦₆₄ v4) ∗ ((sp - 184#64) ↦₆₄ v5) ∗
        ((sp - 176#64) ↦₆₄ v6) ∗ ((sp - 168#64) ↦₆₄ v7) ∗ ((sp - 160#64) ↦₆₄ v8) ∗
        ((sp - 152#64) ↦₆₄ v9) ∗ ((sp - 144#64) ↦₆₄ v10) ∗ ((sp - 136#64) ↦₆₄ v11)) ∗
      (∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        ((sp - 128#64) ↦₆₄ v12) ∗ ((sp - 120#64) ↦₆₄ v13) ∗ ((sp - 112#64) ↦₆₄ v14) ∗ ((sp - 104#64) ↦₆₄ v15)) ∗
      (∃∗ v16 : BitVec 64, ∃∗ v17 : BitVec 64, ∃∗ v18 : BitVec 64, ∃∗ v19 : BitVec 64,
       ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64, ∃∗ v22 : BitVec 64, ∃∗ v23 : BitVec 64,
       ∃∗ v24 : BitVec 64, ∃∗ v25 : BitVec 64, ∃∗ v26 : BitVec 64, ∃∗ v27 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v16) ∗ ((sp - 88#64) ↦₆₄ v17) ∗ ((sp - 80#64) ↦₆₄ v18) ∗
        ((sp - 72#64) ↦₆₄ v19) ∗ ((sp - 64#64) ↦₆₄ v20) ∗ ((sp - 56#64) ↦₆₄ v21) ∗
        ((sp - 48#64) ↦₆₄ v22) ∗ ((sp - 40#64) ↦₆₄ v23) ∗ ((sp - 32#64) ↦₆₄ v24) ∗
        ((sp - 24#64) ↦₆₄ v25) ∗ ((sp - 16#64) ↦₆₄ v26) ∗ ((sp - 8#64) ↦₆₄ v27)) := by
  change memRegion (sp - BitVec.ofNat 64 16608) 16608 =
    memRegion (sp - 224#64 - BitVec.ofNat 64 16384) 16384 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16608) (n := 16384) (k := 224)
      (b' := sp - 224#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 224#64) (n := 96) (k := 128)
      (b' := sp - 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 128#64) (n := 32) (k := 96)
      (b' := sp - 96#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16608) 16384 ∗
    (memRegion (sp - 224#64) (8 * 12) ∗
      (memRegion (sp - 128#64) (8 * 4) ∗ memRegion (sp - 96#64) (8 * 12))) = _
  rw [ProofLib.memRegion_cells (sp - 224#64) 12 (by decide),
    ProofLib.memRegion_cells (sp - 128#64) 4 (by decide),
    ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : sp - 224#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16608 := by bv_kernel
  have hc12a : cells (sp - 224#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 224#64) ↦₆₄ v0) ∗ ((sp - 216#64) ↦₆₄ v1) ∗ ((sp - 208#64) ↦₆₄ v2) ∗
        ((sp - 200#64) ↦₆₄ v3) ∗ ((sp - 192#64) ↦₆₄ v4) ∗ ((sp - 184#64) ↦₆₄ v5) ∗
        ((sp - 176#64) ↦₆₄ v6) ∗ ((sp - 168#64) ↦₆₄ v7) ∗ ((sp - 160#64) ↦₆₄ v8) ∗
        ((sp - 152#64) ↦₆₄ v9) ∗ ((sp - 144#64) ↦₆₄ v10) ∗ ((sp - 136#64) ↦₆₄ v11)) := by cells_unfold
  have hc4 : cells (sp - 128#64) 4 =
      (∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        ((sp - 128#64) ↦₆₄ v12) ∗ ((sp - 120#64) ↦₆₄ v13) ∗ ((sp - 112#64) ↦₆₄ v14) ∗ ((sp - 104#64) ↦₆₄ v15)) := by
    cells_unfold
  have hc12b : cells (sp - 96#64) 12 =
      (∃∗ v16 : BitVec 64, ∃∗ v17 : BitVec 64, ∃∗ v18 : BitVec 64, ∃∗ v19 : BitVec 64,
       ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64, ∃∗ v22 : BitVec 64, ∃∗ v23 : BitVec 64,
       ∃∗ v24 : BitVec 64, ∃∗ v25 : BitVec 64, ∃∗ v26 : BitVec 64, ∃∗ v27 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v16) ∗ ((sp - 88#64) ↦₆₄ v17) ∗ ((sp - 80#64) ↦₆₄ v18) ∗
        ((sp - 72#64) ↦₆₄ v19) ∗ ((sp - 64#64) ↦₆₄ v20) ∗ ((sp - 56#64) ↦₆₄ v21) ∗
        ((sp - 48#64) ↦₆₄ v22) ∗ ((sp - 40#64) ↦₆₄ v23) ∗ ((sp - 32#64) ↦₆₄ v24) ∗
        ((sp - 24#64) ↦₆₄ v25) ∗ ((sp - 16#64) ↦₆₄ v26) ∗ ((sp - 8#64) ↦₆₄ v27)) := by cells_unfold
  rw [hsub, hc12a, hc4, hc12b]

/-- Rejoin the 28 8-byte stack slots in `[sp - 224#64, sp)` into `stackAt sp chainNewStackX`. -/
theorem rejoin_stack_chainNewX (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
     v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : BitVec 64) :
    stackAt (sp - 224#64) extHookStack ∗
      ((sp - 224#64) ↦₆₄ v0) ∗ ((sp - 216#64) ↦₆₄ v1) ∗ ((sp - 208#64) ↦₆₄ v2) ∗
      ((sp - 200#64) ↦₆₄ v3) ∗ ((sp - 192#64) ↦₆₄ v4) ∗ ((sp - 184#64) ↦₆₄ v5) ∗
      ((sp - 176#64) ↦₆₄ v6) ∗ ((sp - 168#64) ↦₆₄ v7) ∗ ((sp - 160#64) ↦₆₄ v8) ∗
      ((sp - 152#64) ↦₆₄ v9) ∗ ((sp - 144#64) ↦₆₄ v10) ∗ ((sp - 136#64) ↦₆₄ v11) ∗
      ((sp - 128#64) ↦₆₄ v12) ∗ ((sp - 120#64) ↦₆₄ v13) ∗ ((sp - 112#64) ↦₆₄ v14) ∗
      ((sp - 104#64) ↦₆₄ v15) ∗ ((sp - 96#64) ↦₆₄ v16) ∗ ((sp - 88#64) ↦₆₄ v17) ∗
      ((sp - 80#64) ↦₆₄ v18) ∗ ((sp - 72#64) ↦₆₄ v19) ∗ ((sp - 64#64) ↦₆₄ v20) ∗
      ((sp - 56#64) ↦₆₄ v21) ∗ ((sp - 48#64) ↦₆₄ v22) ∗ ((sp - 40#64) ↦₆₄ v23) ∗
      ((sp - 32#64) ↦₆₄ v24) ∗ ((sp - 24#64) ↦₆₄ v25) ∗ ((sp - 16#64) ↦₆₄ v26) ∗
      ((sp - 8#64) ↦₆₄ v27) ⊢ stackAt sp chainNewStackX := by
  rw [stackAt_chainNewX_split sp]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (sepConj_mono
      (Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
        (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
          (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
            (Entails.sepExists_right v9 (Entails.sepExists_right v10
              (Entails.sepExists_right v11 (Entails.refl _)))))))))))))
      (sepConj_mono
        (Entails.sepExists_right v12 (Entails.sepExists_right v13
          (Entails.sepExists_right v14 (Entails.sepExists_right v15 (Entails.refl _)))))
        (Entails.sepExists_right v16 (Entails.sepExists_right v17 (Entails.sepExists_right v18
          (Entails.sepExists_right v19 (Entails.sepExists_right v20 (Entails.sepExists_right v21
            (Entails.sepExists_right v22 (Entails.sepExists_right v23 (Entails.sepExists_right v24
              (Entails.sepExists_right v25 (Entails.sepExists_right v26
                (Entails.sepExists_right v27 (Entails.refl _))))))))))))))))

/-- Fold 12 8-byte cells at `[sp - 224#64, sp - 128#64)` into `memRegion (sp - 224#64) 96`. -/
theorem cells12_entails_memRegion_96 (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    ((sp - 224#64) ↦₆₄ w0) ∗ ((sp - 216#64) ↦₆₄ w1) ∗ ((sp - 208#64) ↦₆₄ w2) ∗
    ((sp - 200#64) ↦₆₄ w3) ∗ ((sp - 192#64) ↦₆₄ w4) ∗ ((sp - 184#64) ↦₆₄ w5) ∗
    ((sp - 176#64) ↦₆₄ w6) ∗ ((sp - 168#64) ↦₆₄ w7) ∗ ((sp - 160#64) ↦₆₄ w8) ∗
    ((sp - 152#64) ↦₆₄ w9) ∗ ((sp - 144#64) ↦₆₄ w10) ∗ ((sp - 136#64) ↦₆₄ w11) ⊢
      memRegion (sp - 224#64) 96 := by
  rw [show (96 : Nat) = 8 * 12 by rfl, ProofLib.memRegion_cells (sp - 224#64) 12 (by decide)]
  cells_unfold
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right w6 (Entails.sepExists_right w7 (Entails.sepExists_right w8
        (Entails.sepExists_right w9 (Entails.sepExists_right w10
          (Entails.sepExists_right w11 (Entails.refl _))))))))))))

/-- Split `memRegion out 88` into 9 8-byte cells (`+0..+64`), 3 4-byte cells (`+72, +76, +80`),
and `memRegion (out + 84#64) 4`. -/
theorem memRegion_88_out_split (out : BitVec 64) :
    memRegion out 88 =
      (∃∗ d2 : BitVec 32, ∃∗ d1 : BitVec 32, ∃∗ d0 : BitVec 32,
       ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
       ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u8 : BitVec 64,
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗ ((out + 16#64) ↦₆₄ u2) ∗ ((out + 24#64) ↦₆₄ u3) ∗
        ((out + 32#64) ↦₆₄ u4) ∗ ((out + 40#64) ↦₆₄ u5) ∗ ((out + 48#64) ↦₆₄ u6) ∗
        ((out + 56#64) ↦₆₄ u7) ∗ ((out + 64#64) ↦₆₄ u8) ∗
        ((out + 72#64) ↦₃₂ d0) ∗ ((out + 76#64) ↦₃₂ d1) ∗ ((out + 80#64) ↦₃₂ d2) ∗
        memRegion (out + 84#64) 4) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 72) (k := 16)
      (b' := out + 72#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 72#64) (n := 4) (k := 12)
      (b' := out + 76#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 76#64) (n := 4) (k := 8)
      (b' := out + 80#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 80#64) (n := 4) (k := 4)
      (b' := out + 84#64) rfl (by bv_omega) (by decide),
    show (72 : Nat) = 8 * 9 by rfl,
    ProofLib.memRegion_cells out 9 (by decide),
    NextKeyInternalFacts.memRegion_4_eq_pointsTo32 (out + 72#64),
    NextKeyInternalFacts.memRegion_4_eq_pointsTo32 (out + 76#64),
    NextKeyInternalFacts.memRegion_4_eq_pointsTo32 (out + 80#64)]
  simp only [cells, BitVec.ofNat_eq_ofNat, Nat.reduceMul, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

/-- Split a 56-byte `ChainEpochDirection` slot into 6 8-byte cells, 1 4-byte cell, and 4 bytes of padding. -/
theorem memRegion_56_ced_split (p : BitVec 64) :
    memRegion p 56 =
      (∃∗ d0 : BitVec 32,
       ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗
        ((p + 24#64) ↦₆₄ u3) ∗ ((p + 32#64) ↦₆₄ u4) ∗ ((p + 40#64) ↦₆₄ u5) ∗
        ((p + 48#64) ↦₃₂ d0) ∗ memRegion (p + 52#64) 4) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 48) (k := 8)
      (b' := p + 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := p + 48#64) (n := 4) (k := 4)
      (b' := p + 52#64) rfl (by bv_omega) (by decide),
    show (48 : Nat) = 8 * 6 by rfl,
    ProofLib.memRegion_cells p 6 (by decide),
    NextKeyInternalFacts.memRegion_4_eq_pointsTo32 (p + 48#64)]
  simp only [cells, BitVec.ofNat_eq_ofNat, Nat.reduceMul, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

/-- Split a 96-byte `genr8r` slice into 12 8-byte words `w0..w11` and three 32-byte slices
(`bs.take 32`, `(bs.drop 32).take 32`, `(bs.drop 64).take 32`). -/
theorem exists_unpack64_of_length_96_split {bs : List (BitVec 8)} (h : bs.length = 96) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64,
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
          ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs.take 32) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ (bs.drop 32).take 32) =
          (a ↦₆₄ w4) ∗ ((a + 8#64) ↦₆₄ w5) ∗ ((a + 16#64) ↦₆₄ w6) ∗ ((a + 24#64) ↦₆₄ w7)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ (bs.drop 64).take 32) =
          (a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w9) ∗ ((a + 16#64) ↦₆₄ w10) ∗ ((a + 24#64) ↦₆₄ w11)) := by
  have h1 : (bs.take 32).length = 32 := by simp [h]
  have h2 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h3 : ((bs.drop 64).take 32).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w4, w5, w6, w7, _, hp2⟩ := exists_unpack64_of_length_32 h2
  obtain ⟨w8, w9, w10, w11, _, hp3⟩ := exists_unpack64_of_length_32 h3
  have hbs_eq : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++ (bs.drop 64).take 32) := by
    have hdrop64 : (bs.drop 64).take 32 = (bs.drop 32).drop 32 := by
      rw [List.drop_drop, List.take_of_length_le (by simp [h])]
    rw [hdrop64, List.take_append_drop, List.take_append_drop]
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, fun a => ?_, hp1, hp2, hp3⟩
  conv_lhs => rw [hbs_eq]
  rw [pointsToBytes_append, h1, pointsToBytes_append, h2, hp1, hp2, hp3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- Stack address selected by `csel` for `cedForDirection genr8r dir`. -/
def cedSrc (sp : BitVec 64) (dir : Direction) : BitVec 64 :=
  match dir with
  | .a2b => sp - 192#64
  | .b2a => sp - 160#64

def cedWord (wA wB : BitVec 64) : Direction → BitVec 64
  | .a2b => wA
  | .b2a => wB

theorem cedCells_reframe (sp : BitVec 64) (w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) (dir : Direction) :
    ((sp - 192#64) ↦₆₄ w4) ∗ ((sp - 184#64) ↦₆₄ w5) ∗ ((sp - 176#64) ↦₆₄ w6) ∗ ((sp - 168#64) ↦₆₄ w7) ∗
    ((sp - 160#64) ↦₆₄ w8) ∗ ((sp - 152#64) ↦₆₄ w9) ∗ ((sp - 144#64) ↦₆₄ w10) ∗ ((sp - 136#64) ↦₆₄ w11) =
    (cedSrc sp dir ↦₆₄ cedWord w4 w8 dir) ∗ ((cedSrc sp dir + 8#64) ↦₆₄ cedWord w5 w9 dir) ∗
    ((cedSrc sp dir + 16#64) ↦₆₄ cedWord w6 w10 dir) ∗ ((cedSrc sp dir + 24#64) ↦₆₄ cedWord w7 w11 dir) ∗
    (cedSrc sp dir.switch ↦₆₄ cedWord w4 w8 dir.switch) ∗ ((cedSrc sp dir.switch + 8#64) ↦₆₄ cedWord w5 w9 dir.switch) ∗
    ((cedSrc sp dir.switch + 16#64) ↦₆₄ cedWord w6 w10 dir.switch) ∗ ((cedSrc sp dir.switch + 24#64) ↦₆₄ cedWord w7 w11 dir.switch) := by
  cases dir <;> simp (config := { decide := true }) only [cedSrc, cedWord, Direction.switch, bv_sub_add_lit, Nat.reduceSub]
  ac_rfl

theorem cedCells_eq_pointsToBytes {bs : List (BitVec 8)}
    {w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    (hp2 : ∀ a : BitVec 64,
      (a ↦ₛ (bs.drop 32).take 32) =
        (a ↦₆₄ w4) ∗ ((a + 8#64) ↦₆₄ w5) ∗ ((a + 16#64) ↦₆₄ w6) ∗ ((a + 24#64) ↦₆₄ w7))
    (hp3 : ∀ a : BitVec 64,
      (a ↦ₛ (bs.drop 64).take 32) =
        (a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w9) ∗ ((a + 16#64) ↦₆₄ w10) ∗ ((a + 24#64) ↦₆₄ w11))
    (d : Direction) (a : BitVec 64) :
    (a ↦₆₄ cedWord w4 w8 d) ∗ ((a + 8#64) ↦₆₄ cedWord w5 w9 d) ∗
    ((a + 16#64) ↦₆₄ cedWord w6 w10 d) ∗ ((a + 24#64) ↦₆₄ cedWord w7 w11 d) =
    (a ↦ₛ (Chain.cedForDirection bs d).next) := by
  cases d with
  | a2b => exact (hp2 a).symm
  | b2a => exact (hp3 a).symm

@[simp] theorem cedForDirection_next_length {bs : List (BitVec 8)} (h : bs.length = 96)
    (d : Direction) :
    (Chain.cedForDirection bs d).next.length = 32 := by
  cases d <;> simp [Chain.cedForDirection, ChainEpochDirection.new, h]

@[simp] theorem cedForDirection_prev_data (bs : List (BitVec 8)) (d : Direction) :
    (Chain.cedForDirection bs d).prev.data = [] := by
  cases d <;> rfl

@[simp] theorem cedForDirection_ctr (bs : List (BitVec 8)) (d : Direction) :
    (Chain.cedForDirection bs d).ctr = 0#32 := by
  cases d <;> rfl

/-- Fold the 4 stack cells at `sp - 128#64 .. sp - 104#64` holding `(0, 8, 0, 0)` into
`vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A) (sp - 128#64) 0#64 8#64 0#64 []`. -/
theorem vecDequeAt_empty_sp_intro (A : RustAlloc) (sp : BitVec 64) :
    ((sp - 128#64) ↦₆₄ 0#64) ∗ ((sp - 120#64) ↦₆₄ 8#64) ∗
    ((sp - 112#64) ↦₆₄ 0#64) ∗ ((sp - 104#64) ↦₆₄ 0#64) ⊢
      vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
        (sp - 128#64) 0#64 8#64 0#64 [] := by
  unfold vecDequeAt vecDequeHeader vecDequeRingBuf
  simp (config := { decide := true }) only [List.length_nil, ↓reduceIte, pure_true, sepConj_emp,
    bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  exact Entails.refl _

/-- Unpack the postcondition of `vecDequeGrowSpec` on an initially empty `VecDeque<ChainEpoch>`
at `sp - 128#64` into stack header cells, `A.live ptr' 448 8`, the decomposed 112-byte slot 0
at `ptr'`, and the 3 spare 112-byte slots at `ptr' + 112#64 .. ptr' + 336#64`. -/
theorem vecDequeGrow_post_unpack (A : RustAlloc) (sp ptr' : BitVec 64) :
    vecDequeAt A 112 chainEpochAlign (chainEpochAt A)
      (sp - 128#64) (newCapChainEpoch 0#64) ptr' 0#64 [] ⊢
    ∃∗ d1 : BitVec 32, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ d0 : BitVec 32,
    ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
    ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
      ⌜ptr' ≠ 0#64⌝ ∗ ((sp - 128#64) ↦₆₄ 4#64) ∗ ((sp - 120#64) ↦₆₄ ptr') ∗
      ((sp - 112#64) ↦₆₄ 0#64) ∗ ((sp - 104#64) ↦₆₄ 0#64) ∗ A.live ptr' 448 8 ∗
      (ptr' ↦₆₄ u0) ∗ ((ptr' + 8#64) ↦₆₄ u1) ∗ ((ptr' + 16#64) ↦₆₄ u2) ∗
      ((ptr' + 24#64) ↦₆₄ u3) ∗ ((ptr' + 32#64) ↦₆₄ u4) ∗ ((ptr' + 40#64) ↦₆₄ u5) ∗
      ((ptr' + 48#64) ↦₃₂ d0) ∗ memRegion (ptr' + 52#64) 4 ∗
      ((ptr' + 56#64) ↦₆₄ w0) ∗ ((ptr' + 64#64) ↦₆₄ w1) ∗ ((ptr' + 72#64) ↦₆₄ w2) ∗
      ((ptr' + 80#64) ↦₆₄ w3) ∗ ((ptr' + 88#64) ↦₆₄ w4) ∗ ((ptr' + 96#64) ↦₆₄ w5) ∗
      ((ptr' + 104#64) ↦₃₂ d1) ∗ memRegion (ptr' + 108#64) 4 ∗
      memRegion (ptr' + 112#64) 112 ∗ memRegion (ptr' + 224#64) 112 ∗
      memRegion (ptr' + 336#64) 112 := by
  have hcap : newCapChainEpoch 0#64 = 4#64 := rfl
  rw [hcap]
  unfold vecDequeAt vecDequeHeader vecDequeRingBuf chainEpochAlign
  simp (config := { decide := true }) only [vecDequeSlotsAt, vecDequeLogIdx, List.length_nil,
    BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul,
    Nat.reduceAdd, ↓reduceIte, ↓reduceDIte, BitVec.add_zero, true_and, and_true, sepConj_emp,
    bv_sub_add_lit, Nat.reduceSub]
  rw [ProofLib.memRegion_split' (b := ptr') (n := 56) (k := 56)
      (b' := ptr' + 56#64) rfl (by bv_omega) (by decide),
    memRegion_56_ced_split ptr', memRegion_56_ced_split (ptr' + 56#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine Entails.sepExists_elim fun d1 => Entails.sepExists_elim fun w0 =>
    Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun d0 =>
    Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 =>
    Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
    Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 => ?_
  refine Entails.sepExists_right d1 (Entails.sepExists_right w0
    (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right d0
        (Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
          (Entails.sepExists_right u3 (Entails.sepExists_right u4
            (Entails.sepExists_right u5 (Entails.of_eq (by ac_rfl)))))))))))))))

/-- Fold a full 32-byte `Vec<u8>` header and buffer into `vecU8At A v 32#64 ptr bs`. -/
theorem vecU8At_32_intro (A : RustAlloc) (v ptr : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 32) (hptr : ptr ≠ 0#64) :
    (v ↦₆₄ 32#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 32#64) ∗
    A.live ptr 32 1 ∗ (ptr ↦ₛ bs) ⊢ vecU8At A v 32#64 ptr bs := by
  unfold vecU8At vecHeader; rw [hlen]
  simp (config := { decide := true }) only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, Nat.sub_self, ↓reduceIte, ProofLib.memRegion_zero,
    true_and, sepConj_emp]
  exact Entails.trans (Entails.pure_right hptr (Entails.refl _)) (Entails.of_eq (by ac_rfl))

/-- Fold an empty 72-byte-capacity `Vec<u8>` header and buffer into `vecU8At A v 72#64 ptr []`. -/
theorem vecU8At_72_empty_intro (A : RustAlloc) (v ptr : BitVec 64) (hptr : ptr ≠ 0#64) :
    (v ↦₆₄ 72#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
    A.live ptr 72 1 ∗ memRegion ptr 72 ⊢ vecU8At A v 72#64 ptr [] := by
  unfold vecU8At vecHeader
  simp (config := { decide := true }) only [List.length_nil, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero, BitVec.add_zero,
    ↓reduceIte, pointsToBytes_nil, emp_sepConj, true_and]
  exact Entails.trans (Entails.pure_right hptr (Entails.refl _)) (Entails.of_eq (by ac_rfl))

/-- Fold a 56-byte `ChainEpochDirection` slot at `p` and its two heap allocations into
`chainEpochDirectionAt`. -/
theorem chainEpochDirectionAt_new_intro (A : RustAlloc) (p p_next p_prev : BitVec 64)
    {genr8r : List (BitVec 8)} (hgen : genr8r.length = 96) (d : Direction)
    (hnext : p_next ≠ 0#64) (hprev : p_prev ≠ 0#64) :
    (p ↦₆₄ 32#64) ∗ ((p + 8#64) ↦₆₄ p_next) ∗ ((p + 16#64) ↦₆₄ 32#64) ∗
    ((p + 24#64) ↦₆₄ 72#64) ∗ ((p + 32#64) ↦₆₄ p_prev) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
    ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4 ∗
    A.live p_next 32 1 ∗ (p_next ↦ₛ (Chain.cedForDirection genr8r d).next) ∗
    A.live p_prev 72 1 ∗ memRegion p_prev 72 ⊢
      chainEpochDirectionAt A p
        { next := { cap := 32#64, ptr := p_next }, prev := { cap := 72#64, ptr := p_prev } }
        (Chain.cedForDirection genr8r d) := by
  unfold chainEpochDirectionAt keyHistoryAt
  rw [cedForDirection_prev_data, cedForDirection_ctr]
  have h1 := vecU8At_32_intro A p p_next (cedForDirection_next_length hgen d) hnext
  have h2 := vecU8At_72_empty_intro A (p + 24#64) p_prev hprev
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

/-- Fold the `out` struct fields, `links` buffer, and `next_root` buffer into `chainAt`. -/
theorem chainAt_new_intro (A : RustAlloc) (hkdf : HkdfFn)
    (out ptr' p_send_next p_send_prev p_recv_next p_recv_prev p_root : BitVec 64)
    (initialKey : List (BitVec 8)) (dir : Direction) (params : ChainParamsPB)
    (hgen : (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96).length = 96)
    (hptr : ptr' ≠ 0#64) (hroot : p_root ≠ 0#64) :
    (out ↦₆₄ 4#64) ∗ ((out + 8#64) ↦₆₄ ptr') ∗ ((out + 16#64) ↦₆₄ 0#64) ∗
    ((out + 24#64) ↦₆₄ 1#64) ∗ ((out + 32#64) ↦₆₄ 32#64) ∗ ((out + 40#64) ↦₆₄ p_root) ∗
    ((out + 48#64) ↦₆₄ 32#64) ∗ ((out + 56#64) ↦₆₄ 0#64) ∗ ((out + 64#64) ↦₆₄ 0#64) ∗
    ((out + 72#64) ↦₃₂ params.maxJump) ∗ ((out + 76#64) ↦₃₂ params.maxOooKeys) ∗
    ((out + 80#64) ↦₃₂ dir.toI32) ∗ memRegion (out + 84#64) 4 ∗ A.live ptr' 448 8 ∗
    chainEpochDirectionAt A ptr'
      { next := { cap := 32#64, ptr := p_send_next }, prev := { cap := 72#64, ptr := p_send_prev } }
      (Chain.cedForDirection (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir) ∗
    chainEpochDirectionAt A (ptr' + 56#64)
      { next := { cap := 32#64, ptr := p_recv_next }, prev := { cap := 72#64, ptr := p_recv_prev } }
      (Chain.cedForDirection (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir.switch) ∗
    memRegion (ptr' + 112#64) 112 ∗ memRegion (ptr' + 224#64) 112 ∗
    memRegion (ptr' + 336#64) 112 ∗ A.live p_root 32 1 ∗
    (p_root ↦ₛ (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96).take 32) ⊢
      ∃∗ G : ChainGhost,
        ⌜G.linksCap = 4#64 ∧ G.linksHead = 0#64⌝ ∗
        chainAt A out G (chainNewVal hkdf initialKey dir params) := by
  let gce0 : ChainEpochGhost :=
    { send := { next := { cap := 32#64, ptr := p_send_next }, prev := { cap := 72#64, ptr := p_send_prev } }
      recv := { next := { cap := 32#64, ptr := p_recv_next }, prev := { cap := 72#64, ptr := p_recv_prev } } }
  refine Entails.sepExists_right
    { linksCap := 4#64, linksPtr := ptr', linksHead := 0#64, epochs := [gce0]
      nextRoot := { cap := 32#64, ptr := p_root } } (Entails.pure_right ⟨rfl, rfl⟩ ?_)
  unfold chainAt chainNewVal vecDequeAt vecDequeHeader vecDequeRingBuf
    chainEpochAt chainParamsAt directionAt chainEpochSize chainEpochAlign
  simp (config := { decide := true }) only [vecDequeSlotsAt, vecDequeLogIdx,
    List.zip_cons_cons, List.zip_nil_right, List.length_singleton,
    BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.reduceMul, Nat.reduceAdd, Nat.sub_self, ↓reduceIte, ↓reduceDIte, List.getElem_cons_zero,
    BitVec.add_zero, pure_true, emp_sepConj, sepConj_emp, true_and, and_true,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hlen_root : ((hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96).take 32).length = 32 :=
    List.length_take_of_le (by omega)
  have hroot_vec := vecU8At_32_intro A (out + 32#64) p_root hlen_root hroot
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hroot_vec
  let R := (out ↦₆₄ 4#64) ∗ ((out + 8#64) ↦₆₄ ptr') ∗ ((out + 16#64) ↦₆₄ 0#64) ∗
    ((out + 24#64) ↦₆₄ 1#64) ∗ A.live ptr' 448 8 ∗
    chainEpochDirectionAt A ptr' gce0.send (Chain.cedForDirection (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir) ∗
    chainEpochDirectionAt A (ptr' + 56#64) gce0.recv (Chain.cedForDirection (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir.switch) ∗
    memRegion (ptr' + 112#64) 112 ∗ memRegion (ptr' + 224#64) 112 ∗ memRegion (ptr' + 336#64) 112 ∗
    ((out + 56#64) ↦₆₄ 0#64) ∗ ((out + 64#64) ↦₆₄ 0#64) ∗ ((out + 72#64) ↦₃₂ params.maxJump) ∗
    ((out + 76#64) ↦₃₂ params.maxOooKeys) ∗ ((out + 80#64) ↦₃₂ dir.toI32) ∗ memRegion (out + 84#64) 4
  exact Entails.trans (Entails.of_eq (by dsimp only [R]; ac_rfl))
    (Entails.trans (Entails.pure_right hptr (sepConj_mono_left (Q := R) hroot_vec)) (Entails.of_eq (by dsimp only [R]; ac_rfl)))

@[simp, arm64_norm, wp_norm]
theorem tst_dir_toI32 (dir : Direction) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 dir.toI32 &&& 4294967297#64) == 0#32) =
      (dir.toI32 &&& 1#32 == 0#32) := by
  cases dir <;> rfl

@[simp, arm64_norm, wp_norm]
theorem csel_cedSrc_dir_not (sp : BitVec 64) (dir : Direction) :
    (if ¬(dir.toI32 &&& 1#32 == 0#32) = true then sp - 160#64 else sp - 192#64) =
      cedSrc sp dir := by
  cases dir <;> rfl

@[simp, arm64_norm, wp_norm]
theorem csel_cedSrc_switch_not (sp : BitVec 64) (dir : Direction) :
    (if ¬(dir.toI32 &&& 1#32 == 0#32) = true then sp - 192#64 else sp - 160#64) =
      cedSrc sp dir.switch := by
  cases dir <;> rfl

theorem SepWPp.pure_left_focus {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post panic_post : State → SepProp → Prop} (φ : Prop)
    (hf : P = ⌜φ⌝ ∗ P')
    (h : φ → SepWPp prog pc s P' post panic_post) :
    SepWPp prog pc s P post panic_post := by
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact (h hm.1) R hm.2 hL

theorem SepWPp.call_allowPanic_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    {x : α} {s0 s : State} {P F R : SepProp}
    {post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  exact ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hF.1 hF.2 hpc hrun hsp_align hlr
    (fun R' hm => by
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF.1, hF.2⟩, hpre R' hm⟩)
    (fun sf code R' _ hpost => by
      dsimp only [Spec.inImage] at hpost
      rw [hexit_eq] at hpost
      exact not_satisfies_false_sepConj hpost)
    (fun sf _ _ hm' => by
      dsimp only [Spec.inImage] at hm'
      rw [← sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left (hpan sf)) hm')
    (fun sf hpcm hrunm hspm hcsm hfz hsym => hnext sf hpcm hrunm hspm hcsm ⟨hfz, hsym⟩)
    (fun sf R' _ hpost => by
      dsimp only [Spec.inImage] at hpost
      rw [hoom_eq] at hpost
      exact (not_satisfies_false_sepConj hpost).elim)

open Lean Elab Tactic in
private meta def wppCallChainNewCore (lemId : Ident) (hcall a hF : Term) : TacticM Unit := do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply ($lemId $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wppCallChainNewCore: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  let idPanic := mkIdent ``NextKeyInternalFacts.onPanic_entails_of_trace_eq
  let idGrow := mkIdent ``vecDequeGrowSpec
  evalTactic (← `(tactic| (
    wp_unfold_specs
    (try dsimp only [$idGrow:ident])
    (try dsimp only)
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
    wp_focus_close (wp_unfold_specs; (try dsimp only [$idGrow:ident]); intro _; exact $idPanic:ident (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; (try dsimp only [$idGrow:ident]); first | (intro _ _; rfl) | exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
    (try dsimp only [$idGrow:ident])
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
elab "wpp_call_inImage " hcall:term:max a:term:max hF:term:max : tactic =>
  wppCallChainNewCore (mkIdent ``SepWPp.call_allowPanic_inImage) hcall a hF

open Lean Elab Tactic in
elab "wpp_call_lsCallInv " hcall:term:max a:term:max hF:term:max : tactic =>
  wppCallChainNewCore (mkIdent ``NextKeyInternalFacts.SepWPp.call_allowPanic_lsCallInv_mid) hcall a hF

theorem memRegion_32_cells4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3)) := by
  rw [show (32 : Nat) = 8 * 4 by rfl, ProofLib.memRegion_cells a 4 (by decide)]
  simp only [cells, BitVec.ofNat_eq_ofNat, Nat.reduceMul, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem sub_ok_at_rebase_bv {α : Type} {b : BitVec 64} {H : String → Option (State → State)}
    {name callee : String} {k : BitVec 64} {spec : Spec α}
    (hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff name) + k =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff callee))
    (h : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr callee) spec) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + k) spec := by
  rwa [show (libsignalSessionCode.rebase b H).fnAddr name + k =
    (libsignalSessionCode.rebase b H).fnAddr callee by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, BitVec.add_assoc, hk]]

theorem hokm_sp_reframe (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    (hall : ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        (a + 32#64) ↦₆₄ w4 ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
        ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11))
    (dir : Direction) :
    ((sp - 224#64) ↦ₛ bs) =
      ((sp - 224#64) ↦₆₄ w0) ∗ ((sp - 216#64) ↦₆₄ w1) ∗
      ((sp - 208#64) ↦₆₄ w2) ∗ ((sp - 200#64) ↦₆₄ w3) ∗
      (cedSrc sp dir ↦₆₄ cedWord w4 w8 dir) ∗ ((cedSrc sp dir + 8#64) ↦₆₄ cedWord w5 w9 dir) ∗
      ((cedSrc sp dir + 16#64) ↦₆₄ cedWord w6 w10 dir) ∗ ((cedSrc sp dir + 24#64) ↦₆₄ cedWord w7 w11 dir) ∗
      (cedSrc sp dir.switch ↦₆₄ cedWord w4 w8 dir.switch) ∗
      ((cedSrc sp dir.switch + 8#64) ↦₆₄ cedWord w5 w9 dir.switch) ∗
      ((cedSrc sp dir.switch + 16#64) ↦₆₄ cedWord w6 w10 dir.switch) ∗
      ((cedSrc sp dir.switch + 24#64) ↦₆₄ cedWord w7 w11 dir.switch) := by
  have h1 := hall (sp - 224#64)
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc] at h1
  rw [h1, cedCells_reframe sp w4 w5 w6 w7 w8 w9 w10 w11 dir]

end ChainNewFacts

open ChainNewFacts NextKeyInternalFacts AgreeStateSimp

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false chainStartInfo_length chainEpochSize tst_dir_toI32 csel_cedSrc_dir_not csel_cedSrc_switch_not
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  chainNew_fnOff hkdfToSlice_fnOff vecDequeGrow_fnOff shim_fnOff alloc_fnOff handleError_fnOff
  libsignalSessionCode_fnOff_0x5aaac
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x5a544
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_hook% "alloc::raw_vec::handle_error")

private theorem sub_ok_conseq_entails {α : Type} {prog : Program} {pc : BitVec 64}
    {S₁ S₂ : Spec α} (h : subroutine_ok prog pc S₁)
    (hpre : ∀ x s0, S₂.pre x s0 ⊢ S₁.pre x s0)
    (hpost : ∀ x s0 sf, S₁.post x s0 sf ⊢ S₂.post x s0 sf)
    (hpan : ∀ x s0 sf, S₁.onPanic x s0 sf = S₂.onPanic x s0 sf)
    (hexit : ∀ x c s0 sf, S₁.onExit x c s0 sf = S₂.onExit x c s0 sf)
    (hoom : ∀ x s0 sf, S₁.onOom x s0 sf = S₂.onOom x s0 sf) :
    subroutine_ok prog pc S₂ := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hm hsp _ => ?_
  refine h.mono_outcome x R s0 hpc hrun (Satisfies.mono (sepConj_mono_left (hpre x s0)) hm) hsp fun sf hout => ?_
  rcases hout with ⟨h1, h2, hp⟩ | ⟨h1, hp⟩ | ⟨c, h1, hp⟩ | ⟨h1, hp⟩
  · exact Or.inl ⟨h1, h2, Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hp⟩
  · rw [hpan] at hp; exact Or.inr (Or.inl ⟨h1, hp⟩)
  · rw [hexit] at hp; exact Or.inr (Or.inr (Or.inl ⟨c, h1, hp⟩))
  · rw [hoom] at hp; exact Or.inr (Or.inr (Or.inr ⟨h1, hp⟩))

private def hkdfToSliceSpecCore (hkdf : HkdfFn)
    (P_ikm : Bool → List (BitVec 8) → Prop) (extra : Nat) : Spec HkdfToSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
      s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
      s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
      s.readReg64 .x6 = x.okmA ∧ s.readReg64 .x7 = BitVec.ofNat 64 x.okmLen ∧
      x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
      32 ≤ x.info.length ∧ x.info.length < 55 ∧
      (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96) ∧
      (¬x.saltRO ∨ x.salt.length ≤ 64) ∧ P_ikm x.ikmRO x.ikm⌝ ∗
      bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗
      memRegion (s.sp - BitVec.ofNat 64 (extra + extHookStack)) extra ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜(hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧ sf.trace = s0.trace⌝ ∗
      bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗ (x.okmA ↦ₛ hkdf x.salt x.ikm x.info x.okmLen) ∗
      memRegion (s0.sp - BitVec.ofNat 64 (extra + extHookStack)) extra ∗ stackAt s0.sp extHookStack

private def chainNewSpecCore (hkdf : HkdfFn) (A : RustAlloc)
    (P_ikm : Bool → List (BitVec 8) → Prop) (extra : Nat) : Spec ChainNewGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.ikmA ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.initialKey.length ∧
      (s.readReg64 .x3).setWidth 32 = x.dir.toI32 ∧
      (s.readReg64 .x4).setWidth 32 = x.params.maxJump ∧
      (s.readReg64 .x5).setWidth 32 = x.params.maxOooKeys ∧
      x.initialKey.length < 2 ^ 63 ∧ P_ikm x.ikmRO x.initialKey⌝ ∗
      memRegion x.out 88 ∗ bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool ∗ memRegion (s.sp - BitVec.ofNat 64 (extra + chainNewStackX)) extra ∗
      stackAt s.sp chainNewStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G : ChainGhost,
        ⌜G.linksCap = 4#64 ∧ G.linksHead = 0#64⌝ ∗
        chainAt A x.out G (chainNewVal hkdf x.initialKey x.dir x.params)) ∗
      bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool ∗ memRegion (s0.sp - BitVec.ofNat 64 (extra + chainNewStackX)) extra ∗
      stackAt s0.sp chainNewStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
private theorem chainNew_ok_core {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {P_ikm : Bool → List (BitVec 8) → Prop} {extra : Nat}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 224#64 - BitVec.ofNat 64 (extra + extHookStack) =
      sp - BitVec.ofNat 64 (extra + chainNewStackX))
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
      ((hkdfToSliceSpecCore hkdf P_ikm extra).inImage img))
    (hgrow : VecDequeGrowOkX img A ext)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainNewName)
      ((chainNewSpecCore hkdf A P_ikm extra).inImage img) := by
  unfold tripleRatchetProgAtExt
  refine subroutine_ok_inImage_rodata2_keep (rodata_zeros32_new himg) (rodata_chainStartInfo himg) ?_
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff chainNewName = 0x5aaac :=
    chainNew_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5aaac 464
  have h_hkdf := sub_ok_at_rebase (name := chainNewName) (callee := hkdfToSliceName)
    (k := num% (0x5de8c - 0x5aaac)) (by rw [chainNew_fnOff, hkdfToSlice_fnOff]) hhkdf
  have h_grow := sub_ok_at_rebase_bv (name := chainNewName) (callee := vecDequeGrowName)
    (k := 0x5a544#64 - 0x5aaac#64)
    (by rw [chainNew_fnOff, vecDequeGrow_fnOff]; rfl) hgrow
  have h_shim := sub_ok_at_rebase (name := chainNewName) (callee := shimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5aaac))
    (by rw [chainNew_fnOff, shim_fnOff]) hshim
  have h_alloc := sub_ok_at_rebase (name := chainNewName) (callee := allocName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - 0x5aaac))
    (by rw [chainNew_fnOff, alloc_fnOff]) halloc
  have h_panic := panic_at_handle_error_ext img.base ext chainNewName
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x5aaac))
    (by rw [chainNew_fnOff, handleError_fnOff])
  dsimp only [tripleRatchetProgAtExt] at h_panic
  have hadrp1 : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainNewName + 60#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x5aae8 0x5aaec - 0x5a000) =
      img.base + bv% (ls_xref% 0x5aae8 0x5aaec) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  have hadrp2 : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainNewName + 68#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x5aaf0 0x5aaf4 - 0x5a000) =
      img.base + bv% (ls_xref% 0x5aaf0 0x5aaf4) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainNewName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear himg hhkdf hgrow hshim halloc hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainNewName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨out, ikmRO, ikmA, initialKey, dir, params⟩
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_3 h_4
  have hsalt_ro : ¬true ∨ (List.replicate 32 0#8).length ≤ 64 := Or.inr (by decide)
  have hextra_in :
      memRegion (s0.sp - BitVec.ofNat 64 (extra + chainNewStackX)) extra =
      memRegion (s0.sp - 224#64 - BitVec.ofNat 64 (extra + extHookStack)) extra := by
    rw [hsub_extra s0.sp]
  refine SepWPp.rw_pre (by
    rw [stackAt_chainNewX_split s0.sp,
      memRegion_88_out_split (s0.readReg64 (.gpr 0#5))]) ?_
  sep_elim_exists
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  refine SepWPp.of_sepWP_inImage (mid := entry + 136#64) hinv0 ?_
  apply SepWP.seq_inImage (mid := entry + bv% (0x5de8c - 0x5aaac)) hinv0
  wp_steps
  refine SepWP.fold (Entails.of_eq hextra_in) (by sep_focus) ?_
  refine SepWP.fold (cells12_entails_memRegion_96 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5aaac)) hinv1
  wp_call h_hkdf
    (⟨true, img.base + bv% (ls_xref% 0x5aae8 0x5aaec), List.replicate 32 0#8,
      ikmRO, s0.readReg64 (.gpr 1#5), initialKey,
      true, img.base + bv% (ls_xref% 0x5aaf0 0x5aaf4), chainStartInfo,
      s0.sp - 224#64, 96⟩ : HkdfToSliceGhost)
  wp_steps
  have hstack_sf : stackAt (s0.sp - 224#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 224#64›]
  refine SepWP.fold (Entails.of_eq hextra_in.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have ⟨hF2, hsym2⟩ := hinv2
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5aaac)) hinv2
  wp_call h_shim ()
  wp_steps
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rintro ⟨hF3, hsym3⟩
  wp_call h_alloc (72, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  by_cases hoom1 : sf_2.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro htrace
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5aaac))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
          ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
  · have hoom1_64 : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmod1, htrace1⟩
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
      hokm_all, hokm_root, hokm_a2b, hokm_b2a⟩ :=
      exists_unpack64_of_length_96_split
        ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96›
    refine SepWPp.of_sepWP_inImage (mid := entry + 160#64) hinv3 ?_
    refine SepWP.fold (Entails.of_eq (hokm_sp_reframe s0.sp hokm_all dir)) (by sep_focus) ?_
    apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5aaac)) hinv3
    wp_steps
    have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
      rw [‹sf_2.sp = sf_1.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv4
    have ⟨hF4, hsym4⟩ := hinv4
    apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5aaac)) hinv4
    wp_call h_shim ()
    wp_steps
    have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by
      rw [‹sf_3.sp = sf_2.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    rintro ⟨hF5, hsym5⟩
    wp_call h_alloc (32, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv5
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      intro htrace
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5aaac))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
            ‹sf_3.trace = sf_2.trace›, htrace1, ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hmod2, htrace2⟩
      refine SepWPp.of_sepWP_inImage (mid := entry + 212#64) hinv5 ?_
      refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_4.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
      sep_elim_exists
      apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5aaac)) hinv5
      wp_steps
      have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by
        rw [‹sf_4.sp = sf_3.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv6
      have ⟨hF6, hsym6⟩ := hinv6
      apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5aaac)) hinv6
      wp_call h_shim ()
      wp_steps
      have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by
        rw [‹sf_5.sp = sf_4.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      rintro ⟨hF7, hsym7⟩
      wp_call h_alloc (72, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv7
      by_cases hoom3 : sf_6.readReg64 (Reg.gpr 0#5) = 0
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) = 0#64 := hoom3
        simp only [hoom3, ite_true, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        intro htrace
        apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5aaac))
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
              ‹sf_5.trace = sf_4.trace›, htrace2, ‹sf_3.trace = sf_2.trace›,
              htrace1, ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom3
        simp only [hoom3, ite_false, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        rintro ⟨hmod3, htrace3⟩
        refine SepWPp.of_sepWP_inImage (mid := entry + 236#64) hinv7 ?_
        apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5aaac)) hinv7
        wp_steps
        have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by
          rw [‹sf_6.sp = sf_5.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv8
        have ⟨hF8, hsym8⟩ := hinv8
        apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5aaac)) hinv8
        wp_call h_shim ()
        wp_steps
        have hstack_sf7 : stackAt sf_6.sp extHookStack = stackAt sf_7.sp extHookStack := by
          rw [‹sf_7.sp = sf_6.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        rintro ⟨hF9, hsym9⟩
        wp_call h_alloc (32, 1)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv9
        by_cases hoom4 : sf_8.readReg64 (Reg.gpr 0#5) = 0
        · have hoom4_64 : sf_8.readReg64 (Reg.gpr 0#5) = 0#64 := hoom4
          simp only [hoom4, ite_true, sepConj_assoc]
          refine SepWPp.pure_left_focus _ (by sep_focus) ?_
          intro htrace
          apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5aaac))
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
          simpa only [sepConj_assoc] using
            allowPanic_panicked
              (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
                ‹sf_7.trace = sf_6.trace›, htrace3, ‹sf_5.trace = sf_4.trace›,
                htrace2, ‹sf_3.trace = sf_2.trace›, htrace1,
                ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
        · have hoom4_64 : sf_8.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom4
          simp only [hoom4, ite_false, sepConj_assoc]
          refine SepWPp.pure_left_focus _ (by sep_focus) ?_
          rintro ⟨hmod4, htrace4⟩
          refine SepWPp.of_sepWP_inImage (mid := entry + (0x5a544#64 - 0x5aaac#64)) hinv9 ?_
          refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_8.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
          sep_elim_exists
          wp_steps
          refine SepWP.fold (vecDequeAt_empty_sp_intro A s0.sp) (by sep_focus) ?_
          have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by
            rw [‹sf_8.sp = sf_7.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv10
          change subroutine_ok prog (entry + (0x5a544#64 - 0x5aaac#64))
            ((vecDequeGrowSpec A).inImage img) at h_grow
          wpp_call_inImage h_grow
            (⟨s0.sp - 128#64, 0#64, 8#64, 0#64, []⟩ : VecDequeGrowGhost)
            hinv10
          have hhead'_0 : w_1 = 0#64 := ‹True → w_1 = 0#64› trivial
          subst hhead'_0
          have htrace_grow : sf_9.trace = sf_8.trace := ‹sf_9.trace = sf_8.trace›
          refine SepWPp.of_sepWP_inImage (mid := entry + 364#64) hF_sf ?_
          refine SepWP.fold (vecDequeGrow_post_unpack A s0.sp w) (by sep_focus) ?_
          sep_elim_exists
          refine SepWP.pure_left_focus _ (by sep_focus) ?_
          intro hptr'_ne
          apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5aaac)) hF_sf
          wp_steps
          have hstack_sf9 : stackAt sf_8.sp extHookStack = stackAt sf_9.sp extHookStack := by
            rw [‹sf_9.sp = sf_8.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv11
          have ⟨hF11, hsym11⟩ := hinv11
          apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5aaac)) hinv11
          wp_call h_shim ()
          wp_steps
          have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by
            rw [‹sf_10.sp = sf_9.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          rintro ⟨hF12, hsym12⟩
          wp_call h_alloc (32, 1)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv12
          by_cases hoom5 : sf_11.readReg64 (Reg.gpr 0#5) = 0
          · have hoom5_64 : sf_11.readReg64 (Reg.gpr 0#5) = 0#64 := hoom5
            simp only [hoom5, ite_true, sepConj_assoc]
            refine SepWPp.pure_left_focus _ (by sep_focus) ?_
            intro htrace
            apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5aaac))
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
            simpa only [sepConj_assoc] using
              allowPanic_panicked
                (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
                  ‹sf_10.trace = sf_9.trace›, htrace_grow,
                  htrace4, ‹sf_7.trace = sf_6.trace›, htrace3,
                  ‹sf_5.trace = sf_4.trace›, htrace2, ‹sf_3.trace = sf_2.trace›,
                  htrace1, ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
          · have hoom5_64 : sf_11.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom5
            simp only [hoom5, ite_false, sepConj_assoc]
            refine SepWPp.pure_left_focus _ (by sep_focus) ?_
            rintro ⟨hmod5, htrace5⟩
            apply SepWPp.of_sepWP_ret
            refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_11.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
            sep_elim_exists
            wp_steps
            refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a dir (sf_4.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a dir.switch (sf_8.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (hokm_root (sf_11.readReg64 (.gpr 0#5))).symm) (by sep_focus) ?_
            refine SepWP.fold (chainEpochDirectionAt_new_intro A w
              (sf_4.readReg64 (.gpr 0#5)) (sf_2.readReg64 (.gpr 0#5))
              ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96›
              dir hoom2_64 hoom1_64) (by sep_focus) ?_
            have hrecv_intro := chainEpochDirectionAt_new_intro A (w + 56#64)
              (sf_8.readReg64 (.gpr 0#5)) (sf_6.readReg64 (.gpr 0#5))
              ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96›
              dir.switch hoom4_64 hoom3_64
            simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrecv_intro
            refine SepWP.fold hrecv_intro (by sep_focus) ?_
            refine SepWP.fold (chainAt_new_intro A hkdf (s0.readReg64 (.gpr 0#5)) w
              (sf_4.readReg64 (.gpr 0#5)) (sf_2.readReg64 (.gpr 0#5))
              (sf_8.readReg64 (.gpr 0#5)) (sf_6.readReg64 (.gpr 0#5))
              (sf_11.readReg64 (.gpr 0#5)) initialKey dir params
              ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96›
              hptr'_ne hoom5_64) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (cedCells_reframe s0.sp w4 w5 w6 w7 w8 w9 w10 w11 dir).symm) (by sep_focus) ?_
            have hstack_all : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 224#64) extHookStack := by
              rw [← hstack_sf10, ← hstack_sf9, ← hstack_sf8, ← hstack_sf7, ← hstack_sf6,
                ← hstack_sf5, ← hstack_sf4, ← hstack_sf3, ← hstack_sf2, ← hstack_sf1, ← hstack_sf]
            refine SepWP.fold (Entails.of_eq hstack_all) (by sep_focus) ?_
            refine SepWP.fold (rejoin_stack_chainNewX s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            wp_done

theorem chainNew_ok_of_contracts_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext) (hgrow : VecDequeGrowOkX img A ext)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img)) :
    ChainNewOkX img hkdf A ext := by
  unfold HkdfToSliceSpqrOkX at hhkdf
  have hhkdf' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
      ((hkdfToSliceSpecCore hkdf (fun _ _ => True) 0).inImage img) := by
    refine sub_ok_conseq_entails hhkdf (fun x s => ?_) (fun x s0 sf => ?_)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    · dsimp only [Spec.inImage, hkdfToSliceSpecCore, hkdfToSliceSpqrSpec, hkdfToSliceSpec]
      rw [ProofLib.memRegion_zero, emp_sepConj]
      refine sepConj_mono_right (Entails.pure_left fun hp => ?_)
      rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _, _⟩
      exact Entails.pure_right ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ (Entails.refl _)
    · dsimp only [Spec.inImage, hkdfToSliceSpecCore, hkdfToSliceSpqrSpec, hkdfToSliceSpec]
      rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
  unfold ChainNewOkX
  refine sub_ok_conseq_entails
    (chainNew_ok_core (fun sp => by dsimp only [extHookStack, chainNewStackX]; bv_kernel)
      himg hhkdf' hgrow hshim halloc)
    (fun x s => ?_) (fun x s0 sf => ?_) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · dsimp only [Spec.inImage, chainNewSpecCore, chainNewSpecX]
    simp only [and_true, ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
  · dsimp only [Spec.inImage, chainNewSpecCore, chainNewSpecX]
    rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _

theorem chainNew_ok_ext_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext) (hgrow : VecDequeGrowOkX img A ext)
    (hA : AllocContractsX img A ext) : ChainNewOkX img hkdf A ext :=
  chainNew_ok_of_contracts_x himg hhkdf hgrow (hA.shim extHookStack (by decide) (by decide)) hA.alloc

private theorem stackAt_hkdfExt_split' (sp : BitVec 64) : stackAt sp hkdfToSliceStackExt =
    memRegion (sp - BitVec.ofNat 64 (1232 + extHookStack)) 1232 ∗ stackAt sp extHookStack :=
  ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 17616) (n := 1232) (k := 16384)
    (b' := sp - 16384#64) rfl (by bv_omega) (by decide)

private theorem stackAt_chainNewExt_split' (sp : BitVec 64) : stackAt sp chainNewStackExt =
    memRegion (sp - BitVec.ofNat 64 (1232 + chainNewStackX)) 1232 ∗ stackAt sp chainNewStackX :=
  ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 17840) (n := 1232) (k := 16608)
    (b' := sp - 16608#64) rfl (by bv_omega) (by decide)

theorem chainNew_ok_of_contracts_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext) (hgrow : VecDequeGrowOkX img A ext)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img)) :
    ChainNewOkExt img hkdf A ext := by
  unfold HkdfToSliceSpqrOkExt at hhkdf
  have hhkdf' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
      ((hkdfToSliceSpecCore hkdf (fun ro bs => ¬ro ∨ bs.length < 64) 1232).inImage img) := by
    refine sub_ok_conseq_entails hhkdf (fun x s => ?_) (fun x s0 sf => ?_)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    · dsimp only [Spec.inImage, hkdfToSliceSpecCore, hkdfToSliceSpecExt]
      rw [stackAt_hkdfExt_split' s.sp]; exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.inImage, hkdfToSliceSpecCore, hkdfToSliceSpecExt]
      rw [stackAt_hkdfExt_split' s0.sp]; exact Entails.of_eq (by ac_rfl)
  unfold ChainNewOkExt
  refine sub_ok_conseq_entails
    (chainNew_ok_core (fun sp => by dsimp only [extHookStack, chainNewStackX]; bv_kernel)
      himg hhkdf' hgrow hshim halloc)
    (fun x s => ?_) (fun x s0 sf => ?_) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · dsimp only [Spec.inImage, chainNewSpecCore, chainNewSpecExt]
    rw [stackAt_chainNewExt_split' s.sp]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [Spec.inImage, chainNewSpecCore, chainNewSpecExt]
    rw [stackAt_chainNewExt_split' s0.sp]; exact Entails.of_eq (by ac_rfl)

theorem chainNew_ok_ext_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext) (hgrow : VecDequeGrowOkX img A ext)
    (hA : AllocContractsX img A ext) : ChainNewOkExt img hkdf A ext :=
  chainNew_ok_of_contracts_ext himg hhkdf hgrow (hA.shim extHookStack (by decide) (by decide)) hA.alloc

abbrev chainNew_ok_ext := @chainNew_ok_ext_ext

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
/-- Relocatable `<spqr::chain::Chain>::new` (Block `363`) meets
`withLsCallInv lsmpl (chainNewSpecX hkdf A)` under `[LibsignalPlacement]`. -/
theorem chainNew_placed_ok [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_hkdf : subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (hkdfToSliceSpqrSpec hkdf)))
    (h_grow : subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 353) (withLsCallInv lsmpl (vecDequeGrowSpec A)))
    (h_shim : subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (h_alloc : subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (h_panic : ((blkPC_363).rebase (blkPl_363).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_363).rebase (blkPl_363).base H) (blkPl_363).base
      (withLsCallInv lsmpl (chainNewSpecX hkdf A)) := by
  refine subroutine_ok_withLsCallInv_rodata2_keep rodata_zeros32_placed rodata_chainStartInfo_placed ?_
  wpp_init x s0
  rcases x with ⟨out, ikmRO, ikmA, initialKey, dir, params⟩
  dsimp only [chainNewSpecX] at *
  have hinv0 : LsCallInv lsmpl s0.mem := h_1
  subst h_2 h_3
  refine SepWPp.rw_pre (by rw [stackAt_chainNewX_split s0.sp, memRegion_88_out_split (s0.readReg64 (.gpr 0#5))]) ?_
  sep_elim_exists
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_363).base + 136#64) hinv0 ?_
  apply SepWP.seq_lsCallInv (mid := lsmpl.base 379) hinv0
  wp_steps
  refine SepWP.fold (cells12_entails_memRegion_96 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  wp_call h_hkdf
    (⟨true, lsρ "spqr:.rodata.cst32+0x0", List.replicate 32 0#8, ikmRO, s0.readReg64 (.gpr 1#5), initialKey,
      true, lsρ "spqr:.rodata..Lanon.167", chainStartInfo, s0.sp - 224#64, 96⟩ : HkdfToSliceGhost)
  wp_steps
  have hstack_sf : stackAt (s0.sp - 224#64) extHookStack = stackAt sf.sp extHookStack := by rw [‹sf.sp = s0.sp - 224#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  wp_call h_shim ()
  wp_steps
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  wp_call h_alloc (72, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  by_cases hoom1 : sf_2.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    conv => arg 4; simp only [hoom1, ite_true, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
    simpa only [sepConj_assoc] using allowPanic_panicked
      (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
  · have hoom1_64 : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    conv => arg 4; simp only [hoom1, ite_false, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hmod1, htrace1⟩
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm_all, hokm_root, hokm_a2b, hokm_b2a⟩ :=
      exists_unpack64_of_length_96_split ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96›
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_363).base + 160#64) hinv3 ?_
    refine SepWP.fold (Entails.of_eq (hokm_sp_reframe s0.sp hokm_all dir)) (by sep_focus) ?_
    wp_steps
    have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by rw [‹sf_2.sp = sf_1.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
    wp_call h_shim ()
    wp_steps
    have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by rw [‹sf_3.sp = sf_2.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
    wp_call h_alloc (32, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv5
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      conv => arg 4; simp only [hoom2, ite_true, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
      simpa only [sepConj_assoc] using allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf_3.trace = sf_2.trace›, htrace1, ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      conv => arg 4; simp only [hoom2, ite_false, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hmod2, htrace2⟩
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_363).base + 212#64) hinv5 ?_
      refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_4.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
      sep_elim_exists
      wp_steps
      have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by rw [‹sf_4.sp = sf_3.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
      wp_call h_shim ()
      wp_steps
      have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by rw [‹sf_5.sp = sf_4.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
      wp_call h_alloc (72, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv7
      by_cases hoom3 : sf_6.readReg64 (Reg.gpr 0#5) = 0
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) = 0#64 := hoom3
        conv => arg 4; simp only [hoom3, ite_true, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) fun htrace => ?_
        apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
        simpa only [sepConj_assoc] using allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf_5.trace = sf_4.trace›, htrace2, ‹sf_3.trace = sf_2.trace›, htrace1, ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom3
        conv => arg 4; simp only [hoom3, ite_false, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hmod3, htrace3⟩
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_363).base + 236#64) hinv7 ?_
        wp_steps
        have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by rw [‹sf_6.sp = sf_5.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
        wp_call h_shim ()
        wp_steps
        have hstack_sf7 : stackAt sf_6.sp extHookStack = stackAt sf_7.sp extHookStack := by rw [‹sf_7.sp = sf_6.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
        wp_call h_alloc (32, 1)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv9
        by_cases hoom4 : sf_8.readReg64 (Reg.gpr 0#5) = 0
        · have hoom4_64 : sf_8.readReg64 (Reg.gpr 0#5) = 0#64 := hoom4
          conv => arg 4; simp only [hoom4, ite_true, sepConj_assoc]
          refine SepWPp.pure_left_focus _ (by sep_focus) fun htrace => ?_
          apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
          simpa only [sepConj_assoc] using allowPanic_panicked
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf_7.trace = sf_6.trace›, htrace3, ‹sf_5.trace = sf_4.trace›, htrace2, ‹sf_3.trace = sf_2.trace›, htrace1, ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
        · have hoom4_64 : sf_8.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom4
          conv => arg 4; simp only [hoom4, ite_false, sepConj_assoc]
          refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hmod4, htrace4⟩
          refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 353) hinv9 ?_
          refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_8.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
          sep_elim_exists
          wp_steps
          refine SepWP.fold (vecDequeAt_empty_sp_intro A s0.sp) (by sep_focus) ?_
          have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by rw [‹sf_8.sp = sf_7.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv10
          change subroutine_ok _ _ (withLsCallInv lsmpl (vecDequeGrowSpec A)) at h_grow
          wpp_call_lsCallInv h_grow (⟨s0.sp - 128#64, 0#64, 8#64, 0#64, []⟩ : VecDequeGrowGhost) hinv10
          have hhead'_0 : w_1 = 0#64 := ‹True → w_1 = 0#64› trivial
          subst hhead'_0
          have htrace_grow : sf_9.trace = sf_8.trace := ‹sf_9.trace = sf_8.trace›
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_363).base + 364#64) hF_sf ?_
          refine SepWP.fold (vecDequeGrow_post_unpack A s0.sp w) (by sep_focus) ?_
          sep_elim_exists
          refine SepWP.pure_left_focus _ (by sep_focus) fun hptr'_ne => ?_
          wp_steps
          have hstack_sf9 : stackAt sf_8.sp extHookStack = stackAt sf_9.sp extHookStack := by rw [‹sf_9.sp = sf_8.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
          wp_call h_shim ()
          wp_steps
          have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by rw [‹sf_10.sp = sf_9.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
          wp_call h_alloc (32, 1)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv12
          by_cases hoom5 : sf_11.readReg64 (Reg.gpr 0#5) = 0
          · have hoom5_64 : sf_11.readReg64 (Reg.gpr 0#5) = 0#64 := hoom5
            conv => arg 4; simp only [hoom5, ite_true, sepConj_assoc]
            refine SepWPp.pure_left_focus _ (by sep_focus) fun htrace => ?_
            apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic) fun hm => ?_
            simpa only [sepConj_assoc] using allowPanic_panicked
              (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf_10.trace = sf_9.trace›, htrace_grow, htrace4, ‹sf_7.trace = sf_6.trace›, htrace3, ‹sf_5.trace = sf_4.trace›, htrace2, ‹sf_3.trace = sf_2.trace›, htrace1, ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
          · have hoom5_64 : sf_11.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom5
            conv => arg 4; simp only [hoom5, ite_false, sepConj_assoc]
            refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hmod5, htrace5⟩
            apply SepWPp.of_sepWP_ret
            refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_11.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
            sep_elim_exists
            wp_steps
            refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a dir (sf_4.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a dir.switch (sf_8.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (hokm_root (sf_11.readReg64 (.gpr 0#5))).symm) (by sep_focus) ?_
            refine SepWP.fold (chainEpochDirectionAt_new_intro A w (sf_4.readReg64 (.gpr 0#5)) (sf_2.readReg64 (.gpr 0#5)) ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96› dir hoom2_64 hoom1_64) (by sep_focus) ?_
            have hrecv_intro := chainEpochDirectionAt_new_intro A (w + 56#64) (sf_8.readReg64 (.gpr 0#5)) (sf_6.readReg64 (.gpr 0#5)) ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96› dir.switch hoom4_64 hoom3_64
            simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrecv_intro
            refine SepWP.fold hrecv_intro (by sep_focus) ?_
            refine SepWP.fold (chainAt_new_intro A hkdf (s0.readReg64 (.gpr 0#5)) w (sf_4.readReg64 (.gpr 0#5)) (sf_2.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5)) (sf_6.readReg64 (.gpr 0#5)) (sf_11.readReg64 (.gpr 0#5)) initialKey dir params ‹List.length (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) = 96› hptr'_ne hoom5_64) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (cedCells_reframe s0.sp w4 w5 w6 w7 w8 w9 w10 w11 dir).symm) (by sep_focus) ?_
            have hstack_all : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 224#64) extHookStack := by
              rw [← hstack_sf10, ← hstack_sf9, ← hstack_sf8, ← hstack_sf7, ← hstack_sf6, ← hstack_sf5, ← hstack_sf4, ← hstack_sf3, ← hstack_sf2, ← hstack_sf1, ← hstack_sf]
            refine SepWP.fold (Entails.of_eq hstack_all) (by sep_focus) ?_
            refine SepWP.fold (rejoin_stack_chainNewX s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            wp_done

end CryptoVerification.SpqrV1.ChainProofs
