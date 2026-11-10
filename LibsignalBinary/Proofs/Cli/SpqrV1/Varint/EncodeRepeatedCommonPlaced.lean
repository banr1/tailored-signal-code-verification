/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommon
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
import ProofLib.SepLogic.WPp

/-!
# Relocatable Step Helpers for `prost::encoding::bytes::encode_repeated [local#3]` (Block `448`)

Provides `[LibsignalPlacement]` loop-body step helpers (`step_copy_placed`, `step_iter_placed`,
`step_latch_zero_placed`, `step_latch_succ_placed`) for Block `448`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.SpqrV1.Varint

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
open CryptoVerification.Cli.SpqrV1.Varint.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  LibsignalProtoCodec.encodeVarint encodeBytesField encodeRepeatedBytes
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace EncodeRepeated1

/-- Copy block (`56..84`) on Block `448`: copies `elemBs` (`elemBs ≠ []`) from `elemPtr`
to `ptr + bs2.length` via `memcpy` and updates `[v + 16]` to `bs2.length + elemBs.length`. -/
theorem step_copy_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (v cap ptr elemPtr sp keyVal remBytes curBase16 : BitVec 64)
    (bs2 elemBs : List (BitVec 8))
    (hle : bs2.length + elemBs.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hne : elemBs ≠ [])
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 56#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = keyVal)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 elemBs.length)
    (hx22 : s.readReg64 .x22 = elemPtr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs2.length)
    (hx24 : s.readReg64 .x24 = remBytes)
    (hx25 : s.readReg64 .x25 = curBase16)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v cap ptr bs2 ∗ (elemPtr ↦ₛ elemBs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_448).base + 84#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = remBytes →
      sm.readReg64 .x25 = curBase16 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_448 H) ret sm
        ((vecU8At A v cap ptr (bs2 ++ elemBs) ∗ (elemPtr ↦ₛ elemBs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_448 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  subst hP
  have hpos : 0 < elemBs.length := List.length_pos_of_ne_nil hne
  rw [vecU8At_expose_slice A v cap ptr bs2 elemBs.length hle hcap hptr hpos]
  apply (SepWPp.of_sepWP_cs_placed (mid := lsρ spqrMemcpySym))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine step_memcpy_call_gen_placed A hmemcpy
    (ptr + BitVec.ofNat 64 bs2.length) elemPtr sp ((blkPl_448).base + 76#64) elemBs
    (F := (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs2) ∗
      memRegion (ptr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 elemBs.length)
        (cap.toNat - bs2.length - elemBs.length) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
    (by ac_rfl) ?_
  intro sm hpcm1 hrunm1 hspm1 htrm1 hcsm1 hcs_s0
  rcases hcsm1 with ⟨hx19m, hx20m, hx21m, _, hx23m, hx24m, hx25m, _⟩
  apply (SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 84#64))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs_s0.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self])))
  rw [← vecU8At_pack_slice A v cap ptr bs2 elemBs hle hcap hptr hne]
  exact Entails.of_eq (by ac_rfl)

/-- Single element iteration (`96..184 → 84`) on Block `448`:
encodes `encodeBytesField tag (some elemBs)` for `(elemPtr, elemBs)` at `curBase`
and stops at loop latch `(blkPl_448).base + 84#64`. -/
theorem step_iter_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks)
    {s0 s : State}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (tag : Nat)
    (v curCap curPtr curBase elemPtr sp remBytes : BitVec 64)
    (curBs elemBs : List (BitVec 8))
    (hfit : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
      curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = remBytes)
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesElemAt curBase elemPtr elemBs ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_448).base + 84#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x24 = remBytes →
      sm.readReg64 .x25 = curBase + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_448 H) ret sm
        ((repeatedBytesElemAt curBase elemPtr elemBs ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeBytesField tag (some elemBs)) ∗
          A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_448 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hcopy_step := step_copy_placed A H hmemcpy
  subst hP
  have hlen_ef := encodeBytesField_some_length tag elemBs
  have hkey_eq := encodeKey_lengthDelimited_eq tag
  have hkey_bounds := SpqrV1.Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (tag * 8 + 2))
  have hlen_bounds := SpqrV1.Varint.encodeVarint_length_bounds (BitVec.ofNat 64 elemBs.length)
  have hfit1 : curBs.length + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62 := by
    rw [← hkey_eq]
    rcases hfit with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hb8 := base_add16_sub8 curBase
  have hb16 := base_add16_sub8_add8 curBase
  rw [repeatedBytesElemAt]
  apply (SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 451))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  refine step_encode_varint_call_gen_placed A henc
    (BitVec.ofNat 64 (tag * 8 + 2)) v curCap curPtr sp ((blkPl_448).base + 112#64) curBs hfit1
    (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
      (elemPtr ↦ₛ elemBs) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
    (by ac_rfl) ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcsm1 hcs1 hge1 hpres1
  rcases hcsm1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, hx25_1, _⟩
  have hfit2 : (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length +
      (encodeVarint (BitVec.ofNat 64 elemBs.length)).length ≤ cap1.toNat ∨
      (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length + 10 < 2 ^ 62 := by
    rw [List.length_append, ← hkey_eq]
    rcases hfit with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  apply (SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 451))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine step_encode_varint_call_gen_placed A henc
    (BitVec.ofNat 64 elemBs.length) v cap1 ptr1 sp ((blkPl_448).base + 124#64)
    (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))) hfit2
    (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
      (elemPtr ↦ₛ elemBs) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
    (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcsm2 hcs2 hge2 hpres2
  rcases hcsm2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, hx24_2, hx25_2, _⟩
  set bs2 := curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2)) ++
    encodeVarint (BitVec.ofNat 64 elemBs.length) with hbs2_def
  have hbs_final : bs2 ++ elemBs = curBs ++ encodeBytesField tag (some elemBs) := by
    simp only [hbs2_def, ← hkey_eq, encodeBytesField_some_eq, List.append_assoc]
  have hbs2_len : bs2.length + elemBs.length =
      curBs.length + (encodeBytesField tag (some elemBs)).length := by
    rw [← List.length_append, hbs_final, List.length_append]
  clear_value bs2
  clear hbs2_def
  rw [vecU8At_eq_header_rest A v cap2 ptr2 bs2]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hbs2_le, hcap2_lt, hptr2_ne⟩ => ?_
  have helem_lt : elemBs.length < 2 ^ 63 := by
    rcases hfit with h | h <;> omega
  by_cases hneed : cap2.toNat < bs2.length + elemBs.length
  · have hfit3 : bs2.length + elemBs.length < 2 ^ 62 := by
      rcases hfit with h | h <;> omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 elemBs.length) = true :=
      (elem_len_ult_spare_iff hbs2_le hcap2_lt helem_lt).mpr hneed
    have hne : elemBs ≠ [] := by
      intro h; subst h; simp at hneed; omega
    obtain ⟨hnot_ult, hnew_ge, hnew_cap, hnew_bound⟩ := elem_len_after_reserve_not_ult hfit3 hneed
    apply (SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 460))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    have hx1_toNat : (BitVec.ofNat 64 bs2.length).toNat = bs2.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_do_reserve2_call_gen_placed hres A hdoReserve
      v cap2 ptr2 sp ((blkPl_448).base + 168#64) bs2 elemBs.length hnew_bound
      (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
        (elemPtr ↦ₛ elemBs) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs2.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by rw [← vecU8At_of_header_rest A v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne]; ac_rfl) ?_
    intro s3 newPtr hpc3 hrun3 hsp3 htr3 hcsm3 hcs3
    rcases hcsm3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, _, hx24_3, hx25_3, _⟩
    rw [vecU8At_eq_header_rest A v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr bs2]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hnew_le, hnew_lt63, hnew_ptr⟩ => ?_
    apply (SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 56#64))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv3
    refine hcopy_step v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr elemPtr sp
      (BitVec.ofNat 64 (tag * 8 + 2)) remBytes (curBase + 16#64) bs2 elemBs
      hnew_ge hnew_lt63 hnew_ptr hne
      (F := A.pool ∗ stackAt (sp - 80#64) (48 + resStack) ∗
        ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by rw [← vecU8At_of_header_rest A v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr bs2 hnew_le hnew_lt63 hnew_ptr]; ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
    refine SepWPp.weaken_pre ?_
      (hnext s4 (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr
        hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
        (by omega) (fun h => absurd h (by omega)))
    rw [hbs_final, repeatedBytesElemAt]
    exact Entails.of_eq (by ac_rfl)
  · have hle2 : bs2.length + elemBs.length ≤ cap2.toNat := by omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 elemBs.length) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hneed ((elem_len_ult_spare_iff hbs2_le hcap2_lt helem_lt).mp h)
    have hpres_all : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat →
        cap2 = curCap ∧ ptr2 = curPtr := by
      intro hfit_cap
      have h1 : curBs.length + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length ≤ curCap.toNat := by
        rw [← hkey_eq]; omega
      obtain ⟨hc1, hp1⟩ := hpres1 h1
      have h2 : (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length +
          (encodeVarint (BitVec.ofNat 64 elemBs.length)).length ≤ cap1.toNat := by
        rw [hc1, List.length_append, ← hkey_eq]; omega
      obtain ⟨hc2, hp2⟩ := hpres2 h2
      exact ⟨hc2.trans hc1, hp2.trans hp1⟩
    apply (SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 144#64))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    by_cases helem : elemBs = []
    · subst helem
      apply (SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 84#64))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv3
      refine SepWPp.weaken_pre ?_
        (hnext _ cap2 ptr2
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (hinv2.trans hinv3))
          (by omega) hpres_all)
      have hbs_nil : bs2 = curBs ++ encodeBytesField tag (some []) := by
        simpa using hbs_final
      rw [← hbs_nil, ← vecU8At_of_header_rest A v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne,
        repeatedBytesElemAt]
      exact Entails.of_eq (by ac_rfl)
    · have hcbnz : (BitVec.ofNat 64 elemBs.length == 0#64) = false :=
        len_beq_zero_false (List.length_pos_of_ne_nil helem) helem_lt
      apply (SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 56#64))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv3
      refine hcopy_step v cap2 ptr2 elemPtr sp
        (BitVec.ofNat 64 (tag * 8 + 2)) remBytes (curBase + 16#64) bs2 elemBs
        hle2 hcap2_lt hptr2_ne helem
        (F := A.pool ∗ stackAt (sp - 80#64) (48 + resStack) ∗
          ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (hinv2.trans hinv3))
        (by rw [← vecU8At_of_header_rest A v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne]; ac_rfl) ?_
      intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
      refine SepWPp.weaken_pre ?_
        (hnext s4 cap2 ptr2 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
          (by omega) hpres_all)
      rw [hbs_final, repeatedBytesElemAt]
      exact Entails.of_eq (by ac_rfl)

/-- Latch block for the final element (`84..92 → 212`) on Block `448`. -/
theorem step_latch_zero_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (sp curBase : BitVec 64)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * 1))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_448).base + 212#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_448 H) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_448 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hbeq := latch_beq_zero_true
  apply (SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 212#64))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))

/-- Latch block when `k > 0` elements remain (`84..92 → 96`, `k + 1 < 2 ^ 58`) on Block `448`. -/
theorem step_latch_succ_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (v keyVal sp curBase : BitVec 64) (k : Nat) (hpos : 0 < k) (hlt : k + 1 < 2 ^ 58)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_448).base + 96#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = BitVec.ofNat 64 (24 * k) →
      sm.readReg64 .x25 = (curBase + 24#64) + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_448 H) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_448 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hbeq : (BitVec.ofNat 64 (24 * (k + 1)) == 24#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change 24 * (k + 1) = 24 at ht
    omega
  have hx24_next := latch_sub24_eq k hlt
  have hx25_next := base_add16_add24 curBase
  apply (SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 96#64))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))

end EncodeRepeated1

end CryptoVerification.Cli.SpqrV1.Varint
