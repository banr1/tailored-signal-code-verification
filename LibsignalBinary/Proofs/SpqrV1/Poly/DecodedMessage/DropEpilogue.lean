/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Loop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof -- shake: keep

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Drop Glue and Epilogue

**Checked by Lean.**

Proves the `polys: [Option<Poly>; 16]` drop glue (`0x6c0fc..0x6c2f0`), `points_vecs` deallocation,
and register-restoration epilogue (`0x6bca0..0x6bcdc` and `0x6c2f0..0x6c2f8`) of `decoded_message`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Getters CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareName lagrangePrepare_fnOff LagrangePrepareArgs lagrangePrepareSpec lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack lagrangePrepare_ok polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Memory Region and `optPolyCacheSlotAt` Helpers -/

theorem pointsTo64_entails_memRegion8 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_eight a]
  exact Entails.sepExists_intro w

theorem optPolyCacheSlot_none_entails_memRegion24 (slot : BitVec 64) :
    (slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16 ⊢ memRegion slot 24 := by
  rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split slot 8 16 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion8 slot noneCap)

theorem pointsTo64_three_entails_memRegion24 (slot w0 w1 w2 : BitVec 64) :
    (slot ↦₆₄ w0) ∗ ((slot + 8#64) ↦₆₄ w1) ∗ ((slot + 16#64) ↦₆₄ w2) ⊢ memRegion slot 24 := by
  have h16 : slot + 8#64 + 8#64 = slot + 16#64 := by bv_omega
  rw [show (24 : Nat) = 8 + (8 + 8) from rfl,
    memRegion_split slot 8 (8 + 8) (by decide),
    memRegion_split (slot + 8#64) 8 8 (by decide), h16]
  exact sepConj_mono (pointsTo64_entails_memRegion8 slot w0)
    (sepConj_mono (pointsTo64_entails_memRegion8 (slot + 8#64) w1)
      (pointsTo64_entails_memRegion8 (slot + 16#64) w2))

@[local wp_norm, local arm64_norm]
theorem noneCap_slt_one : noneCap.slt 1#64 = true := rfl

attribute [local irreducible] noneCap

theorem bv64_slt_one_of_ge1_le65536 {n : Nat} (hge : 1 ≤ n) (hle : n ≤ 65536) :
    (BitVec.ofNat 64 n).slt 1#64 = false := by
  rw [Bool.eq_false_iff, ne_eq,
    slt_one_iff_eq_zero (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)]
  exact ofNat_ne_zero_of_pos (by omega) (by omega)

theorem pull_none_slot (M Pool Stk : SepProp) (slot : BitVec 64) (P : SepProp) :
    M ∗ Pool ∗ Stk ∗ ((slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16) ∗ P =
      (slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16 ∗ M ∗ Pool ∗ Stk ∗ P := by
  ac_rfl

theorem pull_some_slot (A : RustAlloc) (M Pool Stk : SepProp) (slot : BitVec 64) (p : Poly) (P : SepProp) :
    M ∗ Pool ∗ Stk ∗ optPolyCacheSlotAt A slot (some p) ∗ P =
      ∃∗ ptr : BitVec 64,
        ⌜1 ≤ p.coefficients.length ∧ p.coefficients.length ≤ 65536 ∧ ptr ≠ 0#64⌝ ∗
          (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
          ((slot + 8#64) ↦₆₄ ptr) ∗
          ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
          A.live ptr (2 * p.coefficients.length) 2 ∗
          gf16SliceAt ptr p.coefficients ∗
          M ∗ Pool ∗ Stk ∗ P := by
  unfold optPolyCacheSlotAt
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  congr 1
  funext ptr
  ac_rfl

theorem merge_prev_slot_none (sp0 slot : BitVec 64) (prev next : Nat)
    (hsum : prev + 24 = next) (hbound : next ≤ 384)
    (haddr : sp0 - 600#64 + BitVec.ofNat 64 prev = slot) (Rest : SepProp) :
    (slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16 ∗
      memRegion (sp0 - 600#64) prev ∗ Rest ⊢
      memRegion (sp0 - 600#64) next ∗ Rest := by
  have heq :
      (slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16 ∗
        memRegion (sp0 - 600#64) prev ∗ Rest =
      (memRegion (sp0 - 600#64) prev ∗
        ((slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16)) ∗ Rest := by ac_rfl
  rw [heq]
  refine sepConj_mono_left ?_
  rw [← hsum, memRegion_split (sp0 - 600#64) prev 24 (by omega), haddr]
  exact sepConj_mono_right (optPolyCacheSlot_none_entails_memRegion24 slot)

theorem merge_prev_slot_some (sp0 slot : BitVec 64) (prev next : Nat)
    (hsum : prev + 24 = next) (hbound : next ≤ 384)
    (haddr : sp0 - 600#64 + BitVec.ofNat 64 prev = slot)
    (w0 w1 w2 : BitVec 64) (Rest : SepProp) :
    ((slot ↦₆₄ w0) ∗ ((slot + 8#64) ↦₆₄ w1) ∗ ((slot + 16#64) ↦₆₄ w2)) ∗
      (memRegion (sp0 - 600#64) prev ∗ Rest) ⊢
      memRegion (sp0 - 600#64) next ∗ Rest := by
  have heq :
      ((slot ↦₆₄ w0) ∗ ((slot + 8#64) ↦₆₄ w1) ∗ ((slot + 16#64) ↦₆₄ w2)) ∗
        (memRegion (sp0 - 600#64) prev ∗ Rest) =
      (memRegion (sp0 - 600#64) prev ∗
        ((slot ↦₆₄ w0) ∗ ((slot + 8#64) ↦₆₄ w1) ∗ ((slot + 16#64) ↦₆₄ w2))) ∗ Rest := by ac_rfl
  rw [heq]
  refine sepConj_mono_left ?_
  rw [← hsum, memRegion_split (sp0 - 600#64) prev 24 (by omega), haddr]
  exact sepConj_mono_right (pointsTo64_three_entails_memRegion24 slot w0 w1 w2)

theorem dropPolySlot_some_to_dealloc (A : RustAlloc) (slot ptr : BitVec 64) (p : Poly) (Rest : SepProp) :
    (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      ((slot + 8#64) ↦₆₄ ptr) ∗
      ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      A.live ptr (2 * p.coefficients.length) 2 ∗
      gf16SliceAt ptr p.coefficients ∗ Rest ⊢
      (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
        ((slot + 8#64) ↦₆₄ ptr) ∗
        ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
        A.live ptr (2 * p.coefficients.length) 2 ∗
        memRegion ptr (2 * p.coefficients.length) ∗ Rest := by
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  exact sepConj_mono_left (gf16SliceAt_to_memRegion ptr p.coefficients)

theorem bv64_lsl1_toNat_of_le65536 {n : Nat} (hle : n ≤ 65536) :
    ((BitVec.ofNat 64 n) <<< 1).toNat = 2 * n := by
  rw [bv64_lsl1_norm n, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem bv64_ofNat_ne0_of_ge1 {n : Nat} (hge : 1 ≤ n) (hle : n ≤ 65536) :
    ((BitVec.ofNat 64 n) <<< 1 == 0#64) = false := by
  rw [bv64_lsl1_norm n, beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change 2 * n = 0 at h1
  omega

/-- Single-field `dealloc` contract shared by `AllocContracts` and `AllocContracts4K`. -/
abbrev DeallocContract (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A)

set_option hygiene false in
local macro "def_drop_poly_slot " thmName:ident startOff:num startBv:term:max endBv:term:max slotBv:term:max prevBytes:num nextBytes:num : command =>
  `(command|
    theorem $thmName {b : BitVec 64} {A : RustAlloc}
        {ext : String → Option (State → State)} {ret_pc : BitVec 64}
        (hdealloc0 : DeallocContract b A ext)
        (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
        (opt : Option Poly)
        (s : State) (P : SepProp) (post : State → SepProp → Prop)
        (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + $startBv)
        (hstat : s.status = .Running)
        (hsp : s.sp = sp0 - 672#64)
        (hcont : ∀ sf : State,
          sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + $endBv →
          sf.status = .Running →
          sf.sp = sp0 - 672#64 →
          traceVRegs sf = traceVRegs s →
          SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
            (memRegion (sp0 - 600#64) $nextBytes ∗
              A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
        SepWP (tripleRatchetProgAtExt b ext) ret_pc s
          (memRegion (sp0 - 600#64) $prevBytes ∗
            A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗
            optPolyCacheSlotAt A (sp0 - $slotBv) opt ∗ P) post := by
      have hdealloc := sub_ok_at_of_fnAddr hdealloc0 decodedMessageName (num% (ls_off% "__rustc::__rust_dealloc" - 0x66788))
      decodedMessageBin_fetches_range b (Rust.withPanics ext) $startOff 28
      dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at *
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
      examples_hide_fetches
      have hsp_align : s.sp &&& 15#64 = 0#64 := by
        rw [hsp]; exact sp672_aligned sp0 hsp0
      cases opt with
      | none =>
        unfold optPolyCacheSlotAt
        rw [pull_none_slot]
        have hslt := noneCap_slt_one
        wp_steps 3
        refine SepWP.weaken_pre
          (merge_prev_slot_none sp0 (sp0 - $slotBv) $prevBytes $nextBytes rfl (by decide) (by bv_omega) _) ?_
        apply hcont
        · simp [wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm, hstat]
        · simpa [wp_norm, arm64_norm] using hsp
        · simp [wp_norm, arm64_norm]
      | some p =>
        rw [pull_some_slot]
        apply SepWP.exists_left; intro ptr_p
        refine SepWP.pure_elim ?_
        rintro ⟨hp_ge1, hp_le, _⟩
        have hslt := bv64_slt_one_of_ge1_le65536 hp_ge1 hp_le
        have htoNat := bv64_lsl1_toNat_of_le65536 hp_le
        have hne0 := bv64_ofNat_ne0_of_ge1 hp_ge1 hp_le
        refine SepWP.weaken_pre (dropPolySlot_some_to_dealloc A (sp0 - $slotBv) ptr_p p _) ?_
        wp_steps 7
        wp_call hdealloc
        wp_conv_pre => rw [hsp]
        refine SepWP.weaken_pre
          (show _ ⊢
            (((sp0 - $slotBv) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
              (((sp0 - $slotBv) + 8#64) ↦₆₄ ptr_p) ∗
              (((sp0 - $slotBv) + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length)) ∗
              (memRegion (sp0 - 600#64) $prevBytes ∗
                A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) by
            simp only [arm64_norm]
            exact Entails.of_eq (by ac_rfl)) ?_
        refine SepWP.weaken_pre
          (merge_prev_slot_some sp0 (sp0 - $slotBv) $prevBytes $nextBytes rfl (by decide) (by bv_omega) _ _ _ _) ?_
        exact hcont _ hpc_sf hrun_sf (by rw [hsp_sf, hsp]) (by simp [traceVRegs, wp_norm, arm64_norm, *]))

def_drop_poly_slot dropPolySlot_1_sepWP  1484 1484#64 1512#64 576#64 24  48
def_drop_poly_slot dropPolySlot_2_sepWP  1512 1512#64 1540#64 552#64 48  72
def_drop_poly_slot dropPolySlot_3_sepWP  1540 1540#64 1568#64 528#64 72  96
def_drop_poly_slot dropPolySlot_4_sepWP  1568 1568#64 1596#64 504#64 96  120
def_drop_poly_slot dropPolySlot_5_sepWP  1596 1596#64 1624#64 480#64 120 144
def_drop_poly_slot dropPolySlot_6_sepWP  1624 1624#64 1652#64 456#64 144 168
def_drop_poly_slot dropPolySlot_7_sepWP  1652 1652#64 1680#64 432#64 168 192
def_drop_poly_slot dropPolySlot_8_sepWP  1680 1680#64 1708#64 408#64 192 216
def_drop_poly_slot dropPolySlot_9_sepWP  1708 1708#64 1736#64 384#64 216 240
def_drop_poly_slot dropPolySlot_10_sepWP 1736 1736#64 1764#64 360#64 240 264
def_drop_poly_slot dropPolySlot_11_sepWP 1764 1764#64 1792#64 336#64 264 288
def_drop_poly_slot dropPolySlot_12_sepWP 1792 1792#64 1820#64 312#64 288 312
def_drop_poly_slot dropPolySlot_13_sepWP 1820 1820#64 1848#64 288#64 312 336
def_drop_poly_slot dropPolySlot_14_sepWP 1848 1848#64 1876#64 264#64 336 360
def_drop_poly_slot dropPolySlot_15_sepWP 1876 1876#64 1904#64 240#64 360 384

theorem optPolyCacheListAt_15_eq (A : RustAlloc) (sp0 : BitVec 64)
    (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Option Poly) (P : SepProp) :
    optPolyCacheListAt A (sp0 - 576#64)
      [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗ P =
      optPolyCacheSlotAt A (sp0 - 576#64) p1 ∗
      optPolyCacheSlotAt A (sp0 - 552#64) p2 ∗
      optPolyCacheSlotAt A (sp0 - 528#64) p3 ∗
      optPolyCacheSlotAt A (sp0 - 504#64) p4 ∗
      optPolyCacheSlotAt A (sp0 - 480#64) p5 ∗
      optPolyCacheSlotAt A (sp0 - 456#64) p6 ∗
      optPolyCacheSlotAt A (sp0 - 432#64) p7 ∗
      optPolyCacheSlotAt A (sp0 - 408#64) p8 ∗
      optPolyCacheSlotAt A (sp0 - 384#64) p9 ∗
      optPolyCacheSlotAt A (sp0 - 360#64) p10 ∗
      optPolyCacheSlotAt A (sp0 - 336#64) p11 ∗
      optPolyCacheSlotAt A (sp0 - 312#64) p12 ∗
      optPolyCacheSlotAt A (sp0 - 288#64) p13 ∗
      optPolyCacheSlotAt A (sp0 - 264#64) p14 ∗
      optPolyCacheSlotAt A (sp0 - 240#64) p15 ∗ P := by
  simp only [optPolyCacheListAt, vecHeaderBytes, arrayAt, arm64_norm, sepConj_emp, sepConj_assoc]

theorem list_length_16_eq {α : Type _} (xs : List α) (h : xs.length = 16) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
      xs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] :=
  match xs, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15], _ =>
    ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, rfl⟩

/-- Drops slots `1..15` (`0x6c14c..0x6c2f0`, `entry + 1484#64` to `entry + 1904#64`),
    merging `memRegion (sp0 - 600#64) 24` and the 15 slots into `memRegion (sp0 - 600#64) 384`. -/
theorem dropOptPolyCache_1_to_15_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hdealloc0 : DeallocContract b A ext)
    (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Option Poly)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1484#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1904#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (memRegion (sp0 - 600#64) 384 ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (memRegion (sp0 - 600#64) 24 ∗
        A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗
        optPolyCacheListAt A (sp0 - 576#64)
          [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗ P) post := by
  rw [optPolyCacheListAt_15_eq]
  refine dropPolySlot_1_sepWP hdealloc0 sp0 hsp0 p1 s _ post hpc hstat hsp (fun s1 hpc1 hstat1 hsp1 htr1 => ?_)
  refine dropPolySlot_2_sepWP hdealloc0 sp0 hsp0 p2 s1 _ post hpc1 hstat1 hsp1 (fun s2 hpc2 hstat2 hsp2 htr2 => ?_)
  refine dropPolySlot_3_sepWP hdealloc0 sp0 hsp0 p3 s2 _ post hpc2 hstat2 hsp2 (fun s3 hpc3 hstat3 hsp3 htr3 => ?_)
  refine dropPolySlot_4_sepWP hdealloc0 sp0 hsp0 p4 s3 _ post hpc3 hstat3 hsp3 (fun s4 hpc4 hstat4 hsp4 htr4 => ?_)
  refine dropPolySlot_5_sepWP hdealloc0 sp0 hsp0 p5 s4 _ post hpc4 hstat4 hsp4 (fun s5 hpc5 hstat5 hsp5 htr5 => ?_)
  refine dropPolySlot_6_sepWP hdealloc0 sp0 hsp0 p6 s5 _ post hpc5 hstat5 hsp5 (fun s6 hpc6 hstat6 hsp6 htr6 => ?_)
  refine dropPolySlot_7_sepWP hdealloc0 sp0 hsp0 p7 s6 _ post hpc6 hstat6 hsp6 (fun s7 hpc7 hstat7 hsp7 htr7 => ?_)
  refine dropPolySlot_8_sepWP hdealloc0 sp0 hsp0 p8 s7 _ post hpc7 hstat7 hsp7 (fun s8 hpc8 hstat8 hsp8 htr8 => ?_)
  refine dropPolySlot_9_sepWP hdealloc0 sp0 hsp0 p9 s8 _ post hpc8 hstat8 hsp8 (fun s9 hpc9 hstat9 hsp9 htr9 => ?_)
  refine dropPolySlot_10_sepWP hdealloc0 sp0 hsp0 p10 s9 _ post hpc9 hstat9 hsp9 (fun s10 hpc10 hstat10 hsp10 htr10 => ?_)
  refine dropPolySlot_11_sepWP hdealloc0 sp0 hsp0 p11 s10 _ post hpc10 hstat10 hsp10 (fun s11 hpc11 hstat11 hsp11 htr11 => ?_)
  refine dropPolySlot_12_sepWP hdealloc0 sp0 hsp0 p12 s11 _ post hpc11 hstat11 hsp11 (fun s12 hpc12 hstat12 hsp12 htr12 => ?_)
  refine dropPolySlot_13_sepWP hdealloc0 sp0 hsp0 p13 s12 _ post hpc12 hstat12 hsp12 (fun s13 hpc13 hstat13 hsp13 htr13 => ?_)
  refine dropPolySlot_14_sepWP hdealloc0 sp0 hsp0 p14 s13 _ post hpc13 hstat13 hsp13 (fun s14 hpc14 hstat14 hsp14 htr14 => ?_)
  refine dropPolySlot_15_sepWP hdealloc0 sp0 hsp0 p15 s14 _ post hpc14 hstat14 hsp14 (fun s15 hpc15 hstat15 hsp15 htr15 => ?_)
  exact hcont s15 hpc15 hstat15 hsp15
    (by rw [htr15, htr14, htr13, htr12, htr11, htr10, htr9, htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1])

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp216_add_8 (sp0 : BitVec 64) : sp0 - 216#64 + 8#64 = sp0 - 208#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp216_add_16 (sp0 : BitVec 64) : sp0 - 216#64 + 16#64 = sp0 - 200#64 := by bv_omega

theorem memRegion24_eq_exists_three (a : BitVec 64) :
    memRegion a vecHeaderBytes =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [show vecHeaderBytes = 8 + (8 + 8) from rfl,
    memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), h16,
    ProofLib.memRegion_eight a,
    ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64)]

theorem fold_optVecU8Of_some_nil (A : RustAlloc) (out_sret : BitVec 64) :
    (out_sret ↦₆₄ 0#64) ∗ ((out_sret + 8#64) ↦₆₄ 1#64) ∗ ((out_sret + 16#64) ↦₆₄ 0#64) ⊢
      optVecU8Of A out_sret (some []) := by
  unfold optVecU8Of vecU8 vecU8At vecHeader
  dsimp only
  apply Entails.sepExists_right 0#64
  apply Entails.sepExists_right 1#64
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]
  have hpure : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  rw [sepConj_comm _ ⌜_⌝]
  exact Entails.pure_right hpure (Entails.refl _)

theorem fold_optVecU8Of_some (A : RustAlloc) (out_sret out_ptr : BitVec 64)
    (outFinal : List (BitVec 8)) (n : Nat)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 2 * (16 * 65536))
    (hlen : outFinal.length = n) (hptr : out_ptr ≠ 0#64) :
    (out_sret ↦₆₄ BitVec.ofNat 64 n) ∗
      ((out_sret + 8#64) ↦₆₄ out_ptr) ∗
      ((out_sret + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      A.live out_ptr n 1 ∗
      (out_ptr ↦ₛ outFinal) ⊢
      optVecU8Of A out_sret (some outFinal) := by
  have hcap_ne : BitVec.ofNat 64 n ≠ 0 :=
    ofNat_ne_zero_of_pos (by omega) (by omega)
  have hcap_toNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold optVecU8Of vecU8 vecU8At vecHeader
  dsimp only
  apply Entails.sepExists_right (BitVec.ofNat 64 n)
  apply Entails.sepExists_right out_ptr
  simp only [hcap_ne, ↓reduceIte, hcap_toNat, hlen, Nat.sub_self, memRegion_zero, sepConj_emp]
  have hpure : n ≤ n ∧ n < 2 ^ 63 ∧ out_ptr ≠ 0 := ⟨Nat.le_refl n, by omega, hptr⟩
  rw [sepConj_comm _ (⌜_⌝ ∗ _), sepConj_assoc]
  refine Entails.pure_right hpure ?_
  exact Entails.of_eq (by ac_rfl)

/-- Copy `out` header to `out_sret` and drop `polys[0..16]` (`0x6c0fc..0x6c2f0`, `entry + 1404#64` to `entry + 1904#64`),
    entered after `decodedMessageLoop_wpp` when `1 ≤ dec.ptsNeeded`. -/
theorem dropOptPolyCache_from1404_sepWP_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hdealloc0 : DeallocContract b A ext)
    (sp0 out_sret out_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (ptsNeeded : Nat) (hge1 : 1 ≤ ptsNeeded) (hle : ptsNeeded ≤ 16 * 65536)
    (polys : List (Option Poly)) (hpolys : polys.length = 16)
    (outFinal : List (BitVec 8)) (hout_len : outFinal.length = 2 * ptsNeeded)
    (hout_ptr : out_ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1404#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1904#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (optVecU8Of A out_sret (some outFinal) ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 600#64) 384 ∗
          memRegion (sp0 - 216#64) 24 ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (optPolyCacheListAt A (sp0 - 600#64) polys ∗
        ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        memRegion out_sret vecHeaderBytes ∗
        A.live out_ptr (2 * ptsNeeded) 1 ∗
        (out_ptr ↦ₛ outFinal) ∗
        A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post := by
  rcases list_length_16_eq polys hpolys with
    ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, rfl⟩
  have hdealloc := sub_ok_at_of_fnAddr hdealloc0 decodedMessageName (num% (ls_off% "__rustc::__rust_dealloc" - 0x66788))
  have h1_15 := @dropOptPolyCache_1_to_15_sepWP b A ext ret_pc hdealloc0 sp0 hsp0
    p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 1404 56
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hsplit_head :
      optPolyCacheListAt A (sp0 - 600#64)
        [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] =
      optPolyCacheSlotAt A (sp0 - 600#64) p0 ∗
        optPolyCacheListAt A (sp0 - 576#64)
          [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] := by
    unfold optPolyCacheListAt vecHeaderBytes
    rw [Alloc.arrayAt_cons]
    simp only [arm64_norm]
  rw [hsplit_head, memRegion24_eq_exists_three out_sret]
  wp_pull_exists
  cases p0 with
  | none =>
    unfold optPolyCacheSlotAt
    rw [sepConj_assoc]
    have hslt := noneCap_slt_one
    wp_steps 9
    refine SepWP.weaken_pre
      (show _ ⊢
        (((sp0 - 600#64) ↦₆₄ noneCap) ∗ memRegion (sp0 - 600#64 + 8#64) 16) ∗
          (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
            ((sp0 - 216#64 + 8#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 216#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded))) ∗
          ((out_sret ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
            ((out_sret + 8#64) ↦₆₄ out_ptr) ∗
            ((out_sret + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
            A.live out_ptr (2 * ptsNeeded) 1 ∗
            (out_ptr ↦ₛ outFinal)) ∗
          (A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗
            optPolyCacheListAt A (sp0 - 576#64)
              [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗ P) by
        simp only [arm64_norm]
        exact Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.weaken_pre
      (sepConj_mono (optPolyCacheSlot_none_entails_memRegion24 (sp0 - 600#64))
        (sepConj_mono
          (pointsTo64_three_entails_memRegion24 (sp0 - 216#64)
            (BitVec.ofNat 64 (2 * ptsNeeded)) out_ptr (BitVec.ofNat 64 (2 * ptsNeeded)))
          (sepConj_mono_left
            (fold_optVecU8Of_some A out_sret out_ptr outFinal (2 * ptsNeeded)
              (by omega) (by omega) hout_len hout_ptr)))) ?_
    refine SepWP.weaken_pre
      (show _ ⊢
        memRegion (sp0 - 600#64) 24 ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗
          optPolyCacheListAt A (sp0 - 576#64)
            [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
          (optVecU8Of A out_sret (some outFinal) ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗
            memRegion (sp0 - 216#64) 24 ∗ P) by
        exact Entails.of_eq (by ac_rfl)) ?_
    refine h1_15 _ _ post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simpa [wp_norm, arm64_norm] using hsp)
      (fun sf hpc_f hstat_f hsp_f htr_f => ?_)
    refine SepWP.weaken_pre
      (show _ ⊢
        optVecU8Of A out_sret (some outFinal) ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 600#64) 384 ∗
          memRegion (sp0 - 216#64) 24 ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P by
        exact Entails.of_eq (by ac_rfl)) ?_
    exact hcont sf hpc_f hstat_f hsp_f (by simpa [wp_norm, arm64_norm] using htr_f)
  | some p =>
    unfold optPolyCacheSlotAt
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro ptr_p
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim ?_
    rintro ⟨hp_ge1, hp_le, _⟩
    have hslt := bv64_slt_one_of_ge1_le65536 hp_ge1 hp_le
    have htoNat := bv64_lsl1_toNat_of_le65536 hp_le
    have hne0 := bv64_ofNat_ne0_of_ge1 hp_ge1 hp_le
    simp only [sepConj_assoc]
    refine SepWP.weaken_pre (dropPolySlot_some_to_dealloc A (sp0 - 600#64) ptr_p p _) ?_
    wp_steps 13
    wp_call hdealloc
    wp_conv_pre => rw [hsp]
    wp_steps 1
    refine SepWP.weaken_pre
      (show _ ⊢
        (((sp0 - 600#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
          ((sp0 - 600#64 + 8#64) ↦₆₄ ptr_p) ∗
          ((sp0 - 600#64 + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length)) ∗
          (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
            ((sp0 - 216#64 + 8#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 216#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded))) ∗
          ((out_sret ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
            ((out_sret + 8#64) ↦₆₄ out_ptr) ∗
            ((out_sret + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
            A.live out_ptr (2 * ptsNeeded) 1 ∗
            (out_ptr ↦ₛ outFinal)) ∗
          (A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗
            optPolyCacheListAt A (sp0 - 576#64)
              [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗ P) by
        simp only [arm64_norm]
        exact Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.weaken_pre
      (sepConj_mono
        (pointsTo64_three_entails_memRegion24 (sp0 - 600#64)
          (BitVec.ofNat 64 p.coefficients.length) ptr_p (BitVec.ofNat 64 p.coefficients.length))
        (sepConj_mono
          (pointsTo64_three_entails_memRegion24 (sp0 - 216#64)
            (BitVec.ofNat 64 (2 * ptsNeeded)) out_ptr (BitVec.ofNat 64 (2 * ptsNeeded)))
          (sepConj_mono_left
            (fold_optVecU8Of_some A out_sret out_ptr outFinal (2 * ptsNeeded)
              (by omega) (by omega) hout_len hout_ptr)))) ?_
    refine SepWP.weaken_pre
      (show _ ⊢
        memRegion (sp0 - 600#64) 24 ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗
          optPolyCacheListAt A (sp0 - 576#64)
            [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
          (optVecU8Of A out_sret (some outFinal) ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗
            memRegion (sp0 - 216#64) 24 ∗ P) by
        exact Entails.of_eq (by ac_rfl)) ?_
    refine h1_15 _ _ post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun_sf])
      (by rw [State.sp_setPC, hsp_sf, hsp])
      (fun sf' hpc_f hstat_f hsp_f htr_f => ?_)
    refine SepWP.weaken_pre
      (show _ ⊢
        optVecU8Of A out_sret (some outFinal) ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 600#64) 384 ∗
          memRegion (sp0 - 216#64) 24 ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P by
        exact Entails.of_eq (by ac_rfl)) ?_
    exact hcont sf' hpc_f hstat_f hsp_f (by rw [htr_f]; simp [traceVRegs, wp_norm, arm64_norm, *])

theorem dropOptPolyCache_from1404_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64} (hA : AllocContracts b A ext)
    (sp0 out_sret out_ptr : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (ptsNeeded : Nat) (hge1 : 1 ≤ ptsNeeded) (hle : ptsNeeded ≤ 16 * 65536)
    (polys : List (Option Poly)) (hpolys : polys.length = 16)
    (outFinal : List (BitVec 8)) (hout_len : outFinal.length = 2 * ptsNeeded) (hout_ptr : out_ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1404#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1904#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (optVecU8Of A out_sret (some outFinal) ∗ ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 600#64) 384 ∗ memRegion (sp0 - 216#64) 24 ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (optPolyCacheListAt A (sp0 - 600#64) polys ∗ ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗ memRegion out_sret vecHeaderBytes ∗
        A.live out_ptr (2 * ptsNeeded) 1 ∗ (out_ptr ↦ₛ outFinal) ∗
        A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post :=
  dropOptPolyCache_from1404_sepWP_core hA.dealloc sp0 out_sret out_ptr hsp0 ptsNeeded hge1 hle
    polys hpolys outFinal hout_len hout_ptr s P post hpc hstat hsp hx29 hcont

/-- Copy empty `out` header `(0, 1, 0)` to `out_sret` and drop `polys[0..16] = replicate 16 none`
    (`0x6c134..0x6c2f0`, `entry + 1460#64` to `entry + 1904#64`), entered when `dec.ptsNeeded = 0`. -/
theorem dropOptPolyCache_from1460_sepWP_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hdealloc0 : DeallocContract b A ext)
    (sp0 out_sret : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1460#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1904#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (optVecU8Of A out_sret (some []) ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 600#64) 384 ∗
          memRegion (sp0 - 216#64) 24 ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (optPolyCacheListAt A (sp0 - 600#64) (List.replicate 16 none) ∗
        ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        ((sp0 - 216#64) ↦₆₄ 0#64) ∗
        ((sp0 - 208#64) ↦₆₄ 1#64) ∗
        ((sp0 - 200#64) ↦₆₄ 0#64) ∗
        memRegion out_sret vecHeaderBytes ∗
        A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post := by
  have h1_15 := @dropOptPolyCache_1_to_15_sepWP b A ext ret_pc hdealloc0 sp0 hsp0
    none none none none none none none none none none none none none none none
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 1460 24
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hsplit_head :
      optPolyCacheListAt A (sp0 - 600#64) (List.replicate 16 none) =
      ((sp0 - 600#64) ↦₆₄ noneCap) ∗ memRegion (sp0 - 600#64 + 8#64) 16 ∗
        optPolyCacheListAt A (sp0 - 576#64)
          [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] := by
    change optPolyCacheListAt A (sp0 - 600#64)
      (none :: [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) = _
    unfold optPolyCacheListAt vecHeaderBytes
    rw [Alloc.arrayAt_cons]
    unfold optPolyCacheSlotAt
    simp only [arm64_norm, sepConj_assoc]
  rw [hsplit_head, memRegion24_eq_exists_three out_sret]
  wp_pull_exists
  wp_steps 6
  refine SepWP.weaken_pre
    (show _ ⊢
      (((sp0 - 600#64) ↦₆₄ noneCap) ∗ memRegion (sp0 - 600#64 + 8#64) 16) ∗
        (((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64 + 8#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64 + 16#64) ↦₆₄ 0#64)) ∗
        ((out_sret ↦₆₄ 0#64) ∗ ((out_sret + 8#64) ↦₆₄ 1#64) ∗ ((out_sret + 16#64) ↦₆₄ 0#64)) ∗
        (A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗
          optPolyCacheListAt A (sp0 - 576#64)
            [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗ P) by
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWP.weaken_pre
    (sepConj_mono (optPolyCacheSlot_none_entails_memRegion24 (sp0 - 600#64))
      (sepConj_mono (pointsTo64_three_entails_memRegion24 (sp0 - 216#64) 0#64 1#64 0#64)
        (sepConj_mono_left (fold_optVecU8Of_some_nil A out_sret)))) ?_
  refine SepWP.weaken_pre
    (show _ ⊢
      memRegion (sp0 - 600#64) 24 ∗
        A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗
        optPolyCacheListAt A (sp0 - 576#64)
          [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] ∗
        (optVecU8Of A out_sret (some []) ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 216#64) 24 ∗ P) by
      exact Entails.of_eq (by ac_rfl)) ?_
  refine h1_15 _ _ post
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by simpa [wp_norm, arm64_norm] using hsp)
    (fun sf hpc_f hstat_f hsp_f htr_f => ?_)
  refine SepWP.weaken_pre
    (show _ ⊢
      optVecU8Of A out_sret (some []) ∗
        ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        memRegion (sp0 - 600#64) 384 ∗
        memRegion (sp0 - 216#64) 24 ∗
        A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P by
      exact Entails.of_eq (by ac_rfl)) ?_
  exact hcont sf hpc_f hstat_f hsp_f (by simpa [wp_norm, arm64_norm] using htr_f)

theorem dropOptPolyCache_from1460_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64} (hA : AllocContracts b A ext)
    (sp0 out_sret : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1460#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1904#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (optVecU8Of A out_sret (some []) ∗ ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 600#64) 384 ∗ memRegion (sp0 - 216#64) 24 ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (optPolyCacheListAt A (sp0 - 600#64) (List.replicate 16 none) ∗ ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        ((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 1#64) ∗ ((sp0 - 200#64) ↦₆₄ 0#64) ∗
        memRegion out_sret vecHeaderBytes ∗ A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post :=
  dropOptPolyCache_from1460_sepWP_core hA.dealloc sp0 out_sret hsp0 s P post hpc hstat hsp hx29 hcont

/-! ## Stack Layout and Epilogue (`0x6bca0..0x6bcdc` and `0x6c2f0..0x6c2f8`) -/

/-- Saved callee-saved registers `x19..x30` at `[sp0 - 96#64 .. sp0)` (96 bytes). -/
def savedRegsAt (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem memRegion96_eq_exists_twelve (sp0 : BitVec 64) :
    memRegion (sp0 - 96#64) 96 =
      (∃∗ v0 : BitVec 64, (sp0 - 96#64) ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (sp0 - 88#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (sp0 - 80#64) ↦₆₄ v2) ∗
      (∃∗ v3 : BitVec 64, (sp0 - 72#64) ↦₆₄ v3) ∗
      (∃∗ v4 : BitVec 64, (sp0 - 64#64) ↦₆₄ v4) ∗
      (∃∗ v5 : BitVec 64, (sp0 - 56#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (sp0 - 48#64) ↦₆₄ v6) ∗
      (∃∗ v7 : BitVec 64, (sp0 - 40#64) ↦₆₄ v7) ∗
      (∃∗ v8 : BitVec 64, (sp0 - 32#64) ↦₆₄ v8) ∗
      (∃∗ v9 : BitVec 64, (sp0 - 24#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (sp0 - 16#64) ↦₆₄ v10) ∗
      (∃∗ v11 : BitVec 64, (sp0 - 8#64) ↦₆₄ v11) := by
  have ha1 : sp0 - 96#64 + 8#64 = sp0 - 88#64 := by bv_omega
  have ha2 : sp0 - 88#64 + 8#64 = sp0 - 80#64 := by bv_omega
  have ha3 : sp0 - 80#64 + 8#64 = sp0 - 72#64 := by bv_omega
  have ha4 : sp0 - 72#64 + 8#64 = sp0 - 64#64 := by bv_omega
  have ha5 : sp0 - 64#64 + 8#64 = sp0 - 56#64 := by bv_omega
  have ha6 : sp0 - 56#64 + 8#64 = sp0 - 48#64 := by bv_omega
  have ha7 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_omega
  have ha8 : sp0 - 40#64 + 8#64 = sp0 - 32#64 := by bv_omega
  have ha9 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_omega
  have ha10 : sp0 - 24#64 + 8#64 = sp0 - 16#64 := by bv_omega
  have ha11 : sp0 - 16#64 + 8#64 = sp0 - 8#64 := by bv_omega
  rw [show (96 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))))) from rfl,
    memRegion_split (sp0 - 96#64) 8 88 (by decide), ha1,
    memRegion_split (sp0 - 88#64) 8 80 (by decide), ha2,
    memRegion_split (sp0 - 80#64) 8 72 (by decide), ha3,
    memRegion_split (sp0 - 72#64) 8 64 (by decide), ha4,
    memRegion_split (sp0 - 64#64) 8 56 (by decide), ha5,
    memRegion_split (sp0 - 56#64) 8 48 (by decide), ha6,
    memRegion_split (sp0 - 48#64) 8 40 (by decide), ha7,
    memRegion_split (sp0 - 40#64) 8 32 (by decide), ha8,
    memRegion_split (sp0 - 32#64) 8 24 (by decide), ha9,
    memRegion_split (sp0 - 24#64) 8 16 (by decide), ha10,
    memRegion_split (sp0 - 16#64) 8 8 (by decide), ha11,
    ProofLib.memRegion_eight (sp0 - 96#64),
    ProofLib.memRegion_eight (sp0 - 88#64),
    ProofLib.memRegion_eight (sp0 - 80#64),
    ProofLib.memRegion_eight (sp0 - 72#64),
    ProofLib.memRegion_eight (sp0 - 64#64),
    ProofLib.memRegion_eight (sp0 - 56#64),
    ProofLib.memRegion_eight (sp0 - 48#64),
    ProofLib.memRegion_eight (sp0 - 40#64),
    ProofLib.memRegion_eight (sp0 - 32#64),
    ProofLib.memRegion_eight (sp0 - 24#64),
    ProofLib.memRegion_eight (sp0 - 16#64),
    ProofLib.memRegion_eight (sp0 - 8#64)]

theorem savedRegsAt_entails_memRegion96 (sp0 : BitVec 64) (s0 : State) :
    savedRegsAt sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  unfold savedRegsAt
  rw [memRegion96_eq_exists_twelve sp0]
  exact sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
      (Entails.sepExists_intro _)))))))))))

theorem stackAt_decodedMessage_eq (sp0 : BitVec 64) :
    stackAt sp0 decodedMessageStack =
      stackAt (sp0 - 672#64) extHookStack ∗
        memRegion (sp0 - 672#64) 576 ∗
        memRegion (sp0 - 96#64) 96 := by
  unfold stackAt decodedMessageStack extHookStack
  have h1 : sp0 - BitVec.ofNat 64 (16384 + (576 + 96)) = (sp0 - 672#64) - 16384#64 := by bv_omega
  have h2 : (sp0 - 672#64) - 16384#64 + 16384#64 = sp0 - 672#64 := by bv_omega
  have h3 : sp0 - 672#64 + 576#64 = sp0 - 96#64 := by bv_omega
  have h4 : (sp0 - 672#64) - BitVec.ofNat 64 (2 ^ 14) = (sp0 - 672#64) - 16384#64 := rfl
  rw [show (672 + 2 ^ 14 : Nat) = 16384 + (576 + 96) from rfl, h1,
    memRegion_split ((sp0 - 672#64) - 16384#64) 16384 (576 + 96) (by decide), h2,
    memRegion_split (sp0 - 672#64) 576 96 (by decide), h3, h4]
  rfl

theorem stackAt_extHook_eq_allocHook (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 16384#64) 12288 := by
  unfold stackAt extHookStack allocHookStack
  have h0 : sp - BitVec.ofNat 64 (12288 + 4096) = sp - 16384#64 := rfl
  have h1 : sp - 16384#64 + 12288#64 = sp - 4096#64 := by bv_omega
  rw [show (2 ^ 14 : Nat) = 12288 + 4096 from rfl, h0,
    memRegion_split (sp - 16384#64) 12288 4096 (by decide), h1, sepConj_comm]

theorem stackAt_extHook_eq_computeAt (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackAt sp computeAtStack ∗ memRegion (sp - 16384#64) 12032 := by
  unfold stackAt extHookStack computeAtStack growOneStack finishGrowStack allocHookStack
  have h0 : sp - BitVec.ofNat 64 (12032 + (144 + ((4128 + 16) + 64))) = sp - 16384#64 := rfl
  have h1 : sp - 16384#64 + 12032#64 = sp - 4352#64 := by bv_omega
  rw [show (2 ^ 14 : Nat) = 12032 + (144 + ((4128 + 16) + 64)) from rfl, h0,
    memRegion_split (sp - 16384#64) 12032 (144 + ((4128 + 16) + 64)) (by decide), h1, sepConj_comm]

theorem stackAt_computeAt_eq_allocHook (sp : BitVec 64) :
    stackAt sp computeAtStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 4352#64) 256 := by
  unfold stackAt computeAtStack growOneStack finishGrowStack allocHookStack
  have h1 : sp - 4352#64 + 256#64 = sp - 4096#64 := by bv_omega
  rw [show (144 + ((4128 + 16) + 64) : Nat) = 256 + 4096 from rfl,
    memRegion_split (sp - 4352#64) 256 4096 (by decide), h1, sepConj_comm]

theorem memRegion_56_8_512_entails_576 (sp0 pv_ptr : BitVec 64) :
    memRegion (sp0 - 672#64) 56 ∗ ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗ memRegion (sp0 - 608#64) 512 ⊢
      memRegion (sp0 - 672#64) 576 := by
  have h1 : sp0 - 672#64 + 56#64 = sp0 - 616#64 := by bv_omega
  have h2 : sp0 - 616#64 + 8#64 = sp0 - 608#64 := by bv_omega
  rw [show (576 : Nat) = 56 + (8 + 512) from rfl,
    memRegion_split (sp0 - 672#64) 56 (8 + 512) (by decide), h1,
    memRegion_split (sp0 - 616#64) 8 512 (by decide), h2]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion8 (sp0 - 616#64) pv_ptr))

def CalleeSavedGprsPreserved (s₀ sf : State) : Prop :=
  sf.readReg64 .x19 = s₀.readReg64 .x19 ∧
  sf.readReg64 .x20 = s₀.readReg64 .x20 ∧
  sf.readReg64 .x21 = s₀.readReg64 .x21 ∧
  sf.readReg64 .x22 = s₀.readReg64 .x22 ∧
  sf.readReg64 .x23 = s₀.readReg64 .x23 ∧
  sf.readReg64 .x24 = s₀.readReg64 .x24 ∧
  sf.readReg64 .x25 = s₀.readReg64 .x25 ∧
  sf.readReg64 .x26 = s₀.readReg64 .x26 ∧
  sf.readReg64 .x27 = s₀.readReg64 .x27 ∧
  sf.readReg64 .x28 = s₀.readReg64 .x28 ∧
  sf.readReg64 .x29 = s₀.readReg64 .x29

theorem calleeSavedPreserved_of_gprs_traceVRegs {s₀ sf : State}
    (hgprs : CalleeSavedGprsPreserved s₀ sf) (htr : traceVRegs sf = traceVRegs s₀) :
    CalleeSavedPreserved s₀ sf ∧ sf.trace = s₀.trace := by
  rcases hgprs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  exact ⟨⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, htr_vr⟩, htr_tr⟩

/-- Epilogue register restoration and `ret` (`0x6bcc0..0x6bcdc`, `entry + 320#64` to `s0.readReg64 .x30`). -/
theorem decodedMessage_epilogue_ret_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 320#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp0 →
      traceVRegs sf = traceVRegs s →
      CalleeSavedGprsPreserved s0 sf →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (savedRegsAt sp0 s0 ∗
        memRegion (sp0 - 672#64) 576 ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P) post := by
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 320 32
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hsp96_align : (sp0 - 96#64) &&& 15#64 = 0#64 := by
    have h : (sp0 - 96#64) &&& 15#64 = sp0 &&& 15#64 := by bv_bits
    rw [h, hsp0]
  unfold savedRegsAt
  simp only [sepConj_assoc]
  wp_steps 8
  refine SepWP.weaken_pre
    (show _ ⊢ stackAt sp0 decodedMessageStack ∗ P by
      rw [stackAt_decodedMessage_eq sp0]
      refine Entails.trans ?_
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (savedRegsAt_entails_memRegion96 sp0 s0))))
      unfold savedRegsAt
      exact Entails.of_eq (by ac_rfl)) ?_
  apply hcont
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm, hstat]
  · simp [wp_norm, arm64_norm, hsp]
  · simp [wp_norm, arm64_norm]
  · unfold CalleeSavedGprsPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

/-- Epilogue `points_vecs` deallocation and return (`0x6bcb0..0x6bcdc`, `entry + 304#64` to `s0.readReg64 .x30`). -/
theorem decodedMessage_epilogue_dealloc_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc0 : DeallocContract b A ext)
    (s0 : State) (sp0 pv_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 304#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx8 : s.readReg64 .x8 = 16#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp0 →
      traceVRegs sf = traceVRegs s →
      CalleeSavedGprsPreserved s0 sf →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (A.pool ∗ stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 56 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        A.pool ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P) post := by
  have hdealloc := sub_ok_at_of_fnAddr hdealloc0 decodedMessageName (num% (ls_off% "__rustc::__rust_dealloc" - 0x66788))
  have hret := @decodedMessage_epilogue_ret_sepWP b ext s0 sp0 hsp0
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 304 16
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hdealloc hret hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hsub16384 : sp0 - 672#64 - 16384#64 = sp0 - 17056#64 := by bv_omega
  rw [stackAt_extHook_eq_allocHook (sp0 - 672#64)]
  simp only [sepConj_assoc]
  wp_steps 4
  wp_call hdealloc
  wp_conv_pre => rw [hsp]
  refine SepWP.weaken_pre
    (show _ ⊢
      savedRegsAt sp0 s0 ∗
        memRegion (sp0 - 672#64) 576 ∗
        stackAt (sp0 - 672#64) extHookStack ∗ (A.pool ∗ P) by
      rw [stackAt_extHook_eq_allocHook (sp0 - 672#64), hsub16384]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_left (memRegion_56_8_512_entails_576 sp0 pv_ptr)))
      exact Entails.of_eq (by ac_rfl)) ?_
  refine hret _ (A.pool ∗ P) post
    hpc_sf hrun_sf (by rw [hsp_sf, hsp])
    (fun sf' hpc_f hstat_f hsp_f htr_f hcs_f => ?_)
  refine SepWP.weaken_pre
    (show stackAt sp0 decodedMessageStack ∗ (A.pool ∗ P) ⊢
      A.pool ∗ stackAt sp0 decodedMessageStack ∗ P by
      exact Entails.of_eq (by ac_rfl)) ?_
  exact hcont sf' hpc_f hstat_f hsp_f (by rw [htr_f]; simp [traceVRegs, wp_norm, arm64_norm, *]) hcs_f

theorem memRegion_48_8_entails_56 (sp0 w : BitVec 64) :
    memRegion (sp0 - 672#64) 48 ∗ ((sp0 - 624#64) ↦₆₄ w) ⊢ memRegion (sp0 - 672#64) 56 := by
  have h1 : sp0 - 672#64 + 48#64 = sp0 - 624#64 := by bv_omega
  rw [show (56 : Nat) = 48 + 8 from rfl, memRegion_split (sp0 - 672#64) 48 8 (by decide), h1]
  exact sepConj_mono_right (pointsTo64_entails_memRegion8 (sp0 - 624#64) w)

/-- Epilogue from `0x6c2f0 (+1904)` (`ldr x8, [sp, #0x30]; cbnz x8, 0x6bcb0`) to return. -/
theorem decodedMessage_epilogue_from1904_sepWP_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc0 : DeallocContract b A ext)
    (s0 : State) (sp0 pv_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1904#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp0 →
      traceVRegs sf = traceVRegs s →
      CalleeSavedGprsPreserved s0 sf →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (A.pool ∗ stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((sp0 - 624#64) ↦₆₄ 16#64) ∗
        ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 48 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        A.pool ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P) post := by
  have hdealloc_ep := @decodedMessage_epilogue_dealloc_sepWP b A ext hdealloc0 s0 sp0 pv_ptr hsp0
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 1904 8
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  wp_steps 2
  refine SepWP.weaken_pre
    (show _ ⊢
      (memRegion (sp0 - 672#64) 48 ∗ ((sp0 - 624#64) ↦₆₄ 16#64)) ∗
        (((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
          A.live pv_ptr 256 8 ∗
          memRegion pv_ptr 256 ∗
          memRegion (sp0 - 608#64) 512 ∗
          savedRegsAt sp0 s0 ∗
          A.pool ∗
          stackAt (sp0 - 672#64) extHookStack ∗ P) by
      exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_48_8_entails_56 sp0 16#64)) ?_
  refine SepWP.weaken_pre
    (show _ ⊢
      ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 56 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        A.pool ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P by
      exact Entails.of_eq (by ac_rfl)) ?_
  refine hdealloc_ep _ P post
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by simpa [wp_norm, arm64_norm] using hsp)
    (by simp [wp_norm, arm64_norm])
    (fun sf hpc_f hstat_f hsp_f htr_f hcs_f => ?_)
  exact hcont sf hpc_f hstat_f hsp_f (by simpa [wp_norm, arm64_norm] using htr_f) hcs_f

theorem decodedMessage_epilogue_from1904_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 : State) (sp0 pv_ptr : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1904#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = sp0 →
      traceVRegs sf = traceVRegs s → CalleeSavedGprsPreserved s0 sf →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (A.pool ∗ stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((sp0 - 624#64) ↦₆₄ 16#64) ∗ ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗ A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗ memRegion (sp0 - 672#64) 48 ∗ memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗ A.pool ∗ stackAt (sp0 - 672#64) extHookStack ∗ P) post :=
  decodedMessage_epilogue_from1904_sepWP_core hA.dealloc s0 sp0 pv_ptr hsp0 s P post hpc hstat hsp hcont

theorem memRegion_24_8_8_8_8_entails_56 (sp0 w648 w632 w624 : BitVec 64) :
    memRegion (sp0 - 672#64) 24 ∗
      ((sp0 - 648#64) ↦₆₄ w648) ∗
      memRegion (sp0 - 640#64) 8 ∗
      ((sp0 - 632#64) ↦₆₄ w632) ∗
      ((sp0 - 624#64) ↦₆₄ w624) ⊢
      memRegion (sp0 - 672#64) 56 := by
  have h1 : sp0 - 672#64 + 24#64 = sp0 - 648#64 := by bv_omega
  have h2 : sp0 - 648#64 + 8#64 = sp0 - 640#64 := by bv_omega
  have h3 : sp0 - 640#64 + 8#64 = sp0 - 632#64 := by bv_omega
  have h4 : sp0 - 632#64 + 8#64 = sp0 - 624#64 := by bv_omega
  rw [show (56 : Nat) = 24 + (8 + (8 + (8 + 8))) from rfl,
    memRegion_split (sp0 - 672#64) 24 32 (by decide), h1,
    memRegion_split (sp0 - 648#64) 8 24 (by decide), h2,
    memRegion_split (sp0 - 640#64) 8 16 (by decide), h3,
    memRegion_split (sp0 - 632#64) 8 8 (by decide), h4]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion8 (sp0 - 648#64) w648)
      (sepConj_mono_right
        (sepConj_mono (pointsTo64_entails_memRegion8 (sp0 - 632#64) w632)
          (pointsTo64_entails_memRegion8 (sp0 - 624#64) w624))))

theorem memRegion_8_504_entails_512 (sp0 w608 : BitVec 64) :
    ((sp0 - 608#64) ↦₆₄ w608) ∗ memRegion (sp0 - 600#64) 504 ⊢
      memRegion (sp0 - 608#64) 512 := by
  have h1 : sp0 - 608#64 + 8#64 = sp0 - 600#64 := by bv_omega
  rw [show (512 : Nat) = 8 + 504 from rfl, memRegion_split (sp0 - 608#64) 8 504 (by decide), h1]
  exact sepConj_mono_left (pointsTo64_entails_memRegion8 (sp0 - 608#64) w608)

/-- Epilogue from `0x6bca0 (+288)` (when `(collectPointsVecsTotal dec 0 16 false []).1 = true`):
    stores `none` to `out_sret`, deallocates `points_vecs`, and returns. -/
theorem decodedMessage_epilogue_from288_sepWP_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc0 : DeallocContract b A ext)
    (s0 : State) (sp0 out_sret pv_ptr w648 pvLenFinal : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 288#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp0 →
      traceVRegs sf = traceVRegs s →
      CalleeSavedGprsPreserved s0 sf →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (optVecU8Of A out_sret none ∗
          A.pool ∗ stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((sp0 - 648#64) ↦₆₄ w648) ∗
        ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        ((sp0 - 624#64) ↦₆₄ 16#64) ∗
        ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ pvLenFinal) ∗
        memRegion out_sret vecHeaderBytes ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 24 ∗
        memRegion (sp0 - 640#64) 8 ∗
        memRegion (sp0 - 600#64) 504 ∗
        savedRegsAt sp0 s0 ∗
        A.pool ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P) post := by
  have hdealloc_ep := @decodedMessage_epilogue_dealloc_sepWP b A ext hdealloc0 s0 sp0 pv_ptr hsp0
  decodedMessageBin_fetches_range b (Rust.withPanics ext) 288 16
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hout_split : memRegion out_sret vecHeaderBytes =
      (∃∗ w0 : BitVec 64, out_sret ↦₆₄ w0) ∗ memRegion (out_sret + 8#64) 16 := by
    rw [show vecHeaderBytes = 8 + 16 from rfl,
      memRegion_split out_sret 8 16 (by decide),
      ProofLib.memRegion_eight out_sret]
  rw [hout_split]
  wp_pull_exists
  wp_steps 4
  have hnone_eq :
      (out_sret ↦₆₄ 18446744073709551615#64) ∗ memRegion (out_sret + 8#64) 16 =
        optVecU8Of A out_sret none := by
    unfold optVecU8Of noneCap; rfl
  refine SepWP.weaken_pre
    (show _ ⊢
      (memRegion (sp0 - 672#64) 24 ∗
        ((sp0 - 648#64) ↦₆₄ w648) ∗
        memRegion (sp0 - 640#64) 8 ∗
        ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        ((sp0 - 624#64) ↦₆₄ 16#64)) ∗
      (((sp0 - 608#64) ↦₆₄ pvLenFinal) ∗ memRegion (sp0 - 600#64) 504) ∗
      (((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        savedRegsAt sp0 s0 ∗
        A.pool ∗
        stackAt (sp0 - 672#64) extHookStack ∗
        (optVecU8Of A out_sret none ∗ P)) by
      rw [← hnone_eq]
      exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWP.weaken_pre
    (sepConj_mono (memRegion_24_8_8_8_8_entails_56 sp0 w648 out_sret 16#64)
      (sepConj_mono_left (memRegion_8_504_entails_512 sp0 pvLenFinal))) ?_
  refine SepWP.weaken_pre
    (show _ ⊢
      ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 56 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        A.pool ∗
        stackAt (sp0 - 672#64) extHookStack ∗
        (optVecU8Of A out_sret none ∗ P) by
      exact Entails.of_eq (by ac_rfl)) ?_
  refine hdealloc_ep _ (optVecU8Of A out_sret none ∗ P) post
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by simpa [wp_norm, arm64_norm] using hsp)
    (by simp [wp_norm, arm64_norm])
    (fun sf hpc_f hstat_f hsp_f htr_f hcs_f => ?_)
  refine SepWP.weaken_pre
    (show A.pool ∗ stackAt sp0 decodedMessageStack ∗ (optVecU8Of A out_sret none ∗ P) ⊢
      optVecU8Of A out_sret none ∗ A.pool ∗ stackAt sp0 decodedMessageStack ∗ P by
      exact Entails.of_eq (by ac_rfl)) ?_
  exact hcont sf hpc_f hstat_f hsp_f (by simpa [wp_norm, arm64_norm] using htr_f) hcs_f

theorem decodedMessage_epilogue_from288_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 : State) (sp0 out_sret pv_ptr w648 pvLenFinal : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 288#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = sp0 →
      traceVRegs sf = traceVRegs s → CalleeSavedGprsPreserved s0 sf →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (optVecU8Of A out_sret none ∗ A.pool ∗ stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((sp0 - 648#64) ↦₆₄ w648) ∗ ((sp0 - 632#64) ↦₆₄ out_sret) ∗ ((sp0 - 624#64) ↦₆₄ 16#64) ∗
        ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗ ((sp0 - 608#64) ↦₆₄ pvLenFinal) ∗
        memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗ memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 24 ∗ memRegion (sp0 - 640#64) 8 ∗ memRegion (sp0 - 600#64) 504 ∗
        savedRegsAt sp0 s0 ∗ A.pool ∗ stackAt (sp0 - 672#64) extHookStack ∗ P) post :=
  decodedMessage_epilogue_from288_sepWP_core hA.dealloc s0 sp0 out_sret pv_ptr w648 pvLenFinal
    hsp0 s P post hpc hstat hsp hcont

end CryptoVerification.SpqrV1.Poly.DecodedMessage
