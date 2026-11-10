/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack `.points` Loop and `.polys` Allocation Steps for `<PolyEncoder>::from_pb`

Lifts `pts_elem_even_nonempty_step`, `pts_elem_even_step`, `pts_outer_loop`, and `.polys` initial
buffer allocations `0..11` (`polys_alloc_0_3`, `polys_alloc_4_7`, `polys_alloc_8_11`) to
`AllocContracts4K`.
-/

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit
  ofNat_succ_sub_one ofNat_succ_add_neg_one zeroExtend_setWidth32_setWidth8
  madd_24_eq mul_24_eq fsp_add_201_add_255 fsp_add_255_add_201 exists_pow_two_eq_two
  add_neg_64_eq_sub_64 add_neg_48_eq_sub_48 add_neg_32_eq_sub_32
  add_neg_24_eq_sub_24 add_neg_16_eq_sub_16
  fsp_928_sub_64 fsp_928_sub_48 fsp_928_sub_32 fsp_928_sub_24 fsp_928_sub_16

/-! ## `.points` Deserialization Loop (`+260 -> +1612 / +1648`) -/

theorem pts_elem_even_nonempty_step_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext) (j m : Nat) (bs : List (BitVec 8))
    (s0 s : State) (fsp ptsPtr bsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hlen : bs.length = 2 * (m + 1)) (hmax : bs.length < 2 ^ 62)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 2#64) (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j) (hx25 : s.readReg64 .x25 = ptsPtr)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm,
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 476#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) →
      sm.readReg64 .x21 = 2#64 → sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = BitVec.ofNat 64 j → sm.readReg64 .x25 = ptsPtr →
      sm.readReg64 .x26 = s.readReg64 .x1 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗ emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          (∃∗ cap, ∃∗ outPtr,
            ((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
            vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗ emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have heven : bs.length % 2 = 0 := by omega
  have hpos : 0 < bs.length := by omega
  have hn64 : bs.length < 2 ^ 64 := by omega
  have h2n64 : 2 * bs.length < 2 ^ 64 := by omega
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk (2 * bs.length) 2 := ⟨by omega, hpow2, by omega⟩
  have h2len_toNat : (BitVec.ofNat 64 (2 * bs.length)).toNat = 2 * bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2n64]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbit32 := bit0_and_32_eq_zero_of_even heven hmax
  have hbit64 := bit0_and_64_eq_zero_of_even heven hmax
  have hlsr1 := lsr_62_eq_zero hmax
  have hlsr2 := lsr_62_nat_eq_zero hmax
  have hne0 := ofNat_ne_zero_of_pos hpos hn64
  have hbeq0 := ofNat_beq_zero_false_of_pos hpos hn64
  have hlsl1 := shiftLeft_1_eq_mul_2 hmax
  have hlsl2 := shiftLeft_1_nat_eq_mul_2 hmax
  have hlen_fn : True → bs.length = 2 * (m + 1) := fun _ => hlen
  clear hlen
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc"))
  simp only [rustAllocSpec] at halloc
  have hpanic1536 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_1536 b ext Q s0 s P R
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 260 220
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1536 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 308#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr0
    refine hpanic1536 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr0⟩
    have hbeq_oom : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    set outPtr := sf_1.readReg64 (Reg.gpr 0#5)
    rw [cells_456_eq fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v0
    apply SepWPp.exists_elim; intro v1
    apply SepWPp.exists_elim; intro v2
    apply SepWPp.of_sepWP (mid := entry + 376#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hlen := hlen_fn trivial
    have hsplit_len : 2 * bs.length = bs.length + bs.length := by omega
    have hsplit_bound : bs.length + bs.length ≤ 2 ^ 64 := by omega
    rw [hsplit_len, ProofLib.memRegion_split outPtr bs.length bs.length hsplit_bound]
    refine SepWPp.weaken_pre
      (by dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]; simp only [BitVec.add_zero, h_1, hsp]; exact Entails.of_eq (by ac_rfl))
      (sepWPp_seq_clean
        (pts_inner_loop (b := b) (ext := ext) m bs 0 bs.length _ fsp
          (ptsPtr + BitVec.ofNat 64 (24 * j)) bsPtr outPtr 0#64 hfsp_align
          (A.live outPtr (bs.length + bs.length) 2 ∗
            memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length ∗
            ((fsp + 464#64) ↦₆₄ outPtr) ∗
            emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hlen (by omega) hmax
          (by dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat]; simp only [arm64_norm, wp_norm, hentry, *])
          (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, Reg.x8, outPtr, *])
          (by simp only [arm64_norm, wp_norm, Reg.x19, *])
          (by simp only [arm64_norm, wp_norm, Reg.x20, *])
          (by simp only [arm64_norm, wp_norm, Reg.x22, outPtr, *])
          (by simp only [arm64_norm, wp_norm, Reg.x23, *])
          (by simp only [arm64_norm, wp_norm, Reg.x28, *]))
        ?_)
    intro s3 hpc3 hrun3 ⟨hsp3, hx20_3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx29_3, htr3, hvregs3⟩
    dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc3
    rw [hentry] at hpc3
    dsimp only [emptySlotAt, BitVec.ofNat_eq_ofNat]
    simp only [BitVec.add_zero, Nat.zero_add]
    refine sepWPp_seq_clean
      (mid := entry + 476#64)
      (P_mid :=
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        (∃∗ cap, ∃∗ outPtr,
          ((fsp + 456#64) ↦₆₄ cap) ∗
          ((fsp + 464#64) ↦₆₄ outPtr) ∗
          ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
          vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun s4 =>
        s4.sp = fsp ∧
        s4.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) ∧
        s4.readReg64 .x21 = 2#64 ∧
        s4.readReg64 .x23 = 24#64 ∧
        s4.readReg64 .x24 = BitVec.ofNat 64 j ∧
        s4.readReg64 .x25 = ptsPtr ∧
        s4.readReg64 .x26 = s.readReg64 .x1 ∧
        s4.readReg64 .x29 = s.readReg64 .x29 ∧
        s4.trace = s0.trace ∧
        calleeSavedVRegs s4 = calleeSavedVRegs s0)
      ?_ ?_
    · have hx24_s3 : s3.readReg64 .x24 = BitVec.ofNat 64 j := by
        rw [hx24_3]; simp only [arm64_norm, wp_norm, Reg.x24, *]
      wp_steps
      refine align_pre ?_ ?_
      · have hpts_len := bytesToGF16ListTotal_length (m + 1) bs hlen
        have hcap_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
        dsimp only [emptySlotAt]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             ((fsp + 464#64) ↦₆₄ outPtr) ∗
             ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
             A.live outPtr (bs.length + bs.length) 2 ∗
             arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs) ∗
             memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
             ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             (bsPtr ↦ₛ bs) ∗
             (((fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ↦₆₄ 0#64) ∗
              ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ 2#64) ∗
              ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64)) ∗
             A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono_left
            (show ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
              ((fsp + 464#64) ↦₆₄ outPtr) ∗
              ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
              A.live outPtr (bs.length + bs.length) 2 ∗
              arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs) ∗
              memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length ⊢
              ∃∗ cap, ∃∗ outPtr,
                ((fsp + 456#64) ↦₆₄ cap) ∗
                ((fsp + 464#64) ↦₆₄ outPtr) ∗
                ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
                vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs) by
              refine Entails.sepExists_right (BitVec.ofNat 64 bs.length)
                (Entails.sepExists_right outPtr ?_)
              unfold vecBuf
              have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := hne0
              rw [hpts_len, hcap_toNat]
              simp only [hcap_ne, ↓reduceIte]
              have hmul2 : bs.length * 2 = bs.length + bs.length := by omega
              have hm2 : (m + 1) * 2 = bs.length := by omega
              have hsub2 : (bs.length - (m + 1)) * 2 = bs.length := by omega
              rw [hmul2, hm2, hsub2]
              simp only [sepConj_pure_left_comm]
              refine Entails.pure_right ⟨by omega, by omega, hoom⟩ ?_
              exact Entails.of_eq (by ac_rfl)))
          (Entails.of_eq (by ac_rfl))
      · apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨Entails.refl _, by wp_norm_goal, by wp_norm_goal, ?_, by wp_norm_goal,
          by wp_norm_goal, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [arm64_norm, wp_norm, Reg.x21, hx21_3, *]
        · simp only [arm64_norm, wp_norm, Reg.x25, hx25_3, *]
        · simp only [arm64_norm, wp_norm, Reg.x26, Reg.x1, hx26_3, *]
        · simp only [arm64_norm, wp_norm, Reg.x29, hx29_3, *]
        · simp only [arm64_norm, wp_norm, htr3, *]
        · simp only [arm64_norm, wp_norm, hvregs3, *]
    · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx21_4, hx23_4, hx24_4, hx25_4, hx26_4, hx29_4, htr4, hvregs4⟩
      exact hcont s4 hpc4 hrun4 hsp4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 htr4 hvregs4

theorem pts_elem_even_step_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext)
    (j : Nat) (bs : List (BitVec 8))
    (s0 s : State) (fsp ptsPtr bsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (heven : bs.length % 2 = 0)
    (hmax : bs.length < 2 ^ 62)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 2#64)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j)
    (hx25 : s.readReg64 .x25 = ptsPtr)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm,
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 476#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) →
      sm.readReg64 .x21 = 2#64 →
      sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = BitVec.ofNat 64 j →
      sm.readReg64 .x25 = ptsPtr →
      sm.readReg64 .x26 = s.readReg64 .x1 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          (∃∗ cap, ∃∗ outPtr,
            ((fsp + 456#64) ↦₆₄ cap) ∗
            ((fsp + 464#64) ↦₆₄ outPtr) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
            vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        cells (fsp + 456#64) 3 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  cases bs with
  | nil =>
    have hempty := pts_elem_even_empty_step (A := A) (b := b) (ext := ext)
      j s fsp ptsPtr hfsp_align
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        (bsPtr ↦ₛ []) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc hrun hsp hx21 hx23 hx24 hx25
    refine SepWPp.weaken_pre
      (by dsimp only [ List.length_nil, BitVec.ofNat_eq_ofNat ]; exact Entails.of_eq (by ac_rfl))
      (sepWPp_seq_clean hempty ?_)
    intro sm hpcm hrunm ⟨hspm, hx19m, hx21m, hx23m, hx24m, hx25m, hx26m, hx29m, htrm, hvregsm⟩
    refine SepWPp.weaken_pre
      (by dsimp only [ List.length_nil, BitVec.ofNat_eq_ofNat ]; exact Entails.of_eq (by ac_rfl))
      (hcont sm hpcm hrunm hspm hx19m hx21m hx23m hx24m hx25m hx26m hx29m (htrm.trans htrace) (hvregsm.trans hvregs))
  | cons b0 bs' =>
    have hlen_m : (b0 :: bs').length = 2 * ((b0 :: bs').length / 2 - 1 + 1) := by
      simp only [List.length_cons] at heven ⊢
      omega
    exact pts_elem_even_nonempty_step_4k hA j ((b0 :: bs').length / 2 - 1) (b0 :: bs')
      s0 s fsp ptsPtr bsPtr hfsp_align Frame R hlen_m hmax
      hpc hrun hsp hx21 hx23 hx24 hx25 htrace hvregs hcont

theorem pts_outer_loop_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext)
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (j : Nat) (acc : List (List GF16))
      (s : State) (Frame R : SepProp),
      rem ≠ [] →
      j + rem.length = 16 →
      acc.length = j →
      (∀ bs ∈ rem, bs.length < 2 ^ 62) →
      s.pc = (contractProg b ext).fnAddr encoderFromPbName + 260#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x21 = 2#64 →
      s.readReg64 .x23 = 24#64 →
      s.readReg64 .x24 = BitVec.ofNat 64 j →
      s.readReg64 .x25 = ptsPtr →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ sm (tail : List Point),
        decodePbPointsTotal rem = .ok tail →
        sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 1648#64 →
        sm.status = .Running →
        sm.sp = fsp →
        sm.readReg64 .x1 = s.readReg64 .x1 →
        sm.readReg64 .x29 = s.readReg64 .x29 →
        sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A (fsp + 480#64) (acc ++ tail.map Point.value) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) →
      (∀ sm (errPts : List (List GF16)),
        decodePbPointsTotal rem = .error .serializationInvalid →
        errPts.length = 16 →
        sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 1612#64 →
        sm.status = .Running →
        sm.sp = fsp →
        sm.readReg64 .x1 = s.readReg64 .x1 →
        sm.readReg64 .x29 = s.readReg64 .x29 →
        sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A (fsp + 480#64) errPts ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
        (vecGF16ListOf A (fsp + 480#64) acc ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) rem.length ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j)) rem ∗
          cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))
  | [], _, _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => (hne rfl).elim
  | bs :: rest, j, acc, s, Frame, R, _, hj_rem, hacc_len, hmax, hpc, hrun, hsp,
    hx21, hx23, hx24, hx25, htrace, hvregs, hcont_ok, hcont_err => by
    have hbs_max : bs.length < 2 ^ 62 := hmax bs List.mem_cons_self
    have hrest_max : ∀ bs' ∈ rest, bs'.length < 2 ^ 62 :=
      fun bs' hm => hmax bs' (List.mem_cons_of_mem _ hm)
    have hj_lt : j < 16 := by simp only [List.length_cons] at hj_rem; omega
    dsimp only [List.length_cons, emptySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat]
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_left (vecU8_open A (ptsPtr + BitVec.ofNat 64 (24 * j)) bs))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap
    apply SepWPp.exists_elim; intro bsPtr
    by_cases hodd_bool : (bs.length % 2 != 0) = true
    · have hodd : bs.length % 2 ≠ 0 := bne_iff_ne.mp hodd_bool
      have hdec_err : decodePbPointsTotal (bs :: rest) = .error .serializationInvalid := by
        simp [decodePbPointsTotal, hodd_bool]
      have hstep := pts_elem_odd_step (b := b) (ext := ext) j bs s fsp ptsPtr hfsp_align
        (vecGF16ListOf A (fsp + 480#64) acc ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ bs) ∗
          vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        hodd hbs_max hpc hrun hsp hx23 hx24 hx25
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hstep ?_)
      intro sm hpcm hrunm ⟨hspm, hx1m, hx29m, htrm, hvregsm⟩
      have herr_len : (acc ++ List.replicate (rest.length + 1) ([] : List GF16)).length = 16 := by
        simp only [List.length_cons] at hj_rem
        rw [List.length_append, List.length_replicate, hacc_len]
        omega
      refine SepWPp.weaken_pre ?_
        (hcont_err sm (acc ++ List.replicate (rest.length + 1) []) hdec_err herr_len
          hpcm hrunm hspm hx1m hx29m (htrm.trans htrace) (hvregsm.trans hvregs))
      have heq_pre :
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecGF16ListOf A (fsp + 480#64) acc ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ bs) ∗
          vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame =
          (vecGF16ListOf A (fsp + 480#64) acc ∗
           emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (rest.length + 1)) ∗
          (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
           ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           (bsPtr ↦ₛ bs) ∗
           vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame := by
        dsimp only [emptySlotsAt]
        ac_rfl
      rw [heq_pre]
      have hslots := emptySlotsAt_entails_vecGF16ListOf A (rest.length + 1)
        (fsp + 480#64 + BitVec.ofNat 64 (24 * j))
      have happ := vecGF16ListOf_append A acc (List.replicate (rest.length + 1) []) (fsp + 480#64)
      rw [hacc_len] at happ
      have hclose := vecU8_close A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
      dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]
      refine Entails.trans
        (sepConj_mono (Entails.trans (sepConj_mono_right hslots) (Entails.of_eq happ.symm))
          (sepConj_mono_left hclose))
        (Entails.of_eq (by ac_rfl))
    · have heven : bs.length % 2 = 0 := by
        simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd_bool
        exact hodd_bool
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (pts_elem_even_step_4k hA j bs s0 s fsp ptsPtr bsPtr hfsp_align
          (vecGF16ListOf A (fsp + 480#64) acc ∗
            emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
            vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            Frame)
          R heven hbs_max hpc hrun hsp hx21 hx23 hx24 hx25 htrace hvregs ?_)
      intro s1 hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1 htr1 hvregs1
      have hfin := pts_elem_finish_step (A := A) (b := b) (ext := ext) j hj_lt bs s1 fsp
        (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ptsPtr hfsp_align
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗
          vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          vecGF16ListOf A (fsp + 480#64) acc ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx24_1 hx25_1
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hfin ?_)
      intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx21_2, hx23_2, hx24_2, hx25_2, hx29_2, htr2, hvregs2⟩
      have hclose := vecU8_close A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
      have happ := vecGF16ListOf_append A acc [bytesToGF16ListTotal bs] (fsp + 480#64)
      rw [hacc_len] at happ
      have hsingle : vecGF16ListOf A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) [bytesToGF16ListTotal bs] =
          vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs) := by
        dsimp only [vecGF16ListOf, arrayAt]; simp only [sepConj_emp]
      rw [hsingle] at happ
      cases rest with
      | nil =>
        have hj15 : j = 15 := by simp only [List.length_cons, List.length_nil] at hj_rem; omega
        have hlt_false : ¬(j + 1 < 16) := by omega
        simp only [hlt_false, ↓reduceIte] at hpc2
        have hdec_ok : decodePbPointsTotal [bs] = .ok [{ value := bytesToGF16ListTotal bs }] := by
          simp [decodePbPointsTotal, hodd_bool]
        refine SepWPp.weaken_pre ?_
          (hcont_ok s2 [{ value := bytesToGF16ListTotal bs }] hdec_ok hpc2 hrun2 hsp2
            (hx1_2.trans hx26_1) (hx29_2.trans hx29_1) (htr2.trans htr1) (hvregs2.trans hvregs1))
        dsimp only [List.map, List.length_nil, emptySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat]
        simp only [sepConj_emp]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (vecGF16ListOf A (fsp + 480#64) acc ∗
             vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
             ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             (bsPtr ↦ₛ bs) ∗
             vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
            cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame by ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
          (Entails.of_eq (by ac_rfl))
      | cons bs' rest' =>
        have hlt_true : j + 1 < 16 := by simp only [List.length_cons] at hj_rem; omega
        simp only [hlt_true, ↓reduceIte] at hpc2
        have hj_addr1 : fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64 =
            fsp + 480#64 + BitVec.ofNat 64 (24 * (j + 1)) := by
          rw [bv_add_lit_add_lit]; rfl
        have hj_addr2 : ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64 =
            ptsPtr + BitVec.ofNat 64 (24 * (j + 1)) := by
          rw [bv_add_lit_add_lit]; rfl
        refine SepWPp.weaken_pre ?_
          (pts_outer_loop_4k hA s0 fsp ptsPtr hfsp_align (bs' :: rest') (j + 1)
            (acc ++ [bytesToGF16ListTotal bs]) s2
            (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * j)) bs ∗ Frame) R
            (List.cons_ne_nil _ _)
            (by simp only [List.length_cons] at hj_rem ⊢; omega)
            (by rw [List.length_append, hacc_len]; rfl)
            hrest_max hpc2 hrun2 hsp2 hx21_2 hx23_2 hx24_2 hx25_2 (htr2.trans htr1) (hvregs2.trans hvregs1)
            (fun sm tail hdec_tail hpcm hrunm hspm hx1m hx29m htrm hvregsm => ?_)
            (fun sm errPts hdec_err herr_len hpcm hrunm hspm hx1m hx29m htrm hvregsm => ?_))
        · rw [← hj_addr1, ← hj_addr2]
          refine Entails.trans
            (Entails.of_eq (show _ =
              (vecGF16ListOf A (fsp + 480#64) acc ∗
               vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
              (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
               ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
               (bsPtr ↦ₛ bs) ∗
               vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
              emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) (bs' :: rest').length ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) (bs' :: rest') ∗
              cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame by ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
            (Entails.of_eq (by ac_rfl))
        · have hdec_cons : decodePbPointsTotal (bs :: bs' :: rest') =
              .ok ({ value := bytesToGF16ListTotal bs } :: tail) := by
            change (if bs.length % 2 != 0 then Except.error PolynomialError.serializationInvalid
              else match decodePbPointsTotal (bs' :: rest') with
              | Except.error e => Except.error e
              | Except.ok tail => Except.ok ({ value := bytesToGF16ListTotal bs } :: tail)) = _
            simp only [hodd_bool, Bool.false_eq_true, ↓reduceIte, hdec_tail]
          have happ_assoc : (acc ++ [bytesToGF16ListTotal bs]) ++ tail.map Point.value =
              acc ++ ({ value := bytesToGF16ListTotal bs } :: tail).map Point.value := by
            simp [List.append_assoc]
          rw [happ_assoc, ← hj_addr2]
          refine SepWPp.weaken_pre
            (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl))
            (hcont_ok sm ({ value := bytesToGF16ListTotal bs } :: tail) hdec_cons
              hpcm hrunm hspm (hx1m.trans (hx1_2.trans hx26_1))
              (hx29m.trans (hx29_2.trans hx29_1)) htrm hvregsm)
        · have hdec_cons : decodePbPointsTotal (bs :: bs' :: rest') = .error .serializationInvalid := by
            change (if bs.length % 2 != 0 then Except.error PolynomialError.serializationInvalid
              else match decodePbPointsTotal (bs' :: rest') with
              | Except.error e => Except.error e
              | Except.ok tail => Except.ok ({ value := bytesToGF16ListTotal bs } :: tail)) = _
            simp only [hodd_bool, Bool.false_eq_true, ↓reduceIte, hdec_err]
          rw [← hj_addr2]
          refine SepWPp.weaken_pre
            (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl))
            (hcont_err sm errPts hdec_cons herr_len
              hpcm hrunm hspm (hx1m.trans (hx1_2.trans hx26_1))
              (hx29m.trans (hx29_2.trans hx29_1)) htrm hvregsm)

/-! ## `.polys` Initial Buffer Allocations 0..11 (`+556 -> +848`) -/

local macro "polys_alloc_call" mid:term : tactic => `(tactic| (
  apply SepWPp.of_sepWP (mid := $mid)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
))

local macro "polys_oom_exit" hoom:ident hpanic:ident : tactic => `(tactic| (
  conv => arg 4; simp only [$hoom:ident, ↓reduceIte, sepConj_assoc]
  apply sepWPp_pure_mid; intro _
  refine $hpanic:ident _ _ ?_
  wp_steps
  exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, *])
))

theorem polys_alloc_0_3_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 556#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p0 p1 p2 p3 : BitVec 64),
      p0 ≠ 0#64 → p1 ≠ 0#64 → p2 ≠ 0#64 → p3 ≠ 0#64 →
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 656#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x20 = p0 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
          ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
          A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
          A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells (fsp + 32#64) 5 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk 2 2 := ⟨by omega, hpow2, by omega⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
  have hpanic1696 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_1696 b ext Q s0 s P R
  have hc5 : cells (fsp + 32#64) 5 =
      ∃∗ c0, ∃∗ c1, ∃∗ c2, ∃∗ c3, ∃∗ c4,
        ((fsp + 32#64) ↦₆₄ c0) ∗ ((fsp + 40#64) ↦₆₄ c1) ∗ ((fsp + 48#64) ↦₆₄ c2) ∗
        ((fsp + 56#64) ↦₆₄ c3) ∗ ((fsp + 64#64) ↦₆₄ c4) := by
    have h1 : fsp + 32#64 + 8#64 = fsp + 40#64 := by bv_omega
    have h2 : fsp + 40#64 + 8#64 = fsp + 48#64 := by bv_omega
    have h3 : fsp + 48#64 + 8#64 = fsp + 56#64 := by bv_omega
    have h4 : fsp + 56#64 + 8#64 = fsp + 64#64 := by bv_omega
    rw [ProofLib.cells_succ, h1, ProofLib.cells_succ, h2, ProofLib.cells_succ, h3,
        ProofLib.cells_succ, h4, ProofLib.cells_succ, ProofLib.cells_zero]
    simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]
  rw [hc5]; simp only [sepExists_sepConj_left, sepConj_assoc]
  iterate 5 (apply SepWPp.exists_elim; intro _)
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 556 104
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1696 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  polys_alloc_call (entry + 576#64)
  by_cases hoom0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · polys_oom_exit hoom0 hpanic1696
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr0⟩
    have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom0
    polys_alloc_call (entry + 600#64)
    by_cases hoom1 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · polys_oom_exit hoom1 hpanic1696
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr1⟩
      have hbeq1 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
      polys_alloc_call (entry + 624#64)
      by_cases hoom2 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · polys_oom_exit hoom2 hpanic1696
      · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr2⟩
        have hbeq2 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
        polys_alloc_call (entry + 648#64)
        by_cases hoom3 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · polys_oom_exit hoom3 hpanic1696
        · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr3⟩
          have hbeq3 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom3
          apply SepWPp.of_sepWP (mid := entry + 656#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.weaken_pre
            (by simp only [h_1, h_23, h_45, h_67, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3, hsp]; exact Entails.of_eq (by ac_rfl))
            (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
              (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
              hoom0 hoom1 hoom2 hoom3
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x20, *])
              (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]))

theorem polys_alloc_4_7_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 656#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p4 p5 p6 p7 : BitVec 64),
      p4 ≠ 0#64 → p5 ≠ 0#64 → p6 ≠ 0#64 → p7 ≠ 0#64 →
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 752#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x20 = s.readReg64 .x20 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
          A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
          A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 4 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk 2 2 := ⟨by omega, hpow2, by omega⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
  have hpanic1696 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_1696 b ext Q s0 s P R
  have hc4 : cells fsp 4 =
      ∃∗ c0, ∃∗ c1, ∃∗ c2, ∃∗ c3,
        (fsp ↦₆₄ c0) ∗ ((fsp + 8#64) ↦₆₄ c1) ∗ ((fsp + 16#64) ↦₆₄ c2) ∗ ((fsp + 24#64) ↦₆₄ c3) := by
    have h1 : fsp + 8#64 + 8#64 = fsp + 16#64 := by bv_omega
    have h2 : fsp + 16#64 + 8#64 = fsp + 24#64 := by bv_omega
    rw [ProofLib.cells_succ, ProofLib.cells_succ, h1, ProofLib.cells_succ, h2,
        ProofLib.cells_succ, ProofLib.cells_zero]
    simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]
  rw [hc4]; simp only [sepExists_sepConj_left, sepConj_assoc]
  iterate 4 (apply SepWPp.exists_elim; intro _)
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 656 100
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1696 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  polys_alloc_call (entry + 672#64)
  by_cases hoom4 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · polys_oom_exit hoom4 hpanic1696
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr4⟩
    have hbeq4 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom4
    polys_alloc_call (entry + 696#64)
    by_cases hoom5 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · polys_oom_exit hoom5 hpanic1696
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr5⟩
      have hbeq5 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom5
      polys_alloc_call (entry + 720#64)
      by_cases hoom6 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · polys_oom_exit hoom6 hpanic1696
      · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr6⟩
        have hbeq6 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom6
        polys_alloc_call (entry + 744#64)
        by_cases hoom7 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · polys_oom_exit hoom7 hpanic1696
        · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr7⟩
          have hbeq7 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom7
          apply SepWPp.of_sepWP (mid := entry + 752#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.weaken_pre
            (by simp only [h_1, h_23, h_45, h_67, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3, hsp]; exact Entails.of_eq (by ac_rfl))
            (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
              (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
              hoom4 hoom5 hoom6 hoom7
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x20, *])
              (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]))

theorem polys_alloc_8_11_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 752#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p8 p9 p10 p11 : BitVec 64),
      p8 ≠ 0#64 → p9 ≠ 0#64 → p10 ≠ 0#64 → p11 ≠ 0#64 →
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 848#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x19 = p8 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = p9 → sm.readReg64 .x23 = p10 →
      sm.readReg64 .x24 = p11 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
          A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk 2 2 := ⟨by omega, hpow2, by omega⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
  have hpanic1696 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_1696 b ext Q s0 s P R
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 752 100
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1696 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  polys_alloc_call (entry + 768#64)
  by_cases hoom8 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · polys_oom_exit hoom8 hpanic1696
  · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr8⟩
    have hbeq8 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom8
    polys_alloc_call (entry + 792#64)
    by_cases hoom9 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · polys_oom_exit hoom9 hpanic1696
    · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr9⟩
      have hbeq9 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom9
      polys_alloc_call (entry + 816#64)
      by_cases hoom10 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · polys_oom_exit hoom10 hpanic1696
      · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr10⟩
        have hbeq10 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom10
        polys_alloc_call (entry + 840#64)
        by_cases hoom11 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · polys_oom_exit hoom11 hpanic1696
        · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr11⟩
          have hbeq11 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom11
          apply SepWPp.of_sepWP (mid := entry + 848#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.weaken_pre
            (by simp only [h_1, h_23, h_45, h_67, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3, hsp]; exact Entails.of_eq (by ac_rfl))
            (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
              (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
              hoom8 hoom9 hoom10 hoom11
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x19, *])
              (by simp only [arm64_norm, wp_norm, Reg.x20, *]) (by simp only [arm64_norm, wp_norm, Reg.x21, *])
              (by simp only [arm64_norm, wp_norm, Reg.x23, *]) (by simp only [arm64_norm, wp_norm, Reg.x24, *])
              (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]))

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
