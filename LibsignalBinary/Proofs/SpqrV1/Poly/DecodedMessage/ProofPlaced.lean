/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpilogue
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.LoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof -- shake: keep

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Relocatable Top-Level Proof

Relocatable `[LibsignalPlacement]` proof of `polyDecoderDecodedMessage_placed_ok` on Block `418`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareName lagrangePrepare_fnOff LagrangePrepareArgs lagrangePrepareSpec lagrangePreparePlacedSpec lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack lagrangePrepare_ok polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompleteName lagrangeComplete_fnOff LagrangeCompleteArgs lagrangeCompleteSpec lagrangeCompletePlacedSpec lagrangeCompletePure lagrangeCompletePure_length lagrangeCompleteStack lagrangeComplete_ok lagrangeComplete_placed_ok)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt reduceTablePlacedAt)
open CryptoVerification.SpqrV1.GF.Mul2U16

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local wp_norm ↓, local arm64_norm ↓] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Initialization of `polys: [Option<Poly>; 16]` (`+352..+424`) -/

def rawOptPolySlots (base : BitVec 64) : Nat → SepProp
  | 0 => emp
  | n + 1 => ((∃∗ w : BitVec 64, base ↦₆₄ w) ∗ memRegion (base + 8#64) 16) ∗ rawOptPolySlots (base + 24#64) n

theorem memRegion_entails_rawOptPolySlots :
    ∀ (n : Nat) (base : BitVec 64), 24 * n < 2 ^ 64 → memRegion base (24 * n) ⊢ rawOptPolySlots base n
  | 0, base, _ => by simp [rawOptPolySlots, memRegion_zero]; exact Entails.refl _
  | n + 1, base, hbound => by
    change memRegion base (24 * (n + 1)) ⊢
      ((∃∗ w : BitVec 64, base ↦₆₄ w) ∗ memRegion (base + 8#64) 16) ∗ rawOptPolySlots (base + 24#64) n
    rw [show 24 * (n + 1) = 8 + (16 + 24 * n) by omega,
      memRegion_split base 8 (16 + 24 * n) (by omega), memRegion_split (base + 8#64) 16 (24 * n) (by omega),
      ProofLib.memRegion_eight base, BitVec.add_assoc, show (8#64 : BitVec 64) + 16#64 = 24#64 from rfl, ← sepConj_assoc]
    exact sepConj_mono_right (memRegion_entails_rawOptPolySlots n (base + 24#64) (by omega))

/-- Symbolic execution of `entry + 352#64` to `entry + 424#64` (18 instructions, `[LibsignalPlacement]`). -/
theorem initOptPolyCache_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 w648 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 352#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 424#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x24 = w648 → sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 648#64) ↦₆₄ w648) ∗ optPolyCacheListAt A (sp0 - 600#64) (List.replicate 16 none) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (((sp0 - 648#64) ↦₆₄ w648) ∗ memRegion (sp0 - 600#64) 384 ∗ P) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  have hsp_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp672_aligned sp0 hsp0
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (memRegion_entails_rawOptPolySlots 16 (sp0 - 600#64) (by decide)))) ?_
  dsimp only [rawOptPolySlots]
  simp only [wp_norm, arm64_norm, sepConj_emp, sepConj_assoc]
  wp_pull_exists
  wp_steps 18
  refine SepWP.weaken_pre
    (show _ ⊢ ((sp0 - 648#64) ↦₆₄ w648) ∗ optPolyCacheListAt A (sp0 - 600#64) (List.replicate 16 none) ∗ P by
      dsimp only [List.replicate, optPolyCacheListAt, arrayAt, optPolyCacheSlotAt, vecHeaderBytes, noneCap]
      simp only [wp_norm, arm64_norm, sepConj_emp, sepConj_assoc]
      exact Entails.of_eq (by ac_rfl))
    (hcont _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
      (by simpa [wp_norm, arm64_norm] using hsp) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))

/-! ## Output Buffer Allocation (`+424..+516`) -/

@[local wp_norm, local arm64_norm]
theorem bv64_lsl1_norm_proof (n : Nat) : (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 (2 * n) :=
  bv64_lsl1_norm n

theorem bv64_ne0_of_pos_le {n : Nat} (hge : 1 ≤ n) (hle : n ≤ 2 * (16 * 65536)) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change n = 0 at h1; omega

/-- Zero-length output path (`dec.ptsNeeded = 0`) from `entry + 424#64` to `entry + 1460#64` (`[LibsignalPlacement]`). -/
theorem allocOut_zero_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 : BitVec 64) (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 424#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hx24 : s.readReg64 .x24 = 0#64) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 1460#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 1#64) ∗ ((sp0 - 200#64) ↦₆₄ 0#64) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s (memRegion (sp0 - 216#64) 24 ∗ P) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  rw [memRegion24_eq_exists_three (sp0 - 216#64)]
  wp_conv_pre => simp only [wp_norm, arm64_norm, sepConj_assoc]
  wp_pull_exists
  wp_steps 8
  exact hcont _ rfl (by simp [wp_norm, arm64_norm, hstat])
    (by simpa [wp_norm, arm64_norm] using hsp) rfl (by simpa [wp_norm, arm64_norm] using hx29)

/-- Post-allocation setup (`+488..+548`, 8 instructions, `[LibsignalPlacement]`). -/
theorem allocOut_pos_setup_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 out_ptr : BitVec 64) (ptsNeeded : Nat) (hge1 : 1 ≤ ptsNeeded) (hle : ptsNeeded ≤ 16 * 65536)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 488#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (hx0 : s.readReg64 .x0 = out_ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (2 * ptsNeeded))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 548#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = 0#64 → sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ 0#64) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s (memRegion (sp0 - 216#64) 24 ∗ P) post := by
  have hne0_pts : (BitVec.ofNat 64 ptsNeeded == 0#64) = false := bv64_ne0_of_pos_le hge1 (by omega)
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  rw [memRegion24_eq_exists_three (sp0 - 216#64)]
  wp_conv_pre => simp only [wp_norm, arm64_norm, sepConj_assoc]
  wp_pull_exists
  wp_steps 8
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _ rfl (by simp [wp_norm, arm64_norm, hstat]) (by simpa [wp_norm, arm64_norm] using hsp) rfl
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using hx24)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hsp]) (by simpa [wp_norm, arm64_norm] using hx29))

/-- Positive-length output path (`1 ≤ ptsNeeded ≤ 16 * 65536`) from `entry + 424#64` to `entry + 548#64` (`[LibsignalPlacement]`). -/
theorem allocOut_pos_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (ptsNeeded : Nat) (hge1 : 1 ≤ ptsNeeded) (hle : ptsNeeded ≤ 16 * 65536)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 424#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (out_ptr : BitVec 64) (sf : State),
      out_ptr ≠ 0#64 → sf.pc = (blkPl_418).base + 548#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = 0#64 → sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ 0#64) ∗ A.live out_ptr (2 * ptsNeeded) 1 ∗
          (out_ptr ↦ₛ ([] : List (BitVec 8))) ∗ memRegion out_ptr (2 * ptsNeeded) ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (memRegion (sp0 - 216#64) 24 ∗ A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem halloc_sat
  have hpan_err :
      ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)).externAt? (lsρ spqrHandleErrorSym) =
        some Rust.panicked :=
    (SpqrV1.Alloc.spqr_externAt?_of_mem).trans h_panic
  have hne0_pts : (BitVec.ofNat 64 ptsNeeded == 0#64) = false := bv64_ne0_of_pos_le hge1 (by omega)
  have hne0_2pts : (BitVec.ofNat 64 (2 * ptsNeeded) == 0#64) = false := bv64_ne0_of_pos_le (by omega) (by omega)
  have htoNat_2pts : (BitVec.ofNat 64 (2 * ptsNeeded)).toNat = 2 * ptsNeeded := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow1 : ∃ m, 1 = 2 ^ m := ⟨0, rfl⟩
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by unfold State.spAligned; rw [hsp, sp672_aligned sp0 hsp0]; rfl
  try dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hpan_err hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 476#64)
  wp_steps 5
  wp_call hshim
  wp_steps 4
  wp_call halloc
  apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
  by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · have hcbnz : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = false := by simp [hptr0]
    wp_conv_pre => rw [alloc_post_pos' hptr0]
    apply SepWPp.pure_left; intro htr_fail
    apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
    wp_steps 5
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have htr_panic_eq :
        (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5)
          (BitVec.ofNat 64 (2 * ptsNeeded))).writeReg64 (Reg.gpr 30#5)
          ((blkPl_418).base + 452#64)).setPC (lsρ spqrHandleErrorSym))).trace = s0.trace ++ [allocFailedEvent] := by
      change sf_1.trace = s0.trace ++ [allocFailedEvent]; rw [htr_fail, h, htr_tr]
    refine SepWPp.panic (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hpan_err)
      (fun hm => allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _)
        ⟨allocFailedIn_of_trace_eq' htr_panic_eq,
          by rw [htr_panic_eq]; exact List.prefix_append s0.trace [allocFailedEvent]⟩ hm)
  · have hcbnz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
    wp_conv_pre => rw [alloc_post_neg' hptr0]
    apply SepWPp.pure_left; rintro ⟨_hptr_mod, htr_ok⟩
    apply SepWPp.of_sepWP (mid := (blkPl_418).base + 488#64)
    wp_steps 1
    apply SepWP.done (by simp [wp_norm, arm64_norm, hcbnz]) (by simp [wp_norm, arm64_norm, hrun_sf_1])
    rw [h_1, hsp]
    apply SepWPp.of_sepWP (mid := (blkPl_418).base + 548#64)
    refine SepWP.weaken_pre
      (show _ ⊢
        memRegion (sp0 - 216#64) 24 ∗
          (A.live (sf_1.readReg64 (Reg.gpr 0#5)) (2 * ptsNeeded) 1 ∗
            ((sf_1.readReg64 (Reg.gpr 0#5)) ↦ₛ ([] : List (BitVec 8))) ∗
            memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * ptsNeeded) ∗
            A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F) by
        simp only [pointsToBytes_nil, sepConj_emp]; exact Entails.of_eq (by ac_rfl))
      (allocOut_pos_setup_placed_sepWP (ext := ext) sp0 (sf_1.readReg64 (Reg.gpr 0#5)) ptsNeeded hge1 hle _ _ _
        (by rfl)
        (by simp [wp_norm, arm64_norm, hrun_sf_1]) (by simp [wp_norm, arm64_norm, hsp_sf, h_1, hsp])
        (by simp [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]; rw [h_14, h_4])
        (by simp only [wp_norm, arm64_norm]; rw [h_17, h_7]; exact hx24)
        (by simp [wp_norm, arm64_norm, *])
        (fun sf_2 hpc2 hstat2 hsp2 htr2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_))
    apply SepWP.done hpc2 hstat2
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext (sf_1.readReg64 (Reg.gpr 0#5)) sf_2 hptr0 hpc2 hstat2 hsp2
        (by rw [htr2]; simp [traceVRegs, wp_norm, arm64_norm, *])
        (by rw [hx20_2]; simp only [wp_norm, arm64_norm]; rw [h_13, h_3])
        hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2)

/-! ## Pure Bridge Lemmas and Post-`collectPointsVecs` Execution (`+352` to Return) -/

theorem collectPointsVecs_false_bounds (dec : PolyDecoder) (hpts_len : dec.pts.length = 16)
    (hsort : PolyDecoderStrictSorted dec) (hret : (collectPointsVecsTotal dec 0 16 false []).1 = false) :
    (∀ k (hk : k < 16), dec.necessaryPoints k ≤ (dec.pts[k]'(by omega)).len) ∧ dec.ptsNeeded ≤ 16 * 65536 := by
  have hpv_info := collectPointsVecsTotal_of_fst_false dec 16 0 false [] hret
  have hge_len : ∀ k (hk : k < 16), dec.necessaryPoints k ≤ (dec.pts[k]'(by omega)).len := by
    intro k hk; have hk_pts : k < dec.pts.length := by omega
    have h1 := hpv_info.2.2 k (by omega) (by omega)
    rw [List.getElem?_eq_getElem hk_pts, Option.getD_some] at h1; exact h1
  have hnec0 : dec.necessaryPoints 0 ≤ 65536 := by
    have h1 := hge_len 0 (by decide)
    have h2 := polyDecoderStrictSorted_elem_length_le hsort (by omega : 0 < dec.pts.length)
    unfold SortedSetPt.len at h1; omega
  exact ⟨hge_len, ptsNeeded_le_of_necessaryPoints_zero_le dec hnec0⟩

theorem exists_lt_necessaryPoints_of_collect_true (dec : PolyDecoder) (hpts : dec.pts.length = 16)
    (htrue : (collectPointsVecsTotal dec 0 16 false []).1 = true) :
    ∃ k, 0 ≤ k ∧ ∃ hk : k < 16, (dec.pts[k]'(by rw [hpts]; exact hk)).len < dec.necessaryPoints k := by
  by_contra hnot
  have hall : ∀ k (hk : k < 16), 0 ≤ k → dec.necessaryPoints k ≤ (dec.pts[k]'(by rw [hpts]; exact hk)).len :=
    fun k hk h0 => Nat.le_of_not_lt (fun hlt => hnot ⟨k, h0, hk, hlt⟩)
  have hfalse := collectPointsVecsTotal_fst_false_of_all_ge dec hpts 16 0 [] (by decide) hall
  rw [hfalse] at htrue; contradiction

theorem decodedMessageLoopTotal_fst_length (dec : PolyDecoder) (pv : List (List Pt)) :
    ∀ (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)),
      polys.length = 16 → (decodedMessageLoopTotal dec pv i rem polys out).1.length = 16
  | 0, _, polys, _, hlen => by simp [decodedMessageLoopTotal, hlen]
  | rem + 1, i, polys, out, hlen => by
    unfold decodedMessageLoopTotal; dsimp only
    apply decodedMessageLoopTotal_fst_length dec pv rem (i + 1)
    split
    · exact hlen
    · split
      · exact hlen
      · simp [List.length_set, hlen]

theorem decodedMessageLoopTotal_snd_length (dec : PolyDecoder) (pv : List (List Pt)) :
    ∀ (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)),
      (decodedMessageLoopTotal dec pv i rem polys out).2.length = out.length + 2 * rem
  | 0, _, _, out => by simp [decodedMessageLoopTotal]
  | rem + 1, i, polys, out => by
    unfold decodedMessageLoopTotal; dsimp only
    rw [decodedMessageLoopTotal_snd_length dec pv rem (i + 1)]; simp [u16ToBeBytes]; omega

theorem decodedMessageTotal_of_isComplete_true {dec : PolyDecoder} (h : dec.isComplete = true) :
    decodedMessageTotal dec = none := by unfold decodedMessageTotal; simp [h]

theorem decodedMessageTotal_of_collect_true {dec : PolyDecoder}
    (hcomp : dec.isComplete = false) (hpts : dec.pts.length = 16)
    (hret : (collectPointsVecsTotal dec 0 16 false []).1 = true) :
    decodedMessageTotal dec = none := by unfold decodedMessageTotal; rw [hpts]; simp [hcomp, hret]

theorem decodedMessageTotal_of_ptsNeeded_zero {dec : PolyDecoder}
    (hcomp : dec.isComplete = false) (hpts : dec.pts.length = 16)
    (hret : (collectPointsVecsTotal dec 0 16 false []).1 = false) (hzero : dec.ptsNeeded = 0) :
    decodedMessageTotal dec = some [] := by
  unfold decodedMessageTotal; rw [hpts, hzero]
  cases hcp : collectPointsVecsTotal dec 0 16 false [] with
  | mk r pv =>
    have hr : r = false := by simpa [hcp] using hret
    subst hr; simp [hcomp, decodedMessageLoopTotal]

theorem decodedMessageTotal_of_collect_false {dec : PolyDecoder}
    (hcomp : dec.isComplete = false) (hpts : dec.pts.length = 16)
    (hret : (collectPointsVecsTotal dec 0 16 false []).1 = false) :
    decodedMessageTotal dec =
      some (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2 := by
  unfold decodedMessageTotal; rw [hpts]
  have hsnd := collectPointsVecsTotal_snd_eq_collectedSlices dec 16 0 [] hret
  rw [List.nil_append] at hsnd
  cases hcp : collectPointsVecsTotal dec 0 16 false [] with
  | mk r pv =>
    have hr : r = false := by simpa [hcp] using hret
    have hpv : pv = collectedSlices dec 0 16 := by simpa [hcp] using hsnd
    subst hr hpv; simp [hcomp]

theorem ptSliceRefListAt_entails_memRegion256 (dec : PolyDecoder) (pv_ptr : BitVec 64)
    (pins : List VecPin) (hpins : pins.length = 16) :
    ptSliceRefListAt dec 0 pv_ptr pins ⊢ memRegion pv_ptr 256 := by
  simpa [hpins] using ptSliceRefListAt_entails_memRegion dec pins 0 pv_ptr (by rw [hpins]; decide)

theorem memRegion_24_8_8_8_entails_48 (sp0 w648 w632 : BitVec 64) :
    memRegion (sp0 - 672#64) 24 ∗ ((sp0 - 648#64) ↦₆₄ w648) ∗
      memRegion (sp0 - 640#64) 8 ∗ ((sp0 - 632#64) ↦₆₄ w632) ⊢ memRegion (sp0 - 672#64) 48 := by
  have h1 : sp0 - 672#64 + 24#64 = sp0 - 648#64 := by bv_omega
  have h2 : sp0 - 648#64 + 8#64 = sp0 - 640#64 := by bv_omega
  have h3 : sp0 - 640#64 + 8#64 = sp0 - 632#64 := by bv_omega
  rw [show (48 : Nat) = 24 + (8 + (8 + 8)) from rfl,
    memRegion_split (sp0 - 672#64) 24 24 (by decide), h1,
    memRegion_split (sp0 - 648#64) 8 16 (by decide), h2,
    memRegion_split (sp0 - 640#64) 8 8 (by decide), h3]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion8 (sp0 - 648#64) w648)
      (sepConj_mono_right (pointsTo64_entails_memRegion8 (sp0 - 632#64) w632)))

theorem interpolateScratchAt_entails_regions (sp0 : BitVec 64) :
    interpolateScratchAt sp0 ⊢
      memRegion (sp0 - 664#64) 16 ∗ memRegion (sp0 - 640#64) 8 ∗ memRegion (sp0 - 192#64) 72 := by
  unfold interpolateScratchAt
  apply Entails.sepExists_elim; intro v664; apply Entails.sepExists_elim; intro v656
  apply Entails.sepExists_elim; intro v640; apply Entails.sepExists_elim; intro v192
  apply Entails.sepExists_elim; intro v184; apply Entails.sepExists_elim; intro v176
  apply Entails.sepExists_elim; intro v168; apply Entails.sepExists_elim; intro v160
  apply Entails.sepExists_elim; intro v152
  have ha0 : sp0 - 664#64 + 8#64 = sp0 - 656#64 := by bv_omega
  have h1 : sp0 - 192#64 + 8#64 = sp0 - 184#64 := by bv_omega
  have h2 : sp0 - 184#64 + 8#64 = sp0 - 176#64 := by bv_omega
  have h3 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := by bv_omega
  have h4 : sp0 - 168#64 + 8#64 = sp0 - 160#64 := by bv_omega
  have h5 : sp0 - 160#64 + 8#64 = sp0 - 152#64 := by bv_omega
  have h6 : sp0 - 152#64 + 8#64 = sp0 - 144#64 := by bv_omega
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split (sp0 - 664#64) 8 8 (by decide), ha0,
    show (72 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + 24))))) from rfl,
    memRegion_split (sp0 - 192#64) 8 64 (by decide), h1, memRegion_split (sp0 - 184#64) 8 56 (by decide), h2,
    memRegion_split (sp0 - 176#64) 8 48 (by decide), h3, memRegion_split (sp0 - 168#64) 8 40 (by decide), h4,
    memRegion_split (sp0 - 160#64) 8 32 (by decide), h5, memRegion_split (sp0 - 152#64) 8 24 (by decide), h6]
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656)) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
    (((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
      ((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
      memRegion (sp0 - 144#64) 24) by ac_rfl)) ?_
  refine sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion8 _ _) (pointsTo64_entails_memRegion8 _ _)) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion8 _ _) (sepConj_mono (pointsTo64_entails_memRegion8 _ _) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion8 _ _) (sepConj_mono (pointsTo64_entails_memRegion8 _ _) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion8 _ _) (sepConj_mono (pointsTo64_entails_memRegion8 _ _) ?_)
  exact sepConj_mono_left (pointsTo64_entails_memRegion8 _ _)

theorem regions_entails_interpolateScratchAt (sp0 : BitVec 64) :
    memRegion (sp0 - 664#64) 16 ∗ memRegion (sp0 - 640#64) 8 ∗ memRegion (sp0 - 192#64) 72 ⊢
      interpolateScratchAt sp0 := by
  unfold interpolateScratchAt
  have ha0 : sp0 - 664#64 + 8#64 = sp0 - 656#64 := by bv_omega
  have h1 : sp0 - 192#64 + 8#64 = sp0 - 184#64 := by bv_omega
  have h2 : sp0 - 184#64 + 8#64 = sp0 - 176#64 := by bv_omega
  have h3 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := by bv_omega
  have h4 : sp0 - 168#64 + 8#64 = sp0 - 160#64 := by bv_omega
  have h5 : sp0 - 160#64 + 8#64 = sp0 - 152#64 := by bv_omega
  have h6 : sp0 - 152#64 + 8#64 = sp0 - 144#64 := by bv_omega
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split (sp0 - 664#64) 8 8 (by decide), ha0,
    show (72 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + 24))))) from rfl,
    memRegion_split (sp0 - 192#64) 8 64 (by decide), h1, memRegion_split (sp0 - 184#64) 8 56 (by decide), h2,
    memRegion_split (sp0 - 176#64) 8 48 (by decide), h3, memRegion_split (sp0 - 168#64) 8 40 (by decide), h4,
    memRegion_split (sp0 - 160#64) 8 32 (by decide), h5, memRegion_split (sp0 - 152#64) 8 24 (by decide), h6,
    ProofLib.memRegion_eight (sp0 - 664#64), ProofLib.memRegion_eight (sp0 - 656#64),
    ProofLib.memRegion_eight (sp0 - 640#64), ProofLib.memRegion_eight (sp0 - 192#64),
    ProofLib.memRegion_eight (sp0 - 184#64), ProofLib.memRegion_eight (sp0 - 176#64),
    ProofLib.memRegion_eight (sp0 - 168#64), ProofLib.memRegion_eight (sp0 - 160#64),
    ProofLib.memRegion_eight (sp0 - 152#64)]
  wp_pull_exists
  apply Entails.sepExists_elim; intro v152; apply Entails.sepExists_elim; intro v160
  apply Entails.sepExists_elim; intro v168; apply Entails.sepExists_elim; intro v176
  apply Entails.sepExists_elim; intro v184; apply Entails.sepExists_elim; intro v192
  apply Entails.sepExists_elim; intro v640; apply Entails.sepExists_elim; intro v656
  apply Entails.sepExists_elim; intro v664
  refine Entails.trans ?_ (Entails.sepExists_intro v664)
  refine Entails.trans ?_ (Entails.sepExists_intro v656)
  refine Entails.trans ?_ (Entails.sepExists_intro v640)
  refine Entails.trans ?_ (Entails.sepExists_intro v192)
  refine Entails.trans ?_ (Entails.sepExists_intro v184)
  refine Entails.trans ?_ (Entails.sepExists_intro v176)
  refine Entails.trans ?_ (Entails.sepExists_intro v168)
  refine Entails.trans ?_ (Entails.sepExists_intro v160)
  refine Entails.trans ?_ (Entails.sepExists_intro v152)
  exact Entails.of_eq (by ac_rfl)

theorem scratch_and_pads_entails_regions (sp0 : BitVec 64) :
    interpolateScratchAt sp0 ∗ memRegion (sp0 - 672#64) 8 ∗ memRegion (sp0 - 120#64) 24 ⊢
      memRegion (sp0 - 672#64) 24 ∗ memRegion (sp0 - 640#64) 8 ∗ memRegion (sp0 - 192#64) 96 := by
  refine Entails.trans (sepConj_mono_left (interpolateScratchAt_entails_regions sp0)) ?_
  have h1 : sp0 - 672#64 + 8#64 = sp0 - 664#64 := by bv_omega
  have h2 : sp0 - 192#64 + 72#64 = sp0 - 120#64 := by bv_omega
  rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split (sp0 - 672#64) 8 16 (by decide), h1,
    show (96 : Nat) = 72 + 24 from rfl, memRegion_split (sp0 - 192#64) 72 24 (by decide), h2]
  exact Entails.of_eq (by ac_rfl)

theorem regions_entails_scratch_and_pads (sp0 : BitVec 64) :
    memRegion (sp0 - 672#64) 24 ∗ memRegion (sp0 - 640#64) 8 ∗ memRegion (sp0 - 192#64) 96 ⊢
      interpolateScratchAt sp0 ∗ memRegion (sp0 - 672#64) 8 ∗ memRegion (sp0 - 120#64) 24 := by
  have h1 : sp0 - 672#64 + 8#64 = sp0 - 664#64 := by bv_omega
  have h2 : sp0 - 192#64 + 72#64 = sp0 - 120#64 := by bv_omega
  rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split (sp0 - 672#64) 8 16 (by decide), h1,
    show (96 : Nat) = 72 + 24 from rfl, memRegion_split (sp0 - 192#64) 72 24 (by decide), h2]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (sp0 - 664#64) 16 ∗ memRegion (sp0 - 640#64) 8 ∗ memRegion (sp0 - 192#64) 72) ∗
      (memRegion (sp0 - 672#64) 8 ∗ memRegion (sp0 - 120#64) 24) by ac_rfl)) ?_
  exact sepConj_mono_left (regions_entails_interpolateScratchAt sp0)

theorem memRegion_384_24_96_entails_504 (sp0 : BitVec 64) :
    memRegion (sp0 - 600#64) 384 ∗ memRegion (sp0 - 216#64) 24 ∗ memRegion (sp0 - 192#64) 96 ⊢
      memRegion (sp0 - 600#64) 504 := by
  have h1 : sp0 - 600#64 + 384#64 = sp0 - 216#64 := by bv_omega
  have h2 : sp0 - 216#64 + 24#64 = sp0 - 192#64 := by bv_omega
  rw [show (504 : Nat) = 384 + (24 + 96) from rfl,
    memRegion_split (sp0 - 600#64) 384 120 (by decide), h1,
    memRegion_split (sp0 - 216#64) 24 96 (by decide), h2]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_8_384_24_96_entails_512 (sp0 w608 : BitVec 64) :
    ((sp0 - 608#64) ↦₆₄ w608) ∗
      (memRegion (sp0 - 600#64) 384 ∗ memRegion (sp0 - 216#64) 24 ∗ memRegion (sp0 - 192#64) 96) ⊢
      memRegion (sp0 - 608#64) 512 :=
  Entails.trans (sepConj_mono_right (memRegion_384_24_96_entails_504 sp0)) (memRegion_8_504_entails_512 sp0 w608)

/-- Splits `memRegion (sp0 - 672#64) 576` into the stack slots used by `decoded_message`. -/
theorem memRegion576_split_for_decodedMessage (sp0 : BitVec 64) :
    memRegion (sp0 - 672#64) 576 ⊢
      (∃∗ w648 : BitVec 64, (sp0 - 648#64) ↦₆₄ w648) ∗ (∃∗ w632 : BitVec 64, (sp0 - 632#64) ↦₆₄ w632) ∗
        (∃∗ w624 : BitVec 64, (sp0 - 624#64) ↦₆₄ w624) ∗ (∃∗ w616 : BitVec 64, (sp0 - 616#64) ↦₆₄ w616) ∗
        (∃∗ w608 : BitVec 64, (sp0 - 608#64) ↦₆₄ w608) ∗ memRegion (sp0 - 600#64) 384 ∗
        memRegion (sp0 - 216#64) 24 ∗ interpolateScratchAt sp0 ∗
        memRegion (sp0 - 672#64) 8 ∗ memRegion (sp0 - 120#64) 24 := by
  have h1 : sp0 - 672#64 + 24#64 = sp0 - 648#64 := by bv_omega
  have h2 : sp0 - 648#64 + 8#64 = sp0 - 640#64 := by bv_omega
  have h3 : sp0 - 640#64 + 8#64 = sp0 - 632#64 := by bv_omega
  have h4 : sp0 - 632#64 + 8#64 = sp0 - 624#64 := by bv_omega
  have h5 : sp0 - 624#64 + 8#64 = sp0 - 616#64 := by bv_omega
  have h6 : sp0 - 616#64 + 8#64 = sp0 - 608#64 := by bv_omega
  have h7 : sp0 - 608#64 + 8#64 = sp0 - 600#64 := by bv_omega
  have h8 : sp0 - 600#64 + 384#64 = sp0 - 216#64 := by bv_omega
  have h9 : sp0 - 216#64 + 24#64 = sp0 - 192#64 := by bv_omega
  rw [show (576 : Nat) = 24 + (8 + (8 + (8 + (8 + (8 + (8 + (384 + (24 + 96)))))))) from rfl,
    memRegion_split (sp0 - 672#64) 24 _ (by decide), h1, memRegion_split (sp0 - 648#64) 8 _ (by decide), h2,
    memRegion_split (sp0 - 640#64) 8 _ (by decide), h3, memRegion_split (sp0 - 632#64) 8 _ (by decide), h4,
    memRegion_split (sp0 - 624#64) 8 _ (by decide), h5, memRegion_split (sp0 - 616#64) 8 _ (by decide), h6,
    memRegion_split (sp0 - 608#64) 8 _ (by decide), h7, memRegion_split (sp0 - 600#64) 384 _ (by decide), h8,
    memRegion_split (sp0 - 216#64) 24 96 (by decide), h9,
    ProofLib.memRegion_eight (sp0 - 648#64), ProofLib.memRegion_eight (sp0 - 632#64),
    ProofLib.memRegion_eight (sp0 - 624#64), ProofLib.memRegion_eight (sp0 - 616#64),
    ProofLib.memRegion_eight (sp0 - 608#64)]
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ w648 : BitVec 64, (sp0 - 648#64) ↦₆₄ w648) ∗ (∃∗ w632 : BitVec 64, (sp0 - 632#64) ↦₆₄ w632) ∗
      (∃∗ w624 : BitVec 64, (sp0 - 624#64) ↦₆₄ w624) ∗ (∃∗ w616 : BitVec 64, (sp0 - 616#64) ↦₆₄ w616) ∗
      (∃∗ w608 : BitVec 64, (sp0 - 608#64) ↦₆₄ w608) ∗ memRegion (sp0 - 600#64) 384 ∗
      memRegion (sp0 - 216#64) 24 ∗
      (memRegion (sp0 - 672#64) 24 ∗ memRegion (sp0 - 640#64) 8 ∗ memRegion (sp0 - 192#64) 96) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (regions_entails_scratch_and_pads sp0)))))))

/-- Helper (`[LibsignalPlacement]`): from `+1904` after `dropOptPolyCache_from1404_placed_sepWP` or `dropOptPolyCache_from1460_placed_sepWP`,
    collapses stack regions and `ptSliceRefListAt` and executes `decodedMessage_epilogue_from1904_placed_sepWP`. -/
theorem decodedMessage_finish_from1904_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (dec : PolyDecoder) (pins : List VecPin) (hpins : pins.length = 16)
    (s0 : State) (out_sret pv_ptr w648 : BitVec 64) (resOpt : Option (List (BitVec 8)))
    (hsp0 : s0.sp &&& 0xf#64 = 0#64) (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1904#64)
    (hstat : s.status = .Running) (hsp : s.sp = s0.sp - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp →
      traceVRegs sf = traceVRegs s → CalleeSavedGprsPreserved s0 sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (optVecU8Of A out_sret resOpt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (optVecU8Of A out_sret resOpt ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
        memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗ A.pool ∗
        stackAt (s0.sp - 672#64) allocHookStack ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12288 ∗
        savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ w648) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
        ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
        interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
        A.live pv_ptr 256 8 ∗ ptSliceRefListAt dec 0 pv_ptr pins ∗ P) post := by
  have hext :
      stackAt (s0.sp - 672#64) allocHookStack ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12288 =
        stackAt (s0.sp - 672#64) extHookStack :=
    (stackAt_extHook_eq_allocHook (s0.sp - 672#64)).symm
  refine SepWP.weaken_pre
    (show _ ⊢
      (interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24) ∗
      (ptSliceRefListAt dec 0 pv_ptr pins ∗ ((s0.sp - 648#64) ↦₆₄ w648) ∗
        ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
        memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
        (stackAt (s0.sp - 672#64) allocHookStack ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12288) ∗
        (((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ A.live pv_ptr 256 8 ∗
          savedRegsAt s0.sp s0 ∗ A.pool ∗ (optVecU8Of A out_sret resOpt ∗ P))) by exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWP.weaken_pre (sepConj_mono_left (scratch_and_pads_entails_regions s0.sp)) ?_
  refine SepWP.weaken_pre
    (show _ ⊢
      ptSliceRefListAt dec 0 pv_ptr pins ∗
        (memRegion (s0.sp - 672#64) 24 ∗ ((s0.sp - 648#64) ↦₆₄ w648) ∗
          memRegion (s0.sp - 640#64) 8 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret)) ∗
        (((s0.sp - 608#64) ↦₆₄ 16#64) ∗
          (memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗ memRegion (s0.sp - 192#64) 96)) ∗
        (((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ A.live pv_ptr 256 8 ∗
          savedRegsAt s0.sp s0 ∗ A.pool ∗
          (stackAt (s0.sp - 672#64) allocHookStack ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12288) ∗
          (optVecU8Of A out_sret resOpt ∗ P)) by exact Entails.of_eq (by ac_rfl)) ?_
  rw [hext]
  refine SepWP.weaken_pre
    (sepConj_mono (ptSliceRefListAt_entails_memRegion256 dec pv_ptr pins hpins)
      (sepConj_mono (memRegion_24_8_8_8_entails_48 s0.sp w648 out_sret)
        (sepConj_mono_left (memRegion_8_384_24_96_entails_512 s0.sp 16#64)))) ?_
  refine SepWP.weaken_pre
    (show _ ⊢
      ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗ memRegion (s0.sp - 672#64) 48 ∗ memRegion (s0.sp - 608#64) 512 ∗
        savedRegsAt s0.sp s0 ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
        (optVecU8Of A out_sret resOpt ∗ P) by exact Entails.of_eq (by ac_rfl))
    (decodedMessage_epilogue_from1904_placed_sepWP hdealloc_sat s0 s0.sp pv_ptr hsp0 s
      (optVecU8Of A out_sret resOpt ∗ P) post hpc hstat hsp
      (fun sf hpc_f hrun_f hsp_f htr_f hcs_f =>
        SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (hcont sf hpc_f hrun_f hsp_f htr_f hcs_f)))

/-- Execution from `entry + 352#64` to function return (`s0.readReg64 .x30`) when
    `dec.isComplete = false` and `(collectPointsVecsTotal dec 0 16 false []).1 = false` (`[LibsignalPlacement]`). -/
theorem decodedMessage_afterCollect_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (lagrangePreparePlacedSpec A))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) lagrangeCompletePlacedSpec)
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec A))
    (dec : PolyDecoder) (decA out_sret pv_ptr : BitVec 64) (pins : List VecPin)
    (hcomp_false : dec.isComplete = false) (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec) (hret : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (blkPl_418).base + 352#64)
    (hstat : s.status = .Running) (hsp : s.sp = s0.sp - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx20 : s.readReg64 .x20 = decA) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp →
      traceVRegs sf = traceVRegs s0 → CalleeSavedGprsPreserved s0 sf →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (optVecU8Of A out_sret (decodedMessageTotal dec) ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
        ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
        memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
        interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
        memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
        ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗ F) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have ⟨hall_ge, hneed_le⟩ := collectPointsVecs_false_bounds dec hpts hsort hret
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 424#64)
  refine SepWP.weaken_pre
    (show _ ⊢
      ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ memRegion (s0.sp - 600#64) 384 ∗
        (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
          ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
          memRegion (s0.sp - 216#64) 24 ∗ interpolateScratchAt s0.sp ∗
          memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
          memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
          ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗ F) by exact Entails.of_eq (by ac_rfl))
    (initOptPolyCache_placed_sepWP (ext := ext) (A := A) s0.sp (BitVec.ofNat 64 dec.ptsNeeded) hsp0 s _ _
      hpc hstat hsp (fun s1 hpc1 hrun1 hsp1 htr1 hx20_1 hx24_1 hx29_1 => ?_))
  apply SepWP.done hpc1 hrun1
  by_cases hneed0 : dec.ptsNeeded = 0
  · have hx24_0 : s1.readReg64 .x24 = 0#64 := by rw [hx24_1, hneed0]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
    refine SepWP.weaken_pre
      (show _ ⊢
        memRegion (s0.sp - 216#64) 24 ∗
          (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            optPolyCacheListAt A (s0.sp - 600#64) (List.replicate 16 none) ∗
            savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗
            ((s0.sp - 608#64) ↦₆₄ 16#64) ∗ interpolateScratchAt s0.sp ∗
            memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
            memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗ F) by exact Entails.of_eq (by ac_rfl))
      (allocOut_zero_placed_sepWP (ext := ext) s0.sp s1 _ _ hpc1 hrun1 hsp1 hx24_0 (by rw [hx29_1, hx29])
        (fun s2 hpc2 hrun2 hsp2 htr2 hx29_2 => ?_))
    rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64)]
    refine SepWP.weaken_pre
      (show _ ⊢
        optPolyCacheListAt A (s0.sp - 600#64) (List.replicate 16 none) ∗
          ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 216#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 208#64) ↦₆₄ 1#64) ∗ ((s0.sp - 200#64) ↦₆₄ 0#64) ∗
          memRegion out_sret vecHeaderBytes ∗ A.pool ∗ stackAt (s0.sp - 672#64) allocHookStack ∗
          (memRegion ((s0.sp - 672#64) - 16384#64) 12288 ∗ savedRegsAt s0.sp s0 ∗
            ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
            ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
            interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗
            (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F)) by exact Entails.of_eq (by ac_rfl))
      (dropOptPolyCache_from1460_placed_sepWP hdealloc_sat s0.sp out_sret hsp0 s2 _ _
        hpc2 hrun2 hsp2 hx29_2 (fun s3 hpc3 hrun3 hsp3 htr3 => ?_))
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (decodedMessage_finish_from1904_placed_sepWP hdealloc_sat dec pins hpins s0 out_sret pv_ptr
        (BitVec.ofNat 64 dec.ptsNeeded) (some []) hsp0 s3
        (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F) _
        hpc3 hrun3 hsp3 (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
    apply SepWP.done hpc_f hrun_f
    have htot := decodedMessageTotal_of_ptsNeeded_zero hcomp_false hpts hret hneed0
    refine SepWPp.weaken_pre
      (show _ ⊢
        optVecU8Of A out_sret (decodedMessageTotal dec) ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ F by
        rw [htot]; exact Entails.of_eq (by ac_rfl))
      (hnext sf hpc_f hrun_f hsp_f (by rw [htr_f, htr3, htr2, htr1, htr]) hcs_f)
  · have hge1 : 1 ≤ dec.ptsNeeded := Nat.pos_of_ne_zero hneed0
    rw [stackAt_extHook_eq_computeAt (s0.sp - 672#64), stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
    refine SepWPp.weaken_pre
      (show _ ⊢
        memRegion (s0.sp - 216#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 672#64) allocHookStack ∗
          (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            optPolyCacheListAt A (s0.sp - 600#64) (List.replicate 16 none) ∗
            savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗
            ((s0.sp - 608#64) ↦₆₄ 16#64) ∗ interpolateScratchAt s0.sp ∗
            memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
            memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ memRegion ((s0.sp - 672#64) - 4352#64) 256 ∗
            memRegion ((s0.sp - 672#64) - 16384#64) 12032 ∗ F) by exact Entails.of_eq (by ac_rfl))
      (allocOut_pos_placed_wpp h_panic hshim_sat halloc_sat s0.sp hsp0 dec.ptsNeeded hge1 hneed_le s0 s1 _ R Q
        hpc1 hrun1 hsp1 (by rw [htr1, htr]) hx24_1 (by rw [hx29_1, hx29])
        (fun out_ptr s2 hout_ne0 hpc2 hrun2 hsp2 htr2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_))
    refine SepWPp.weaken_pre
      (show _ ⊢
        optPolyCacheListAt A (s0.sp - 600#64) (List.replicate 16 none) ∗
          ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
          ((s0.sp - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((s0.sp - 208#64) ↦₆₄ out_ptr) ∗ ((s0.sp - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * 0)) ∗
          ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          (out_ptr ↦ₛ ([] : List (BitVec 8))) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (2 * (dec.ptsNeeded - 0)) ∗
          interpolateScratchAt s0.sp ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
          stackAt (s0.sp - 672#64) computeAtStack ∗
          (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ memRegion out_sret vecHeaderBytes ∗
            A.live pv_ptr 256 8 ∗ A.live out_ptr (2 * dec.ptsNeeded) 1 ∗
            memRegion ((s0.sp - 672#64) - 16384#64) 12032 ∗ F) by
        rw [stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
        simp only [Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        exact Entails.of_eq (by ac_rfl))
      (decodedMessageLoop_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp_ok hcomp_at
        dec s0.sp decA pv_ptr out_ptr pins
        hsp0 hpts hpins hsort hneed_le hall_ge s0 _ R Q
        (dec.ptsNeeded - 1) 0 (List.replicate 16 none) [] s2 (by omega) (by simp) (by simp)
        hpc2 hrun2 hsp2 htr2 (by rw [hx20_2, hx20_1, hx20]) hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
        (fun s3 hpc3 hrun3 hsp3 htr3 hx29_3 => ?_))
    have hrem_eq : dec.ptsNeeded - 1 + 1 = dec.ptsNeeded := by omega
    rw [hrem_eq]
    have hpolys_len :
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).1.length = 16 :=
      decodedMessageLoopTotal_fst_length dec (collectedSlices dec 0 16) dec.ptsNeeded 0 (List.replicate 16 none) [] (by simp)
    have hout_len :
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2.length =
          2 * dec.ptsNeeded := by
      simpa using decodedMessageLoopTotal_snd_length dec (collectedSlices dec 0 16) dec.ptsNeeded 0 (List.replicate 16 none) []
    apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
    rw [stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
    have hmem256_12032 :
        memRegion ((s0.sp - 672#64) - 4352#64) 256 ∗ memRegion ((s0.sp - 672#64) - 16384#64) 12032 =
          memRegion ((s0.sp - 672#64) - 16384#64) 12288 := by
      have hsub : (s0.sp - 672#64) - 16384#64 + 12032#64 = (s0.sp - 672#64) - 4352#64 := by bv_omega
      rw [show (12288 : Nat) = 12032 + 256 from rfl,
        memRegion_split ((s0.sp - 672#64) - 16384#64) 12032 256 (by decide), hsub, sepConj_comm]
    refine SepWP.weaken_pre
      (show _ ⊢
        optPolyCacheListAt A (s0.sp - 600#64)
          (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).1 ∗
          ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
          ((s0.sp - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((s0.sp - 208#64) ↦₆₄ out_ptr) ∗
          ((s0.sp - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          memRegion out_sret vecHeaderBytes ∗ A.live out_ptr (2 * dec.ptsNeeded) 1 ∗
          (out_ptr ↦ₛ (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2) ∗
          A.pool ∗ stackAt (s0.sp - 672#64) allocHookStack ∗
          (memRegion ((s0.sp - 672#64) - 16384#64) 12288 ∗ savedRegsAt s0.sp s0 ∗
            ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
            ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
            interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ A.live pv_ptr 256 8 ∗
            ptSliceRefListAt dec 0 pv_ptr pins ∗
            (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F)) by
        rw [← hmem256_12032]; exact Entails.of_eq (by ac_rfl))
      (dropOptPolyCache_from1404_placed_sepWP hdealloc_sat s0.sp out_sret out_ptr hsp0 dec.ptsNeeded hge1 hneed_le
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).1 hpolys_len
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2 hout_len
        hout_ne0 s3 _ _ hpc3 hrun3 hsp3 hx29_3 (fun s4 hpc4 hrun4 hsp4 htr4 => ?_))
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (decodedMessage_finish_from1904_placed_sepWP hdealloc_sat dec pins hpins s0 out_sret pv_ptr
        (BitVec.ofNat 64 dec.ptsNeeded)
        (some (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2) hsp0 s4
        (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ F) _
        hpc4 hrun4 hsp4 (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
    apply SepWP.done hpc_f hrun_f
    have htot := decodedMessageTotal_of_collect_false hcomp_false hpts hret
    refine SepWPp.weaken_pre
      (show _ ⊢
        optVecU8Of A out_sret (decodedMessageTotal dec) ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ F by
        rw [htot]; exact Entails.of_eq (by ac_rfl))
      (hnext sf hpc_f hrun_f hsp_f (by rw [htr_f, htr4, htr3]) hcs_f)

/-! ## Top-Level Entry Proof (`polyDecoderDecodedMessage_placed_ok`) -/

/-- Prologue (`+0..+32`, 8 instructions, `[LibsignalPlacement]`). -/
theorem decodedMessage_prologue_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (s0 : State) (P : SepProp) (post : State → SepProp → Prop) (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s0.pc = (blkPl_418).base) (hstat : s0.status = .Running)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 32#64 →
      sf.status = .Running → sf.sp = s0.sp - 672#64 → traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x0 = s0.readReg64 .x0 → sf.readReg64 .x8 = s0.readReg64 .x8 →
      sf.readReg64 .x29 = s0.sp - 96#64 → sf.readReg64 .x30 = s0.readReg64 .x30 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf (savedRegsAt s0.sp s0 ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s0 (memRegion (s0.sp - 96#64) 96 ∗ P) post := by
  have hsp672_al : (s0.sp - 672#64) &&& 15#64 = 0#64 := sp672_aligned s0.sp hsp0
  have hsp96_al : (s0.sp - 96#64) &&& 15#64 = 0#64 := by
    have h : (s0.sp - 96#64) &&& 15#64 = s0.sp &&& 15#64 := by bv_bits
    rw [h, hsp0]
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  rw [memRegion96_eq_exists_twelve s0.sp]
  wp_conv_pre => simp only [wp_norm, arm64_norm, sepConj_assoc]
  wp_pull_exists
  wp_steps 8
  refine SepWP.weaken_pre
    (show _ ⊢ savedRegsAt s0.sp s0 ∗ P by unfold savedRegsAt; exact Entails.of_eq (by ac_rfl))
    (hcont _ rfl (by simp [wp_norm, arm64_norm, hstat]) (by simp [wp_norm, arm64_norm]) rfl
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))

/-- Post-`pv_ptr`-allocation setup (`+80..+128`, 12 instructions, `[LibsignalPlacement]`). -/
theorem decodedMessage_allocPv_setup_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (dec : PolyDecoder) (sp0 decA pv_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hneed : dec.ptsNeeded < 2 ^ 64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 80#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hx0 : s.readReg64 .x0 = pv_ptr) (hx20 : s.readReg64 .x20 = decA)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 128#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      sf.readReg64 .x0 = pv_ptr → sf.readReg64 .x20 = decA → sf.readReg64 .x21 = 0#64 →
      sf.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) →
      sf.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) →
      sf.readReg64 .x24 = decA + 40#64 → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = 0#64 → sf.readReg64 .x27 = 0#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 → sf.readReg64 .x30 = s.readReg64 .x30 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 624#64) ↦₆₄ 16#64) ∗ ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 0#64) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        (∃∗ w648 : BitVec 64, (sp0 - 648#64) ↦₆₄ w648) ∗ (∃∗ w624 : BitVec 64, (sp0 - 624#64) ↦₆₄ w624) ∗
        (∃∗ w616 : BitVec 64, (sp0 - 616#64) ↦₆₄ w616) ∗ (∃∗ w608 : BitVec 64, (sp0 - 608#64) ↦₆₄ w608) ∗ P) post := by
  have hsp_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp672_aligned sp0 hsp0
  have hlsr := bv64_lsr4_ofNat hneed
  try dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat] at *
  wp_pull_exists
  wp_steps 12
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _ rfl (by simp [wp_norm, arm64_norm, hstat]) (by simpa [wp_norm, arm64_norm] using hsp) rfl
      (by simpa [wp_norm, arm64_norm] using hx0) (by simpa [wp_norm, arm64_norm] using hx20)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hlsr])
      (by simp [wp_norm, arm64_norm, bv64_and15_ofNat]) (by simp [wp_norm, arm64_norm, hx20])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))

theorem reassemble_polyDecoderAt {A : RustAlloc} (decA : BitVec 64) (dec : PolyDecoder)
    (hpts : dec.pts.length = 16) (hneed : dec.ptsNeeded < 2 ^ 64) :
    sortedSetPtListOf A decA dec.pts ∗
      ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((decA + 392#64) ↦₈ if dec.isComplete then 1#8 else 0#8) ∗
      memRegion (decA + 393#64) 7 ⊢
      polyDecoderAt A decA dec := by
  dsimp only [polyDecoderAt, NUM_POLYS, CHUNK_SIZE, boolByte, polyDecoderPadSize,
    polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff, BitVec.ofNat_eq_ofNat]
  exact Entails.pure_right ⟨hpts, hneed⟩ (Entails.of_eq (by ac_rfl))

theorem polyDecoderDecodedMessage_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (lagrangePreparePlacedSpec A))
    (hcomp_ok : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) lagrangeCompletePlacedSpec)
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (computeAtPlacedSpec A)) :
    DecodedMessagePlacedOkExt A ext := by
  unfold DecodedMessagePlacedOkExt; simp only [decodedMessagePlacedSpec]; wpp_init x s0
  have hx8 : s0.readReg64 (Reg.gpr 8#5) = x.out := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = x.decA := by assumption
  have hsort : PolyDecoderStrictSorted x.dec := by assumption
  clear h h_1 h_2 hpre
  have hshim : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem halloc_sat
  have hpan_err :
      ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)).externAt? (lsρ spqrHandleErrorSym) =
        some Rust.panicked :=
    (SpqrV1.Alloc.spqr_externAt?_of_mem).trans h_panic
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  wp_conv_pre =>
    dsimp only [polyDecoderAt, NUM_POLYS, CHUNK_SIZE, boolByte, polyDecoderPadSize,
      polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff, BitVec.ofNat_eq_ofNat]
    rw [show memRegion x.out vecHeaderBytes ∗
          (⌜x.dec.pts.length = 16 ∧ x.dec.ptsNeeded < 2 ^ 64⌝ ∗ sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
            memRegion (x.decA + 393#64) 7) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack =
        ⌜x.dec.pts.length = 16 ∧ x.dec.ptsNeeded < 2 ^ 64⌝ ∗
          (stackAt s0.sp decodedMessageStack ∗ memRegion x.out vecHeaderBytes ∗
            sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
            memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) by ac_rfl]
  apply SepWPp.pure_left; rintro ⟨hpts_len, hneed_lt⟩
  have hlen_bound : ∀ s ∈ x.dec.pts, s.vec.length ≤ 65536 := by
    intro s hs; rcases List.getElem_of_mem hs with ⟨i, hi, rfl⟩
    exact polyDecoderStrictSorted_elem_length_le hsort hi
  wp_conv_pre => rw [stackAt_decodedMessage_eq s0.sp]
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 32#64)
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (s0.sp - 96#64) 96 ∗
      (memRegion (s0.sp - 672#64) 576 ∗ stackAt (s0.sp - 672#64) extHookStack ∗
        memRegion x.out vecHeaderBytes ∗ sortedSetPtListOf A x.decA x.dec.pts ∗
        ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
        ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
        memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) by exact Entails.of_eq (by ac_rfl))
    (decodedMessage_prologue_placed_sepWP (ext := ext) s0 _ _ hsp0 hpc hrun
      (fun s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx29_1 hx30_1 => ?_))
  rcases Prod.mk.inj htr1 with ⟨htr1_tr, htr1_vr⟩
  apply SepWP.done hpc1 hrun1
  dsimp only [Reg.x0, Reg.x8, Reg.x29, Reg.x30] at hx0_1 hx8_1 hx29_1 hx30_1
  rw [hx0] at hx0_1; rw [hx8] at hx8_1
  have hsp1_al : s1.sp &&& 15#64 = 0#64 := by rw [hsp1]; exact sp672_aligned s0.sp hsp0
  have hsp1_aligned : s1.spAligned = true := by unfold State.spAligned; rw [hsp1_al]; rfl
  cases hcomp : x.dec.isComplete
  · -- `x.dec.isComplete = false`
    wp_conv_pre => simp only [Bool.false_eq_true, ↓reduceIte]
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_left (memRegion576_split_for_decodedMessage s0.sp))) ?_
    wp_conv_pre => rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64)]
    try dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hpan_err hpc1 ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_418).base + 76#64)
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i w_4 w_3 w_2 w_1 w
    wp_steps 5; wp_call hshim; wp_steps 3
    have hpow8 : ∃ m, 8 = 2 ^ m := ⟨3, rfl⟩
    wp_call halloc
    apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
    by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by simp [hptr0]
      wp_conv_pre => rw [alloc_post_pos' hptr0]
      apply SepWPp.pure_left; intro htr_fail
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps 4
      apply SepWP.done (by rfl) (by wp_norm_lhs)
      have htr_panic_eq :
          (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 8#64).writeReg64 (Reg.gpr 1#5)
            256#64).writeReg64 (Reg.gpr 30#5)
            ((blkPl_418).base + 1968#64)).setPC (lsρ spqrHandleErrorSym))).trace = s0.trace ++ [allocFailedEvent] := by
        change sf_1.trace = s0.trace ++ [allocFailedEvent]; rw [htr_fail, h, htr1_tr]
      refine SepWPp.panic (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hpan_err)
        (fun hm => by
          rw [← sepConj_assoc]
          exact allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _)
            ⟨allocFailedIn_of_trace_eq' htr_panic_eq,
              by rw [htr_panic_eq]; exact List.prefix_append s0.trace [allocFailedEvent]⟩ hm)
    · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
      wp_conv_pre => rw [alloc_post_neg' hptr0]
      apply SepWPp.pure_left; rintro ⟨_hptr_mod, htr_ok⟩
      apply SepWPp.of_sepWP (mid := (blkPl_418).base + 80#64)
      wp_steps 1
      apply SepWP.done (by simp [wp_norm, arm64_norm, hcbz]) (by simp [wp_norm, arm64_norm, hrun_sf_1])
      rw [h_1, hsp1]
      apply SepWPp.of_sepWP (mid := (blkPl_418).base + 128#64)
      refine SepWP.weaken_pre
        (show _ ⊢
          ((x.decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            (∃∗ w648 : BitVec 64, (s0.sp - 648#64) ↦₆₄ w648) ∗
            (∃∗ w624 : BitVec 64, (s0.sp - 624#64) ↦₆₄ w624) ∗
            (∃∗ w616 : BitVec 64, (s0.sp - 616#64) ↦₆₄ w616) ∗
            (∃∗ w608 : BitVec 64, (s0.sp - 608#64) ↦₆₄ w608) ∗
            (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ x.out) ∗
              memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
              interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
              memRegion (s0.sp - 120#64) 24 ∗ stackAt (s0.sp - 672#64) extHookStack ∗
              memRegion x.out vecHeaderBytes ∗ A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗
              memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
              sortedSetPtListOf A x.decA x.dec.pts ∗ ((x.decA + 392#64) ↦₈ 0#8) ∗
              memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) by
          rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64),
            show s0.sp - 672#64 - 16384#64 = s0.sp - 17056#64 by bv_omega]
          try dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat]
          refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w)))
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_2))))
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_3)))))
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_4))))))
          exact Entails.of_eq (by ac_rfl))
        (decodedMessage_allocPv_setup_placed_sepWP (ext := ext) x.dec s0.sp x.decA (sf_1.readReg64 (Reg.gpr 0#5)) hsp0 hneed_lt _ _ _
          (by rfl)
          (by simp [wp_norm, arm64_norm, hrun_sf_1]) (by simp [wp_norm, arm64_norm, hsp_sf, h_1, hsp1])
          (by simp [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]; rw [h_13, h_3])
          (fun s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 hx30_2 => ?_))
      have htr2' : traceVRegs s2 = traceVRegs s0 := by rw [htr2]; simp [traceVRegs, wp_norm, arm64_norm, *]
      have hx29_2' : s2.readReg64 .x29 = s0.sp - 96#64 := by
        simp [wp_norm, arm64_norm, *]
      wp_conv_pre =>
        rw [sortedSetPtListOf_eq_exists_pins A x.dec.pts x.decA]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i pins
      apply SepWP.done hpc2 hrun2
      wp_conv_pre =>
        try dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat]
        rw [show ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
              ((s0.sp - 608#64) ↦₆₄ 0#64) ∗ savedRegsAt s0.sp s0 ∗
              ((s0.sp - 632#64) ↦₆₄ x.out) ∗ memRegion (s0.sp - 600#64) 384 ∗
              memRegion (s0.sp - 216#64) 24 ∗ interpolateScratchAt s0.sp ∗
              memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
              stackAt (s0.sp - 672#64) extHookStack ∗ memRegion x.out vecHeaderBytes ∗
              A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗ memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
              ⌜pins.length = x.dec.pts.length⌝ ∗ sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
              ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7 ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool =
            ⌜pins.length = x.dec.pts.length⌝ ∗
              (((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 608#64) ↦₆₄ 0#64) ∗
                sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
                memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
                (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                  memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
                  interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
                  memRegion (s0.sp - 120#64) 24 ∗ memRegion x.out vecHeaderBytes ∗
                  A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗
                  reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                  (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                    ((x.decA + 392#64) ↦₈ 0#8) ∗
                    memRegion (x.decA + 393#64) 7))) by ac_rfl]
      apply SepWPp.pure_left; intro hpins
      have hpins16 : pins.length = 16 := by rw [hpins, hpts_len]
      cases hcol : (collectPointsVecsTotal x.dec 0 16 false []).1
      · -- `(collectPointsVecsTotal x.dec 0 16 false []).1 = false`
        have ⟨hall_ge, _⟩ := collectPointsVecs_false_bounds x.dec hpts_len hsort hcol
        apply SepWPp.of_sepWP (mid := (blkPl_418).base + 352#64)
        refine SepWP.weaken_pre
          (show _ ⊢
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 608#64) ↦₆₄ 0#64) ∗
              sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
              ptSliceRefListAt x.dec 0 (sf_1.readReg64 (Reg.gpr 0#5)) (pins.take 0) ∗
              memRegion ((sf_1.readReg64 (Reg.gpr 0#5)) + BitVec.ofNat 64 (16 * 0)) (16 * (16 - 0)) ∗
              (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
                interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
                memRegion (s0.sp - 120#64) 24 ∗ memRegion x.out vecHeaderBytes ∗
                A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗
                reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((x.decA + 392#64) ↦₈ 0#8) ∗
                  memRegion (x.decA + 393#64) 7)) by
            simp only [List.take_zero, ptSliceRefListAt, Nat.mul_zero, Nat.sub_zero,
              BitVec.ofNat_eq_ofNat, BitVec.add_zero, emp_sepConj]
            exact Entails.of_eq (by ac_rfl))
          (collectPointsVecs_ok_loop_placed_sepWP (ext := ext) x.dec x.decA (sf_1.readReg64 (Reg.gpr 0#5)) s0.sp pins
            hpts_len hpins16 hneed_lt hlen_bound hall_ge hsp0 15 0 s2 0#64 _ _ (by decide)
            hpc2 hrun2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
            (fun s3 hpc3 hrun3 hsp3 htr3 _hx0_3 hx20_3 hx29_3 _hx30_3 => ?_))
        apply SepWP.done hpc3 hrun3
        conv => arg 6; ext sf P_f; rw [← sepConj_assoc]
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (decodedMessage_afterCollect_placed_wpp h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hprep hcomp_ok hcomp_at
            x.dec x.decA x.out (sf_1.readReg64 (Reg.gpr 0#5)) pins
            hcomp hpts_len hpins16 hsort hcol s0 s3
            (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((x.decA + 392#64) ↦₈ 0#8) ∗
              memRegion (x.decA + 393#64) 7) R _
            hsp0 hpc3 hrun3 hsp3 (by rw [htr3, htr2']) hx20_3 (by rw [hx29_3, hx29_2'])
            (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
        rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f with ⟨hcs_f, htr_f⟩
        refine SepWPp.weaken_pre
          (show _ ⊢
            ⌜sf.trace = s0.trace⌝ ∗ optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
              polyDecoderAt A x.decA x.dec ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack by
            refine Entails.trans
              (sepConj_mono_right (sepConj_mono_left
                (sortedSetPtListPinAt_entails_sortedSetPtListOf A pins x.dec.pts x.decA hpins))) ?_
            refine Entails.pure_right htr_f ?_
            refine Entails.trans (Entails.of_eq (show _ =
              (sortedSetPtListOf A x.decA x.dec.pts ∗
                ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7) ∗
              (optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
                tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack) by ac_rfl)) ?_
            rw [show (0#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
            refine Entails.trans (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
            exact Entails.of_eq (by ac_rfl))
          (SepWPp.done hpc_f hrun_f ⟨fun hm => by simpa only [sepConj_assoc] using hm, hsp_f, hcs_f⟩)
      · -- `(collectPointsVecsTotal x.dec 0 16 false []).1 = true`
        have hex_lt := exists_lt_necessaryPoints_of_collect_true x.dec hpts_len hcol
        apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
        refine collectPointsVecs_none_loop_placed_sepWP (ext := ext) x.dec x.decA (sf_1.readReg64 (Reg.gpr 0#5)) s0.sp pins
          hpts_len hpins16 hneed_lt hlen_bound hsp0
          15 0 0 false s2 0#64 _ _ (by decide) (by decide) (Or.inr hex_lt)
          hpc2 hrun2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
          (fun s3 pvLenFinal hpc3 hrun3 hsp3 htr3 _hx29_3 _hx30_3 => ?_)
        refine SepWP.weaken_pre
          (show _ ⊢
            (interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24) ∗
              (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
                ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                ((s0.sp - 608#64) ↦₆₄ pvLenFinal) ∗ memRegion x.out vecHeaderBytes ∗
                A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗ memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
                memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
                savedRegsAt s0.sp s0 ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                (sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
                  ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((x.decA + 392#64) ↦₈ 0#8) ∗
                  memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt)) by
            exact Entails.of_eq (by ac_rfl)) ?_
        refine SepWP.weaken_pre (sepConj_mono_left (scratch_and_pads_entails_regions s0.sp)) ?_
        refine SepWP.weaken_pre
          (show _ ⊢
            (memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗ memRegion (s0.sp - 192#64) 96) ∗
              (((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
                ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                ((s0.sp - 608#64) ↦₆₄ pvLenFinal) ∗ memRegion x.out vecHeaderBytes ∗
                A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗ memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
                memRegion (s0.sp - 672#64) 24 ∗ memRegion (s0.sp - 640#64) 8 ∗
                savedRegsAt s0.sp s0 ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                (sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
                  ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((x.decA + 392#64) ↦₈ 0#8) ∗
                  memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt)) by
            exact Entails.of_eq (by ac_rfl)) ?_
        refine SepWP.weaken_pre (sepConj_mono_left (memRegion_384_24_96_entails_504 s0.sp)) ?_
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (decodedMessage_epilogue_from288_placed_sepWP hdealloc_sat s0 s0.sp x.out (sf_1.readReg64 (Reg.gpr 0#5))
            (BitVec.ofNat 64 x.dec.ptsNeeded) pvLenFinal hsp0 s3
            (sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
              ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((x.decA + 392#64) ↦₈ 0#8) ∗
              memRegion (x.decA + 393#64) 7 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) _
            hpc3 hrun3 hsp3 (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        have htot := decodedMessageTotal_of_collect_true hcomp hpts_len hcol
        have htr_f_vr : traceVRegs sf = traceVRegs s0 := by rw [htr_f, htr3, htr2']
        rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f_vr with ⟨hcs_f, htr_f'⟩
        refine SepWPp.weaken_pre
          (show _ ⊢
            ⌜sf.trace = s0.trace⌝ ∗ optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
              polyDecoderAt A x.decA x.dec ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack by
            rw [htot]
            refine Entails.trans
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (sortedSetPtListPinAt_entails_sortedSetPtListOf A pins x.dec.pts x.decA hpins))))) ?_
            refine Entails.pure_right htr_f' ?_
            refine Entails.trans (Entails.of_eq (show _ =
              (sortedSetPtListOf A x.decA x.dec.pts ∗
                ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7) ∗
              (optVecU8Of A x.out none ∗
                tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack) by ac_rfl)) ?_
            rw [show (0#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
            refine Entails.trans (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
            exact Entails.of_eq (by ac_rfl))
          (SepWPp.done hpc_f hrun_f ⟨fun hm => by simpa only [sepConj_assoc] using hm, hsp_f, hcs_f⟩)
  · -- `x.dec.isComplete = true`
    wp_conv_pre => simp only [↓reduceIte]
    have hout_split : memRegion x.out vecHeaderBytes =
        (∃∗ w0 : BitVec 64, x.out ↦₆₄ w0) ∗ memRegion (x.out + 8#64) 16 := by
      rw [show vecHeaderBytes = 8 + 16 from rfl,
        memRegion_split x.out 8 16 (by decide), ProofLib.memRegion_eight x.out]
    wp_conv_pre => rw [hout_split]
    try dsimp only [BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    wp_steps 5
    have hnone_eq :
        (x.out ↦₆₄ 18446744073709551615#64) ∗ memRegion (x.out + 8#64) 16 =
          optVecU8Of A x.out none := by unfold optVecU8Of noneCap; rfl
    refine SepWP.weaken_pre
      (show _ ⊢
        savedRegsAt s0.sp s0 ∗ memRegion (s0.sp - 672#64) 576 ∗
          stackAt (s0.sp - 672#64) extHookStack ∗
          (optVecU8Of A x.out none ∗ sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 1#8) ∗ memRegion (x.decA + 393#64) 7 ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) by
        rw [← hnone_eq]; exact Entails.of_eq (by ac_rfl))
      (decodedMessage_epilogue_ret_placed_sepWP (ext := ext) s0 s0.sp hsp0 _ _ _
        (by rfl)
        (by simp [wp_norm, arm64_norm, hrun1]) (by simpa [wp_norm, arm64_norm] using hsp1)
        (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
    apply SepWP.done hpc_f hrun_f
    have htot := decodedMessageTotal_of_isComplete_true hcomp
    have htr_f_vr : traceVRegs sf = traceVRegs s0 := by simpa [wp_norm, arm64_norm, htr1] using htr_f
    rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f_vr with ⟨hcs_f, htr_f'⟩
    refine SepWPp.weaken_pre
      (show _ ⊢
        ⌜sf.trace = s0.trace⌝ ∗ optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
          polyDecoderAt A x.decA x.dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack by
        rw [htot]
        refine Entails.pure_right htr_f' ?_
        refine Entails.trans (Entails.of_eq (show _ =
          (sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 1#8) ∗ memRegion (x.decA + 393#64) 7) ∗
          (optVecU8Of A x.out none ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack) by ac_rfl)) ?_
        rw [show (1#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
        refine Entails.trans (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
        exact Entails.of_eq (by ac_rfl))
      (SepWPp.done hpc_f hrun_f ⟨fun hm => by simpa only [sepConj_assoc] using hm, hsp_f, hcs_f⟩)

end CryptoVerification.SpqrV1.Poly.DecodedMessage
