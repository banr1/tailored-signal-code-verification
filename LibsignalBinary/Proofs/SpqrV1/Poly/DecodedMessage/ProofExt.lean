/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpilogue
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopExt
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: 4K-Stack Top-Level Proof

**Checked by Lean.**

Proves `polyDecoderDecodedMessage_ok_4k` and `polyDecoderDecodedMessage_ok_inImage_4k` under
`AllocContracts4K` at stack budget `decodedMessageStack` (`17056` B).
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack allocFailedEvent allocFailedIn)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet (extHookStack panic_at_handle_error_ext
  subroutine_ok_inImage_of_subroutine_ok tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder NUM_POLYS CHUNK_SIZE)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly (boolByte vecHeaderBytes
  polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff polyDecoderPadOff
  polyDecoderPadSize sortedSetPtListOf sortedSetPtListPinAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted)
open CryptoVerification.SpqrV1.Poly.ComputeAt (computeAtStack computeAt_ok_4k)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeComplete_ok)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  decodedMessageName decodedMessage_fnOff decodedMessageStack decodedMessageSpec
  DecodedMessageOkExt decodedMessageTotal decodedMessageLoopTotal collectPointsVecsTotal
  collectedSlices optVecU8Of optPolyCacheListAt ptSliceRefListAt savedRegsAt traceVRegs
  sp672_aligned CalleeSavedGprsPreserved calleeSavedPreserved_of_gprs_traceVRegs
  stackAt_decodedMessage_eq stackAt_extHook_eq_allocHook stackAt_extHook_eq_computeAt
  stackAt_computeAt_eq_allocHook sortedSetPtListOf_eq_exists_pins
  sortedSetPtListPinAt_entails_sortedSetPtListOf polyDecoderStrictSorted_elem_length_le
  collectPointsVecs_ok_loop_sepWP collectPointsVecs_none_loop_sepWP
  allocFailedIn_of_trace_eq' interpolateScratchAt decodedMessage_epilogue_ret_sepWP
  initOptPolyCache_sepWP bv64_lsl1_norm_proof bv64_ne0_of_pos_le allocOut_zero_sepWP
  allocOut_pos_setup_sepWP collectPointsVecs_false_bounds
  exists_lt_necessaryPoints_of_collect_true decodedMessageLoopTotal_fst_length
  decodedMessageLoopTotal_snd_length decodedMessageTotal_of_isComplete_true
  decodedMessageTotal_of_collect_true decodedMessageTotal_of_ptsNeeded_zero
  decodedMessageTotal_of_collect_false ptSliceRefListAt_entails_memRegion256
  memRegion_24_8_8_8_entails_48 scratch_and_pads_entails_regions
  memRegion_384_24_96_entails_504 memRegion_8_384_24_96_entails_512
  memRegion576_split_for_decodedMessage decodedMessage_prologue_sepWP
  decodedMessage_allocPv_setup_sepWP reassemble_polyDecoderAt
  bv64_lsl1_norm bv64_add1_norm
  sp96_sub_120 sp96_sub_96 sp96_sub_80 sp96_sub_72 sp96_sub_64 sp96_sub_56
  sp96_sub_48 sp96_sub_40 sp96_sub_32 sp216_add_48 sp192_add_8 sp168_add_8
  sp144_add_8 sp144_add_16
  dropOptPolyCache_from1404_sepWP_core dropOptPolyCache_from1460_sepWP_core
  decodedMessage_epilogue_from1904_sepWP_core decodedMessage_epilogue_from288_sepWP_core)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopExt (
  decodedMessageLoop_wpp_4k)

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local wp_norm ↓, local arm64_norm ↓] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm, local arm64_norm] bv64_lsl1_norm bv64_add1_norm bv64_lsl1_norm_proof
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  sp96_sub_120 sp96_sub_96 sp96_sub_80 sp96_sub_72 sp96_sub_64 sp96_sub_56
  sp96_sub_48 sp96_sub_40 sp96_sub_32 sp216_add_48 sp192_add_8 sp168_add_8
  sp144_add_8 sp144_add_16

open Lean Elab Tactic in
local elab "decoded_message_fetches_range_ext " b:term:max H:term:max k0:num len:num : tactic => do
  let codeName := `CryptoVerification.libsignalSessionCode
  let binName := `CryptoVerification.SpqrV1.Poly.DecodedMessage.decodedMessageBin
  let eOff ← ProofLib.CodeLookup.lookup codeName .fnOff
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches_range $(mkCIdent codeName) $(mkIdent binName) $b $H $hfn $offLit $k0 $len))

/-! ## Pure & Alloc Post Helpers -/

private theorem pull_pure_after_two_4k (P1 P2 : SepProp) (φ : Prop) (Rest : SepProp) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  rw [← sepConj_assoc P2 ⌜φ⌝ Rest, sepConj_comm P2 ⌜φ⌝, sepConj_assoc ⌜φ⌝ P2 Rest,
      ← sepConj_assoc P1 ⌜φ⌝ _, sepConj_comm P1 ⌜φ⌝, sepConj_assoc ⌜φ⌝ P1 _]

private theorem alloc_post_pos_4k {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ : Prop} {Q : SepProp}
    (h0 : x0 = 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else Q) ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  have h0' : x0 = 0 := h0
  simp only [h0', ↓reduceIte]
  exact pull_pure_after_two_4k P1 P2 φ Rest

private theorem alloc_post_neg_4k {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ ψ : Prop} {Q : SepProp}
    (h0 : x0 ≠ 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else ⌜ψ⌝ ∗ Q) ∗ Rest = ⌜ψ⌝ ∗ P1 ∗ P2 ∗ Q ∗ Rest := by
  have h0' : x0 ≠ 0 := h0
  simp only [h0', ↓reduceIte]
  rw [sepConj_assoc ⌜ψ⌝ Q Rest]
  exact pull_pure_after_two_4k P1 P2 ψ (Q ∗ Rest)

private theorem pure_elim_focus_4k {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P' Q Qp)
    (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp := by
  rw [hf]
  exact SepWPp.pure_left h

/-! ## Output Buffer Allocation (`entry + 424#64` to `entry + 548#64`) under `AllocContracts4K` -/

/-- Positive-length output path (`1 ≤ ptsNeeded ≤ 16 * 65536`) from `entry + 424#64` to
    `entry + 548#64`. -/
theorem allocOut_pos_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hA : AllocContracts4K b A ext) (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (ptsNeeded : Nat) (hge1 : 1 ≤ ptsNeeded) (hle : ptsNeeded ≤ 16 * 65536)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 424#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (out_ptr : BitVec 64) (sf : State),
      out_ptr ≠ 0#64 → sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = 0#64 → sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ 0#64) ∗ A.live out_ptr (2 * ptsNeeded) 1 ∗
          (out_ptr ↦ₛ ([] : List (BitVec 8))) ∗ memRegion out_ptr (2 * ptsNeeded) ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (memRegion (sp0 - 216#64) 24 ∗ A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := hA.shim_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have halloc := hA.alloc_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
      "__rustc::__rust_alloc")
    (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hpan_err :
      (tripleRatchetProgAtExt b ext).externAt?
        ((tripleRatchetProgAtExt b ext).fnAddr decodedMessageName +
          bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
            "alloc::raw_vec::handle_error")) =
        some Rust.panicked :=
    panic_at_handle_error_ext b ext decodedMessageName
      (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
        "alloc::raw_vec::handle_error")
      (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hne0_pts : (BitVec.ofNat 64 ptsNeeded == 0#64) = false := bv64_ne0_of_pos_le hge1 (by omega)
  have hne0_2pts : (BitVec.ofNat 64 (2 * ptsNeeded) == 0#64) = false := bv64_ne0_of_pos_le (by omega) (by omega)
  have htoNat_2pts : (BitVec.ofNat 64 (2 * ptsNeeded)).toNat = 2 * ptsNeeded := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow1 : ∃ m, 1 = 2 ^ m := ⟨0, rfl⟩
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by unfold State.spAligned; rw [hsp, sp672_aligned sp0 hsp0]; rfl
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 424 64
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hshim halloc hpan_err hpc ⊢
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 476#64)
  wp_steps 5
  wp_call hshim
  wp_steps 4
  wp_call halloc
  apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
  by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · have hcbnz : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = false := by simp [hptr0]
    wp_conv_pre => rw [alloc_post_pos_4k hptr0]
    apply SepWPp.pure_left; intro htr_fail
    apply SepWPp.of_sepWP (mid := entry +
      bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
        "alloc::raw_vec::handle_error"))
    wp_steps 5
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have htr_panic_eq :
        (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5)
          (BitVec.ofNat 64 (2 * ptsNeeded))).writeReg64 (Reg.gpr 30#5)
          (entry + 452#64)).setPC (entry +
            bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
              "alloc::raw_vec::handle_error")))).trace = s0.trace ++ [allocFailedEvent] := by
      change sf_1.trace = s0.trace ++ [allocFailedEvent]; rw [htr_fail, h, htr_tr]
    refine SepWPp.panic (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hpan_err)
      (fun hm => allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _)
        ⟨allocFailedIn_of_trace_eq' htr_panic_eq,
          by rw [htr_panic_eq]; exact List.prefix_append s0.trace [allocFailedEvent]⟩ hm)
  · have hcbnz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
    wp_conv_pre => rw [alloc_post_neg_4k hptr0]
    apply SepWPp.pure_left; rintro ⟨_hptr_mod, htr_ok⟩
    apply SepWPp.of_sepWP (mid := entry + 488#64)
    wp_steps 1
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf_1])
    rw [h_1, hsp]
    apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 548#64)
    refine SepWP.weaken_pre
      (show _ ⊢
        memRegion (sp0 - 216#64) 24 ∗
          (A.live (sf_1.readReg64 (Reg.gpr 0#5)) (2 * ptsNeeded) 1 ∗
            ((sf_1.readReg64 (Reg.gpr 0#5)) ↦ₛ ([] : List (BitVec 8))) ∗
            memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * ptsNeeded) ∗
            A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F) by
        simp only [pointsToBytes_nil]; sep_frame)
      (allocOut_pos_setup_sepWP sp0 (sf_1.readReg64 (Reg.gpr 0#5)) ptsNeeded hge1 hle _ _ _
        (by dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat]; rw [hentry]; simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_sf_1]) (by simp [wp_norm, arm64_norm, hsp_sf, h_1, hsp])
        (by simp [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]; rw [h_14, h_4])
        (by simp only [wp_norm, arm64_norm]; rw [h_17, h_7]; exact hx24)
        (by simp [wp_norm, arm64_norm, *])
        (fun sf_2 hpc2 hstat2 hsp2 htr2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_))
    apply SepWP.done hpc2 hstat2
    have hpc2' : sf_2.pc = entry + 548#64 := by
      dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hpc2
      rw [hentry] at hpc2; exact hpc2
    refine SepWPp.weaken_pre (by sep_frame)
      (hnext (sf_1.readReg64 (Reg.gpr 0#5)) sf_2 hptr0 hpc2' hstat2 hsp2
        (by rw [htr2]; simp [traceVRegs, wp_norm, arm64_norm, *])
        (by rw [hx20_2]; simp only [wp_norm, arm64_norm]; rw [h_13, h_3])
        hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2)

/-! ## Post-`collectPointsVecs` Execution (`entry + 352#64` to Return) -/

/-- Helper: from `entry + 1904#64` after `dropOptPolyCache_from1404_sepWP_4k` or
    `dropOptPolyCache_from1460_sepWP_4k`, collapses stack regions and `ptSliceRefListAt` and
    executes `decodedMessage_epilogue_from1904_sepWP_4k`. -/
theorem decodedMessage_finish_from1904_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (dec : PolyDecoder) (pins : List VecPin) (hpins : pins.length = 16)
    (s0 : State) (out_sret pv_ptr w648 : BitVec 64) (resOpt : Option (List (BitVec 8)))
    (hsp0 : s0.sp &&& 0xf#64 = 0#64) (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1904#64)
    (hstat : s.status = .Running) (hsp : s.sp = s0.sp - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp →
      traceVRegs sf = traceVRegs s → CalleeSavedGprsPreserved s0 sf →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (optVecU8Of A out_sret resOpt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
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
          savedRegsAt s0.sp s0 ∗ A.pool ∗ (optVecU8Of A out_sret resOpt ∗ P))) by sep_frame) ?_
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
          (optVecU8Of A out_sret resOpt ∗ P)) by sep_frame) ?_
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
        (optVecU8Of A out_sret resOpt ∗ P) by sep_frame)
    (decodedMessage_epilogue_from1904_sepWP_core hA.dealloc s0 s0.sp pv_ptr hsp0 s
      (optVecU8Of A out_sret resOpt ∗ P) post hpc hstat hsp
      (fun sf hpc_f hrun_f hsp_f htr_f hcs_f =>
        SepWP.weaken_pre (by sep_frame) (hcont sf hpc_f hrun_f hsp_f htr_f hcs_f)))

/-- Execution from `entry + 352#64` to function return (`s0.readReg64 .x30`) under
    `AllocContracts4K b A ext` when `dec.isComplete = false` and
    `(collectPointsVecsTotal dec 0 16 false []).1 = false`. -/
theorem decodedMessage_afterCollect_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts4K b A ext)
    (dec : PolyDecoder) (decA out_sret pv_ptr : BitVec 64) (pins : List VecPin)
    (hcomp_false : dec.isComplete = false) (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec) (hret : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 352#64)
    (hstat : s.status = .Running) (hsp : s.sp = s0.sp - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx20 : s.readReg64 .x20 = decA) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp →
      traceVRegs sf = traceVRegs s0 → CalleeSavedGprsPreserved s0 sf →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (optVecU8Of A out_sret (decodedMessageTotal dec) ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
        ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
        memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
        interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
        memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
        ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
        reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗ F) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have ⟨hall_ge, hneed_le⟩ := collectPointsVecs_false_bounds dec hpts hsort hret
  apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 424#64)
  refine SepWP.weaken_pre
    (show _ ⊢
      ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ memRegion (s0.sp - 600#64) 384 ∗
        (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗ ((s0.sp - 624#64) ↦₆₄ 16#64) ∗
          ((s0.sp - 616#64) ↦₆₄ pv_ptr) ∗ ((s0.sp - 608#64) ↦₆₄ 16#64) ∗
          memRegion (s0.sp - 216#64) 24 ∗ interpolateScratchAt s0.sp ∗
          memRegion (s0.sp - 672#64) 8 ∗ memRegion (s0.sp - 120#64) 24 ∗
          memRegion out_sret vecHeaderBytes ∗ A.live pv_ptr 256 8 ∗
          ptSliceRefListAt dec 0 pv_ptr pins ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗ F) by sep_frame)
    (initOptPolyCache_sepWP (A := A) s0.sp (BitVec.ofNat 64 dec.ptsNeeded) hsp0 s _ _
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
            reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗ F) by sep_frame)
      (allocOut_zero_sepWP s0.sp s1 _ _ hpc1 hrun1 hsp1 hx24_0 (by rw [hx29_1, hx29])
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
            (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTableAt b ∗ tokenInitAt b ∗ F)) by sep_frame)
      (dropOptPolyCache_from1460_sepWP_core hA.dealloc s0.sp out_sret hsp0 s2 _ _
        hpc2 hrun2 hsp2 hx29_2 (fun s3 hpc3 hrun3 hsp3 htr3 => ?_))
    refine SepWP.weaken_pre (by sep_frame)
      (decodedMessage_finish_from1904_sepWP_4k hA dec pins hpins s0 out_sret pv_ptr
        (BitVec.ofNat 64 dec.ptsNeeded) (some []) hsp0 s3
        (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTableAt b ∗ tokenInitAt b ∗ F) _
        hpc3 hrun3 hsp3 (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
    apply SepWP.done hpc_f hrun_f
    have htot := decodedMessageTotal_of_ptsNeeded_zero hcomp_false hpts hret hneed0
    refine SepWPp.weaken_pre
      (show _ ⊢
        optVecU8Of A out_sret (decodedMessageTotal dec) ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ F by
        rw [htot]; sep_frame)
      (hnext sf hpc_f hrun_f hsp_f (by rw [htr_f, htr3, htr2, htr1, htr]) hcs_f)
  · have hge1 : 1 ≤ dec.ptsNeeded := Nat.pos_of_ne_zero hneed0
    have hcomp_ok := lagrangeComplete_ok b ext
    have hcomp_at := computeAt_ok_4k b hb A ext hA
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
            reduceTableAt b ∗ tokenInitAt b ∗ memRegion ((s0.sp - 672#64) - 4352#64) 256 ∗
            memRegion ((s0.sp - 672#64) - 16384#64) 12032 ∗ F) by sep_frame)
      (allocOut_pos_wpp_4k hA s0.sp hsp0 dec.ptsNeeded hge1 hneed_le s0 s1 _ R Q
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
          interpolateScratchAt s0.sp ∗ reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
          stackAt (s0.sp - 672#64) computeAtStack ∗
          (savedRegsAt s0.sp s0 ∗ ((s0.sp - 632#64) ↦₆₄ out_sret) ∗
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ memRegion (s0.sp - 672#64) 8 ∗
            memRegion (s0.sp - 120#64) 24 ∗ memRegion out_sret vecHeaderBytes ∗
            A.live pv_ptr 256 8 ∗ A.live out_ptr (2 * dec.ptsNeeded) 1 ∗
            memRegion ((s0.sp - 672#64) - 16384#64) 12032 ∗ F) by
        rw [stackAt_computeAt_eq_allocHook (s0.sp - 672#64)]
        simp only [Nat.mul_zero, Nat.sub_zero, BitVec.add_zero]
        sep_frame)
      (decodedMessageLoop_wpp_4k hb hA hcomp_ok hcomp_at dec s0.sp decA pv_ptr out_ptr pins
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
            (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTableAt b ∗ tokenInitAt b ∗ F)) by
        rw [← hmem256_12032]; sep_frame)
      (dropOptPolyCache_from1404_sepWP_core hA.dealloc s0.sp out_sret out_ptr hsp0 dec.ptsNeeded hge1 hneed_le
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).1 hpolys_len
        (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2 hout_len
        hout_ne0 s3 _ _ hpc3 hrun3 hsp3 hx29_3 (fun s4 hpc4 hrun4 hsp4 htr4 => ?_))
    refine SepWP.weaken_pre (by sep_frame)
      (decodedMessage_finish_from1904_sepWP_4k hA dec pins hpins s0 out_sret pv_ptr
        (BitVec.ofNat 64 dec.ptsNeeded)
        (some (decodedMessageLoopTotal dec (collectedSlices dec 0 16) 0 dec.ptsNeeded (List.replicate 16 none) []).2) hsp0 s4
        (sortedSetPtListPinAt A decA pins dec.pts ∗ reduceTableAt b ∗ tokenInitAt b ∗ F) _
        hpc4 hrun4 hsp4 (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
    apply SepWP.done hpc_f hrun_f
    have htot := decodedMessageTotal_of_collect_false hcomp_false hpts hret
    refine SepWPp.weaken_pre
      (show _ ⊢
        optVecU8Of A out_sret (decodedMessageTotal dec) ∗ sortedSetPtListPinAt A decA pins dec.pts ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack ∗ F by
        rw [htot]; sep_frame)
      (hnext sf hpc_f hrun_f hsp_f (by rw [htr_f, htr4, htr3]) hcs_f)

/-! ## Top-Level Entry Proofs (`polyDecoderDecodedMessage_ok_4k`) -/

/-- `<PolyDecoder as Decoder>::decoded_message` satisfies `decodedMessageSpec A b` under
    4 KB `AllocContracts4K b A ext`. -/
theorem polyDecoderDecodedMessage_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    DecodedMessageOkExt b A ext := by
  unfold DecodedMessageOkExt; simp only [decodedMessageSpec]; wpp_init x s0
  have hb : b &&& 0xfff#64 = 0#64 := by assumption
  have hx8 : s0.readReg64 (Reg.gpr 8#5) = x.out := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = x.decA := by assumption
  have hsort : PolyDecoderStrictSorted x.dec := by assumption
  clear h h_1 h_2 h_3 hpre
  have hshim := hA.shim_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have halloc := hA.alloc_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
      "__rustc::__rust_alloc")
    (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hpan_err :
      (tripleRatchetProgAtExt b ext).externAt?
        ((tripleRatchetProgAtExt b ext).fnAddr decodedMessageName +
          bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
            "alloc::raw_vec::handle_error")) =
        some Rust.panicked :=
    panic_at_handle_error_ext b ext decodedMessageName
      (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
        "alloc::raw_vec::handle_error")
      (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  wp_conv_pre =>
    dsimp only [polyDecoderAt, NUM_POLYS, CHUNK_SIZE, boolByte, polyDecoderPadSize,
      polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff, BitVec.ofNat_eq_ofNat]
  refine pure_elim_focus_4k (x.dec.pts.length = 16 ∧ x.dec.ptsNeeded < 2 ^ 64)
    (fun ⟨hpts_len, hneed_lt⟩ => ?_) (by sep_focus)
  have hlen_bound : ∀ s ∈ x.dec.pts, s.vec.length ≤ 65536 := by
    intro s hs; rcases List.getElem_of_mem hs with ⟨i, hi, rfl⟩
    exact polyDecoderStrictSorted_elem_length_le hsort hi
  wp_conv_pre => rw [stackAt_decodedMessage_eq s0.sp]
  apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 32#64)
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (s0.sp - 96#64) 96 ∗
      (memRegion (s0.sp - 672#64) 576 ∗ stackAt (s0.sp - 672#64) extHookStack ∗
        memRegion x.out vecHeaderBytes ∗ sortedSetPtListOf A x.decA x.dec.pts ∗
        ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
        ((x.decA + 392#64) ↦₈ if x.dec.isComplete then 1#8 else 0#8) ∗
        memRegion (x.decA + 393#64) 7 ∗ tokenInitAt b ∗ reduceTableAt b ∗ A.pool) by sep_frame)
    (decodedMessage_prologue_sepWP s0 _ _ hsp0 (by simpa [wp_norm, arm64_norm] using hpc) hrun
      (fun s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx29_1 hx30_1 => ?_))
  rcases Prod.mk.inj htr1 with ⟨htr1_tr, htr1_vr⟩
  apply SepWP.done hpc1 hrun1
  dsimp only [Reg.x0, Reg.x8, Reg.x29, Reg.x30] at hx0_1 hx8_1 hx29_1 hx30_1
  rw [hx0] at hx0_1; rw [hx8] at hx8_1
  have hsp1_al : s1.sp &&& 15#64 = 0#64 := by rw [hsp1]; exact sp672_aligned s0.sp hsp0
  have hsp1_aligned : s1.spAligned = true := by unfold State.spAligned; rw [hsp1_al]; rfl
  cases hcomp : x.dec.isComplete
  · wp_conv_pre => simp only [Bool.false_eq_true, ↓reduceIte]
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_left (memRegion576_split_for_decodedMessage s0.sp))) ?_
    wp_conv_pre => rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64)]
    decoded_message_fetches_range_ext b (Rust.withPanics ext) 32 48
    decoded_message_fetches_range_ext b (Rust.withPanics ext) 1956 12
    dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hshim halloc hpan_err hpc1 ⊢
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 76#64)
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i w_4 w_3 w_2 w_1 w
    wp_steps 5; wp_call hshim; wp_steps 3
    have hpow8 : ∃ m, 8 = 2 ^ m := ⟨3, rfl⟩
    wp_call halloc
    apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
    by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by simp [hptr0]
      wp_conv_pre => rw [alloc_post_pos_4k hptr0]
      apply SepWPp.pure_left; intro htr_fail
      apply SepWPp.of_sepWP (mid := entry +
        bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
          "alloc::raw_vec::handle_error"))
      wp_steps 4
      apply SepWP.done (by rfl) (by wp_norm_lhs)
      have htr_panic_eq :
          (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 8#64).writeReg64 (Reg.gpr 1#5)
            256#64).writeReg64 (Reg.gpr 30#5)
            (entry + 1968#64)).setPC (entry +
              bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
                "alloc::raw_vec::handle_error")))).trace = s0.trace ++ [allocFailedEvent] := by
        change sf_1.trace = s0.trace ++ [allocFailedEvent]; rw [htr_fail, h, htr1_tr]
      refine SepWPp.panic (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hpan_err)
        (fun hm => by
          rw [← sepConj_assoc]
          exact allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _)
            ⟨allocFailedIn_of_trace_eq' htr_panic_eq,
              by rw [htr_panic_eq]; exact List.prefix_append s0.trace [allocFailedEvent]⟩ hm)
    · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
      wp_conv_pre => rw [alloc_post_neg_4k hptr0]
      apply SepWPp.pure_left; rintro ⟨_hptr_mod, htr_ok⟩
      apply SepWPp.of_sepWP (mid := entry + 80#64)
      wp_steps 1
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf_1])
      rw [h_1, hsp1]
      apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 128#64)
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
              memRegion (x.decA + 393#64) 7 ∗ tokenInitAt b ∗ reduceTableAt b ∗ A.pool) by
          rw [stackAt_extHook_eq_allocHook (s0.sp - 672#64),
            show s0.sp - 672#64 - 16384#64 = s0.sp - 17056#64 by bv_omega]
          dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat]
          refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w)))
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_2))))
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_3)))))
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro w_4))))))
          sep_frame)
        (decodedMessage_allocPv_setup_sepWP x.dec s0.sp x.decA (sf_1.readReg64 (Reg.gpr 0#5)) hsp0 hneed_lt _ _ _
          (by dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat]; rw [hentry]; simp [wp_norm, arm64_norm])
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
        dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat]
      refine pure_elim_focus_4k (pins.length = x.dec.pts.length) (fun hpins => ?_) (by sep_focus)
      have hpins16 : pins.length = 16 := by rw [hpins, hpts_len]
      cases hcol : (collectPointsVecsTotal x.dec 0 16 false []).1
      · have ⟨hall_ge, _⟩ := collectPointsVecs_false_bounds x.dec hpts_len hsort hcol
        apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 352#64)
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
                reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((x.decA + 392#64) ↦₈ 0#8) ∗
                  memRegion (x.decA + 393#64) 7)) by
            simp only [List.take_zero, ptSliceRefListAt, Nat.mul_zero, Nat.sub_zero,
              BitVec.add_zero, emp_sepConj]
            sep_frame)
          (collectPointsVecs_ok_loop_sepWP x.dec x.decA (sf_1.readReg64 (Reg.gpr 0#5)) s0.sp pins
            hpts_len hpins16 hneed_lt hlen_bound hall_ge hsp0 15 0 s2 0#64 _ _ (by decide)
            hpc2 hrun2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
            (fun s3 hpc3 hrun3 hsp3 htr3 _hx0_3 hx20_3 hx29_3 _hx30_3 => ?_))
        apply SepWP.done hpc3 hrun3
        conv => arg 6; ext sf P_f; rw [← sepConj_assoc]
        refine SepWPp.weaken_pre (by sep_frame)
          (decodedMessage_afterCollect_wpp_4k hb hA x.dec x.decA x.out (sf_1.readReg64 (Reg.gpr 0#5)) pins
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
              tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack by
            refine Entails.trans
              (sepConj_mono_right (sepConj_mono_left
                (sortedSetPtListPinAt_entails_sortedSetPtListOf A pins x.dec.pts x.decA hpins))) ?_
            refine Entails.pure_right htr_f ?_
            refine Entails.trans (show _ ⊢
              (sortedSetPtListOf A x.decA x.dec.pts ∗
                ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7) ∗
              (optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
                tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack) by sep_frame) ?_
            rw [show (0#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
            refine Entails.trans (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
            sep_frame)
          (SepWPp.done hpc_f hrun_f ⟨fun hm => by simpa only [sepConj_assoc] using hm, hsp_f, hcs_f⟩)
      · have hex_lt := exists_lt_necessaryPoints_of_collect_true x.dec hpts_len hcol
        apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
        refine SepWP.weaken_pre
          (show _ ⊢
            ((s0.sp - 624#64) ↦₆₄ 16#64) ∗ ((s0.sp - 608#64) ↦₆₄ 0#64) ∗
              sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
              memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
              (savedRegsAt s0.sp s0 ∗ ((s0.sp - 648#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((s0.sp - 632#64) ↦₆₄ x.out) ∗ ((s0.sp - 616#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                memRegion (s0.sp - 600#64) 384 ∗ memRegion (s0.sp - 216#64) 24 ∗
                interpolateScratchAt s0.sp ∗ memRegion (s0.sp - 672#64) 8 ∗
                memRegion (s0.sp - 120#64) 24 ∗ memRegion x.out vecHeaderBytes ∗
                A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗
                reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt (s0.sp - 672#64) extHookStack ∗
                (((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                  ((x.decA + 392#64) ↦₈ 0#8) ∗
                  memRegion (x.decA + 393#64) 7)) by sep_frame)
          (collectPointsVecs_none_loop_sepWP x.dec x.decA (sf_1.readReg64 (Reg.gpr 0#5)) s0.sp pins
            hpts_len hpins16 hneed_lt hlen_bound hsp0
            15 0 0 false s2 0#64 _ _ (by decide) (by decide) (Or.inr hex_lt)
            hpc2 hrun2 hsp2 hx0_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
            (fun s3 pvLenFinal hpc3 hrun3 hsp3 htr3 _hx29_3 _hx30_3 => ?_))
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
                  memRegion (x.decA + 393#64) 7 ∗ tokenInitAt b ∗ reduceTableAt b)) by
            sep_frame) ?_
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
                  memRegion (x.decA + 393#64) 7 ∗ tokenInitAt b ∗ reduceTableAt b)) by
            sep_frame) ?_
        refine SepWP.weaken_pre (sepConj_mono_left (memRegion_384_24_96_entails_504 s0.sp)) ?_
        refine SepWP.weaken_pre (by sep_frame)
          (decodedMessage_epilogue_from288_sepWP_core hA.dealloc s0 s0.sp x.out (sf_1.readReg64 (Reg.gpr 0#5))
            (BitVec.ofNat 64 x.dec.ptsNeeded) pvLenFinal hsp0 s3
            (sortedSetPtListPinAt A x.decA pins x.dec.pts ∗
              ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
              ((x.decA + 392#64) ↦₈ 0#8) ∗
              memRegion (x.decA + 393#64) 7 ∗ tokenInitAt b ∗ reduceTableAt b) _
            hpc3 hrun3 hsp3 (fun sf hpc_f hrun_f hsp_f htr_f hcs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        have htot := decodedMessageTotal_of_collect_true hcomp hpts_len hcol
        have htr_f_vr : traceVRegs sf = traceVRegs s0 := by rw [htr_f, htr3, htr2']
        rcases calleeSavedPreserved_of_gprs_traceVRegs hcs_f htr_f_vr with ⟨hcs_f, htr_f'⟩
        refine SepWPp.weaken_pre
          (show _ ⊢
            ⌜sf.trace = s0.trace⌝ ∗ optVecU8Of A x.out (decodedMessageTotal x.dec) ∗
              polyDecoderAt A x.decA x.dec ∗
              tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack by
            rw [htot]
            refine Entails.trans
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (sortedSetPtListPinAt_entails_sortedSetPtListOf A pins x.dec.pts x.decA hpins))))) ?_
            refine Entails.pure_right htr_f' ?_
            refine Entails.trans (show _ ⊢
              (sortedSetPtListOf A x.decA x.dec.pts ∗
                ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
                ((x.decA + 392#64) ↦₈ 0#8) ∗ memRegion (x.decA + 393#64) 7) ∗
              (optVecU8Of A x.out none ∗
                tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack) by sep_frame) ?_
            rw [show (0#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
            refine Entails.trans (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
            sep_frame)
          (SepWPp.done hpc_f hrun_f ⟨fun hm => by simpa only [sepConj_assoc] using hm, hsp_f, hcs_f⟩)
  · wp_conv_pre => simp only [↓reduceIte]
    have hout_split : memRegion x.out vecHeaderBytes =
        (∃∗ w0 : BitVec 64, x.out ↦₆₄ w0) ∗ memRegion (x.out + 8#64) 16 := by
      rw [show vecHeaderBytes = 8 + 16 from rfl,
        memRegion_split x.out 8 16 (by decide), ProofLib.memRegion_eight x.out]
    wp_conv_pre => rw [hout_split]
    decoded_message_fetches_range_ext b (Rust.withPanics ext) 32 20
    dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := s0.readReg64 .x30)
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    wp_steps 5
    have hnone_eq :
        (x.out ↦₆₄ 0xffff_ffff_ffff_ffff#64) ∗ memRegion (x.out + 8#64) 16 =
          optVecU8Of A x.out none := by unfold optVecU8Of noneCap; rfl
    refine SepWP.weaken_pre
      (show _ ⊢
        savedRegsAt s0.sp s0 ∗ memRegion (s0.sp - 672#64) 576 ∗
          stackAt (s0.sp - 672#64) extHookStack ∗
          (optVecU8Of A x.out none ∗ sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 1#8) ∗ memRegion (x.decA + 393#64) 7 ∗
            tokenInitAt b ∗ reduceTableAt b ∗ A.pool) by
        rw [← hnone_eq]; sep_frame)
      (decodedMessage_epilogue_ret_sepWP s0 s0.sp hsp0 _ _ _
        (by dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat]; rw [hentry]; simp [wp_norm, arm64_norm])
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
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack by
        rw [htot]
        refine Entails.pure_right htr_f' ?_
        refine Entails.trans (show _ ⊢
          (sortedSetPtListOf A x.decA x.dec.pts ∗
            ((x.decA + 384#64) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
            ((x.decA + 392#64) ↦₈ 1#8) ∗ memRegion (x.decA + 393#64) 7) ∗
          (optVecU8Of A x.out none ∗
            tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack) by sep_frame) ?_
        rw [show (1#8 : BitVec 8) = if x.dec.isComplete then 1#8 else 0#8 by rw [hcomp]; rfl]
        refine Entails.trans (sepConj_mono_left (reassemble_polyDecoderAt x.decA x.dec hpts_len hneed_lt)) ?_
        sep_frame)
      (SepWPp.done hpc_f hrun_f ⟨fun hm => by simpa only [sepConj_assoc] using hm, hsp_f, hcs_f⟩)

theorem polyDecoderDecodedMessage_ok_inImage_4k {img : Obj.Image}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodedMessageName)
      ((decodedMessageSpec A img.base).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (polyDecoderDecodedMessage_ok_4k hA)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.Poly.DecodedMessage
export LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofExt (
  polyDecoderDecodedMessage_ok_4k
  polyDecoderDecodedMessage_ok_inImage_4k
)
end CryptoVerification.SpqrV1.Poly.DecodedMessage
-- AUTO-BRIDGE END
