/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6e
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part E

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant6e.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
  v6hr_stagingSlotsPre v6hr_stagingSlotsPost v6hr_decWordsAt
  v6hr_stackRest10000 v6hr_decHeap epilogueStackSlots epilogueStackGaps epilogueOutFull
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit
  v6hr_bv_add_lit_add_lit
  v6hr_bfm_reconstruct_64 v6hr_bfm_reconstruct_64'

/-! ## Decoder Call (`+9936 -> +10000`) and Error/Ok Branches -/

theorem v6hr_sepWPp_bind_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm Pm →
      SepWPp prog target sm Pm Q Qp) :
    SepWPp prog target s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := h1 R hm hL
  rcases hout with ⟨hpcm, hrunm, Pm, hpm, hQm⟩ | hpan | hoom
  · have hcl_m : LibsignalCodeLoaded lsmpl sm.mem :=
      LibsignalCodeLoaded.of_keepsFrozen hcl hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ := h2 sm Pm hpcm hrunm hcl_m hQm R hpm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem v6hr_sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  v6hr_sepWPp_bind_lscl hcl (SepWPp.of_sepWP_ret h1) fun sm Pm hpcm hrunm hcl_m ⟨hPm, hQr⟩ =>
    SepWPp.weaken_pre hPm (h2 sm hpcm hrunm hcl_m hQr)

theorem v6hr_step_9936_dec_none_to_10416_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 : BitVec 64) (P : SepProp)
    (hl1 : l1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = noneCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10416#64) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0) := by
  have hne_l1 := cap_add_one_beq_zero_false hl1
  dsimp only [noneCap] at hx28_1
  change s1.pc = (blkPl_333).base + 9936#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10416#64) s1 P _
  wp_steps
  wp_done

theorem v6hr_step_9936_dec_some_to_35448_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 ptsCap ptsPtr w120 : BitVec 64)
    (d : ProtoPolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1 : l1.toNat < 2 ^ 63)
    (h1 : d.pts.length ≤ ptsCap.toNat) (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : EncoderFromPb.loByte w120 = boolByte d.isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d.ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d.polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 d.pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.pool ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          (memRegion ((s0.sp - 2400#64) + 1888#64) polyDecoderSize ∗
           protoPolynomialDecoderAt A ((s0.sp - 2400#64) + 1392#64) d ∗
           A.pool ∗ stackAt (s0.sp - 2400#64) decoderFromPbStack) ∗
          ((((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
           (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗ Rest)) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        s2.readReg64 .x1 = (s0.sp - 2400#64) + 1392#64 ∧
        s2.readReg64 .x30 = lsmpl.base 333 + 10000#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = p1_new ∧
        s2.readReg64 .x26 = l1 ∧
        s2.readReg64 .x27 = c0 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hne_l1 := cap_add_one_beq_zero_false hl1
  have hpts_lt : ptsCap.toNat < 2 ^ 63 := by omega
  have hne_c3 := cap_add_one_beq_zero_false hpts_lt
  have hw11 : (d.ptsNeeded.zeroExtend 64).setWidth 32 = d.ptsNeeded := by bv_kernel
  have hw12 : (d.polys.zeroExtend 64).setWidth 32 = d.polys := by bv_kernel
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (v6hr_memRegion_40_split ((s0.sp - 2400#64) + 1392#64)))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u32
  apply ProofLib.SepWP.exists_left; intro u28
  apply ProofLib.SepWP.exists_left; intro u24
  apply ProofLib.SepWP.exists_left; intro u16
  apply ProofLib.SepWP.exists_left; intro u8
  apply ProofLib.SepWP.exists_left; intro u0
  change s1.pc = (blkPl_333).base + 9936#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 376) s1 _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpack := v6hr_protoPolynomialDecoderAt_pack A ((s0.sp - 2400#64) + 1392#64)
      d ptsCap ptsPtr w120 h1 h2 h3 hw120
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
    dsimp only [polyDecoderSize, decoderFromPbStack]
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((((s0.sp - 2400#64 + 1392#64) ↦₆₄ ptsCap) ∗
          ((s0.sp - 2400#64 + 1400#64) ↦₆₄ ptsPtr) ∗
          ((s0.sp - 2400#64 + 1408#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
          ((s0.sp - 2400#64 + 1416#64) ↦₃₂ d.ptsNeeded) ∗
          ((s0.sp - 2400#64 + 1420#64) ↦₃₂ d.polys) ∗
          ((s0.sp - 2400#64 + 1424#64) ↦₆₄ w120)) ∗
         (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24))) ∗
        (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
         A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (by ac_rfl))
  · dsimp only [blkPl_333, Obj.MultiPlacedLib.blockPlacement]
    wp_done

theorem v6hr_step_9936_dec_some_to_10000_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdec : DecoderFromPbPlacedOkExt A ext)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out c0 p1_new l1 ptsCap ptsPtr w120 : BitVec 64)
    (d : ProtoPolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1 : l1.toNat < 2 ^ 63)
    (h1 : d.pts.length ≤ ptsCap.toNat) (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : EncoderFromPb.loByte w120 = boolByte d.isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d.ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d.polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 d.pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10000#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (decoderFromPbResult d) ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine v6hr_sepWPp_seq_clean_lscl hcl1
    (v6hr_step_9936_dec_some_to_35448_placed s0 s1 out c0 p1_new l1 ptsCap ptsPtr w120 d Rest
      hsp0_align hl1 h1 h2 h3 hw120 hpc1 hrun1 hsp1 hx11_1 hx12_1 hx19_1 hx23_1 hx24_1
      hx25_1 hx26_1 hx27_1 hx28_1 htr1) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx1_2, hx30_2, hx19_2, hx21_2, hx26_2, hx27_2, htr2⟩
  have hsp2_align : s2.spAligned = true := by
    change (s2.sp &&& 15#64 == 0#64) = true
    rwa [hsp2]
  refine v6hr_sepWPp_call_entails hdec
    ⟨(s0.sp - 2400#64) + 1888#64, (s0.sp - 2400#64) + 1392#64, d⟩
    s2 _ _ (statesFromPbOnPanic s0) _ hpc2 hrun2 hsp2_align hx30_2 ?_ ?_ (fun _ _ => rfl) ?_
  · dsimp only [withLsCodeLoaded, decoderFromPbSpec]
    rw [hsp2, sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s2.mem⌝, ← sepConj_assoc]
    exact Entails.pure_right hcl2 (Entails.pure_right ⟨hx0_2, hx1_2⟩ (Entails.refl _))
  · intro sf
    exact v6hr_onPanic_frame_entails htr2
  · intro sf hpcf hrunf hspf hcsf
    rcases hcsf with ⟨hx19_f, _, hx21_f, _, _, _, _, hx26_f, hx27_f, _, _, hvregs_f⟩
    dsimp only [withLsCodeLoaded, decoderFromPbSpec]
    rw [sepConj_assoc]
    apply ProofLib.SepWP.pure_elim; intro htr_f
    apply ProofLib.SepWP.done hpcf hrunf
    refine ⟨?_, by rw [hspf, hsp2], by rw [hx19_f, hx19_2], by rw [hx21_f, hx21_2],
      by rw [hx26_f, hx26_2], by rw [hx27_f, hx27_2], ⟨htr_f.trans htr2.1, hvregs_f.trans htr2.2⟩⟩
    rw [hsp2]
    dsimp only [protoPolynomialDecoderSize, decoderFromPbStack]
    exact Entails.of_eq (by ac_rfl)

theorem v6hr_step_10000_err_to_10492_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 : BitVec 64) (e : PolynomialError) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10000#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10492#64) s1
      (resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error e) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0) := by
  have h1888 : (s0.sp - 2400#64) + 1888#64 = s0.sp - 512#64 := by bv_omega
  have herr := v6hr_resultPolyDecoder_err_entails_400 A ((s0.sp - 2400#64) + 1888#64) e
  unfold resultPolyDecoderFromPbAt at herr ⊢
  dsimp only [noneCap] at ⊢
  rw [h1888] at herr ⊢
  simp only [sepConj_assoc]
  change s1.pc = (blkPl_333).base + 10000#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10492#64) s1 _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · refine Entails.trans
      (Entails.of_eq (show _ =
        (((s0.sp - 512#64) ↦₆₄ noneCap) ∗
         ((s0.sp - 512#64 + resultPolyDecoderErrByteOff) ↦₈ polynomialErrorByte e) ∗
         memRegion (s0.sp - 512#64 + 9#64) resultPolyDecoderErrTailSize) ∗ Rest by
        dsimp only [noneCap]; ac_rfl)) ?_
    exact sepConj_mono_left herr
  · wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlaced
  (v6hr_sepWPp_seq_clean_lscl
   v6hr_step_9936_dec_none_to_10416_placed
   v6hr_step_9936_dec_some_to_35448_placed
   v6hr_step_9936_dec_some_to_10000_placed
   v6hr_step_10000_err_to_10492_placed)

end CryptoVerification.SpqrV1.States.FromPb
