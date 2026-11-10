/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsaPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsg
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsh
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 2 (`HeaderSent`, `+508`) — Part H

Relocatable Block-`333` `<PolyEncoder>::from_pb` (`+9096`) and `<PolyDecoder>::from_pb`
(`+9384`) call helpers and `+9100` encoder-error branch.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open V1State.Chunked
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1
open LibsignalBinary.Proofs.SpqrV1.States
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced

set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit v2hsh_bv_add_add_lit

private theorem v2hsh_sepWPp_call_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  have h1 : SepWPp prog ret_pc s (P_step ∗ F)
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post x s sm ∗ F)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
    refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
      (fun R' hm => by
        rw [sepConj_assoc] at hm
        dsimp only [withLsCodeLoaded]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨hcl, hpre (F ∗ R') hm⟩)
      (fun sf code _ _ hpost => by
        dsimp only [withLsCodeLoaded] at hpost
        rw [hexit_eq] at hpost
        exact not_satisfies_false_sepConj hpost)
      (fun sm _ hm_f => Satisfies.mono (sepConj_mono_left (hpan sm)) hm_f)
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf _ _ hpost => by
        dsimp only [withLsCodeLoaded] at hpost
        rw [hoom_eq] at hpost
        exact (not_satisfies_false_sepConj hpost).elim)
  intro R' hm hL
  rcases h1 R' hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan_out | hoom_out⟩
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcl.of_keepsFrozen hsteps.keepsFrozen) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan_out)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

/-! ## `<PolyEncoder>::from_pb` Call Helper at `+9096` -/

theorem v2hsh_encoder_call_9096_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (henc : EncoderFromPbPlacedOkExt A ext)
    (s0 s : State) (target_pc fsp out d0 pa1 ca3 pbA epoch : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (R Rest : SepProp)
    (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hpc : s.pc = lsmpl.base 333 + 9096#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1792#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = d0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = epoch)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 333 + 9100#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧
       s1.readReg64 .x19 = out ∧
       s1.readReg64 .x21 = fsp + 1392#64 ∧
       s1.readReg64 .x22 = d0 ∧
       s1.readReg64 .x23 = pa1 ∧
       s1.readReg64 .x24 = fsp + 1888#64 ∧
       s1.readReg64 .x25 = fsp + 1792#64 ∧
       s1.readReg64 .x26 = ca3 ∧
       s1.readReg64 .x27 = pbA ∧
       s1.readReg64 .x28 = epoch ∧
       TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         resultPolyEncoderFromPbAt A (fsp + 1888#64) (fromPbResult pbEnc) ∗
         memRegion (fsp + 1792#64) protoPolynomialEncoderSize ∗
         A.pool ∗
         Rest)
        post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A (fsp + 1792#64) pbEnc ∗
        A.pool ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hsub := v2hse2_sub_ok_encoder_from_pb_placed henc
  have hstep := SepWP.weaken_pre (Entails.of_eq (show
      stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A (fsp + 1792#64) pbEnc ∗
        A.pool ∗ Rest =
      (stackAt fsp encoderFromPbStack ∗
       memRegion (fsp + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A (fsp + 1792#64) pbEnc ∗
       A.pool) ∗ Rest by ac_rfl))
    (v2hse2_bl_encoder_9096_to_32996_placed (ext := ext) s0 s fsp out d0 ca3 pbA _
      hpc hrun hsp hx0 hx1 hx19 hx22 hx24 hx25 hx26 hx27 htr)
  refine SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono hstep fun sm Pm hpc_m hrun_m ⟨hPm,
      hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hlr_m, htr_m⟩ hcl_m =>
      SepWPp.weaken_pre hPm (by
        rw [hx21] at hx21_m; rw [hx23] at hx23_m; rw [hx28] at hx28_m
        have hsp_align_m : sm.spAligned = true := by
          unfold State.spAligned
          rw [hsp_m]
          exact hfsp_align
        refine v2hsh_sepWPp_call_lscl hsub
          (x := EncoderFromPbGhost.mk (fsp + 1888#64) (fsp + 1792#64) pbEnc)
          (F := Rest)
          hcl_m hpc_m hrun_m hsp_align_m hlr_m
          (fun R' hm => ?_)
          (fun sf => v2hsh_onPanic_shift htr_m sf)
          (fun _ _ => rfl)
          (fun sf hpcf hrunf hspf hcsf hcl_sf => ?_)
        · have hpre_ent :
              stackAt fsp encoderFromPbStack ∗
                memRegion (fsp + 1888#64) polyEncoderSize ∗
                protoPolynomialEncoderAt A (fsp + 1792#64) pbEnc ∗
                A.pool ⊢
              (encoderFromPbSpec A).pre
                (EncoderFromPbGhost.mk (fsp + 1888#64) (fsp + 1792#64) pbEnc) sm := by
            dsimp only [encoderFromPbSpec]
            rw [hsp_m]
            exact Entails.pure_right ⟨hx0_m, hx1_m, hpts_len⟩ (Entails.of_eq (by ac_rfl))
          exact Satisfies.mono (sepConj_mono_left hpre_ent) hm
        · dsimp only [encoderFromPbSpec]
          rw [hsp_m, sepConj_assoc]
          apply SepWPp.pure_elim; intro htr_sf
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (hnext sf hpcf hrunf hcl_sf ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
          · rw [hspf, hsp_m]
          · rw [hcsf.1, hx19_m]
          · rw [hcsf.2.2.1, hx21_m]
          · rw [hcsf.2.2.2.1, hx22_m]
          · rw [hcsf.2.2.2.2.1, hx23_m]
          · rw [hcsf.2.2.2.2.2.1, hx24_m]
          · rw [hcsf.2.2.2.2.2.2.1, hx25_m]
          · rw [hcsf.2.2.2.2.2.2.2.1, hx26_m]
          · rw [hcsf.2.2.2.2.2.2.2.2.1, hx27_m]
          · rw [hcsf.2.2.2.2.2.2.2.2.2.1, hx28_m]
          · exact ⟨htr_sf.trans htr_m.1, hcsf.2.2.2.2.2.2.2.2.2.2.2.trans htr_m.2⟩))

/-! ## `<PolyDecoder>::from_pb` Call Helper at `+9384` -/

theorem v2hsh_decoder_call_9384_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdec : DecoderFromPbPlacedOkExt A ext)
    (s0 s : State) (target_pc fsp out x20_val x21_val ca3 x28_val : BitVec 64)
    (pbDec : ProtoPolynomialDecoder) (R Rest : SepProp)
    (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64)
    (hx1 : s.readReg64 .x1 = fsp + 1848#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = x21_val)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = x28_val)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 333 + 9388#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧
       s1.readReg64 .x19 = out ∧
       s1.readReg64 .x20 = x20_val ∧
       s1.readReg64 .x21 = x21_val ∧
       s1.readReg64 .x22 = fsp + 1888#64 ∧
       s1.readReg64 .x23 = fsp + 848#64 ∧
       s1.readReg64 .x25 = fsp + 1792#64 ∧
       s1.readReg64 .x26 = ca3 ∧
       s1.readReg64 .x28 = x28_val ∧
       TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         resultPolyDecoderFromPbAt A (fsp + 1888#64) (decoderFromPbResult pbDec) ∗
         memRegion (fsp + 1848#64) protoPolynomialDecoderSize ∗
         A.pool ∗
         Rest)
        post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyDecoderSize ∗
        protoPolynomialDecoderAt A (fsp + 1848#64) pbDec ∗
        A.pool ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hsub := v2hsd_sub_ok_decoder_from_pb_placed hdec
  have hstep := SepWP.weaken_pre (Entails.of_eq (show
      stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyDecoderSize ∗
        protoPolynomialDecoderAt A (fsp + 1848#64) pbDec ∗
        A.pool ∗ Rest =
      (stackAt fsp encoderFromPbStack ∗
       memRegion (fsp + 1888#64) polyDecoderSize ∗
       protoPolynomialDecoderAt A (fsp + 1848#64) pbDec ∗
       A.pool) ∗ Rest by ac_rfl))
    (v2hse3_bl_decoder_9384_to_35448_placed (ext := ext) s0 s fsp out x20_val x21_val ca3 x28_val _
      hpc hrun hsp hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr)
  refine SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono hstep fun sm Pm hpc_m hrun_m ⟨hPm,
      hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx25_m, hx26_m, hx28_m, hlr_m, htr_m⟩ hcl_m =>
      SepWPp.weaken_pre hPm (by
        have hsp_align_m : sm.spAligned = true := by
          unfold State.spAligned
          rw [hsp_m]
          exact hfsp_align
        refine v2hsh_sepWPp_call_lscl hsub
          (x := ⟨fsp + 1888#64, fsp + 1848#64, pbDec⟩)
          (F := Rest)
          hcl_m hpc_m hrun_m hsp_align_m hlr_m
          (fun R' hm => ?_)
          (fun sf => v2hsh_onPanic_shift htr_m sf)
          (fun _ _ => rfl)
          (fun sf hpcf hrunf hspf hcsf hcl_sf => ?_)
        · have hpre_ent :
              stackAt fsp encoderFromPbStack ∗
                memRegion (fsp + 1888#64) polyDecoderSize ∗
                protoPolynomialDecoderAt A (fsp + 1848#64) pbDec ∗
                A.pool ⊢
              (decoderFromPbSpec A).pre ⟨fsp + 1888#64, fsp + 1848#64, pbDec⟩ sm := by
            dsimp only [decoderFromPbSpec, decoderFromPbStack, encoderFromPbStack]
            rw [hsp_m]
            exact Entails.pure_right ⟨hx0_m, hx1_m⟩ (Entails.of_eq (by ac_rfl))
          exact Satisfies.mono (sepConj_mono_left hpre_ent) hm
        · dsimp only [decoderFromPbSpec, decoderFromPbStack, encoderFromPbStack]
          rw [hsp_m, sepConj_assoc]
          apply SepWPp.pure_elim; intro htr_sf
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (hnext sf hpcf hrunf hcl_sf ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
          · rw [hspf, hsp_m]
          · rw [hcsf.1, hx19_m]
          · rw [hcsf.2.1, hx20_m]
          · rw [hcsf.2.2.1, hx21_m]
          · rw [hcsf.2.2.2.1, hx22_m]
          · rw [hcsf.2.2.2.2.1, hx23_m]
          · rw [hcsf.2.2.2.2.2.2.1, hx25_m]
          · rw [hcsf.2.2.2.2.2.2.2.1, hx26_m]
          · rw [hcsf.2.2.2.2.2.2.2.2.2.1, hx28_m]
          · exact ⟨htr_sf.trans htr_m.1, hcsf.2.2.2.2.2.2.2.2.2.2.2.trans htr_m.2⟩))

/-! ## `<PolyEncoder>::from_pb = Err` Branch (`+9100 -> +9212 -> +9228 -> ret`) -/

theorem v2hsh_branch_enc_err_9100_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (err : PolynomialError) (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = d_w0)
    (hx26_1 : s1.readReg64 .x26 = u8) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (s0.sp - 2400#64 + 1888#64) (.error err) ∗
        memRegion (s0.sp - 2400#64 + 1792#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 1848#64) 40 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 1392#64) 400 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A dk u8 u16 u24
  have hd_r : vecU8Payload A u48 pa1 auth.rootKey ⊢ vecCapPtrDealloc A u48 pa1 := by
    rw [hu48]; exact vecU8Payload_entails_dealloc A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
  have hd_m : vecU8Payload A u72 pa2 auth.macKey ⊢ vecCapPtrDealloc A u72 pa2 := by
    rw [hu72]; exact vecU8Payload_entails_dealloc A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
  have hek_eq :
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 =
      v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 := rfl
  let Frame9100 : SepProp :=
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 2288#64) 16 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9100 :
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
      stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 ∗
        vecCapPtrDealloc A u48 pa1 ∗ vecCapPtrDealloc A u72 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
        A.pool ∗ Frame9100 := by
    rw [hek_eq]; dsimp only [Frame9100]
    refine Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey ∗
      v4b_vecU8Heap A dk u8 u16 u24 ∗
      (stackAt fsp encoderFromPbStack ∗
       resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗
       ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 ∗
       A.pool ∗
       (memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hd_r (sepConj_mono hd_m (sepConj_mono_left hd_dk)))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9100 ?_
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 9212#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗
      memRegion (fsp + 1888#64) 400 ∗
      ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      memRegion (fsp + 1264#64) 80 ∗ A.pool ∗ Frame9100)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s2 s0)
    (v2hse2_enc_err_9100_to_9212_placed hA s0 s1 fsp out d_w0 u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80
      err Frame9100 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, htr2⟩
  let Frame9212 : SepProp :=
    memRegion (fsp + 1888#64) 400 ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    memRegion (fsp + 1264#64) 80 ∗
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 2288#64) 16 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 192 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9212 :
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) 400 ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        memRegion (fsp + 1264#64) 80 ∗ A.pool ∗ Frame9100) =
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        v2hsc_optProtoPolyDecoderHeap A optDec d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212) := by
    dsimp only [Frame9100, Frame9212]
    rw [v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32,
        v2hstop_optProtoDecoderHeap_eq_v2hsc A optDec d_w0 d_w8 d_w16 d_w24 d_w32]
    ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre9212) ?_
  refine seq_clean_lscl hcl2
    (mid := lsmpl.base 333 + 9228#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗
      v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212)
    (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧
      s3.readReg64 .x23 = 0#64 ∧ TraceCalleeSaved s3 s0)
    (v2hsc_cleanup_9212_to_9228_placed hA s0 s2 fsp out optDec d_w0 d_w8 d_w16
      (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 u72 Frame9212
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2) ?_
  intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx23_3, htr3⟩
  have h960 := v2hsh_memRegion_1344_960_collapse fsp
  have hcol2304 := v2hsh_collapse_2304_from_9228 fsp u8 u16 u24 u40 u48 u72 u80 pa2
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  have hpre9228 :
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) := by
    rw [← v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32]
    dsimp only [Frame9212]
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16) ∗
       (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗ memRegion (fsp + 1264#64) 80)) ∗
      (stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left
      (Entails.trans (sepConj_mono_left h960)
        (Entails.trans (Entails.of_eq (by ac_rfl)) hcol2304))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre9228 ?_
  have hx23_lo : (s3.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx23_3]; rfl
  have h9228 := v2hs_err_cleanup_9228_placed (A := A) (F := F) (ext := ext)
    s0 s3 out .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx23_lo htr3
  exact SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
    ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

end CryptoVerification.SpqrV1.States.FromPb
