/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbProof
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::into_pb`: `withLsCodeLoaded` Proof

Proves `decoder_into_pb_cl_placed_ok_ext` and `decoder_into_pb_cl_placed_ok_x` on Block `377` under
`[LibsignalPlacement]` with `withLsCodeLoaded lsmpl`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
  (vecPtOf vecPtListOf sortedSetPtOf_eq_vecPtOf sortedSetPtListOf_eq_vecPtListOf
   dropGluePoly16Stack DropGlueSortedSetPt16Ghost dropGlueSortedSetPt16Spec)
open CryptoVerification.CodeLayout
open CryptoGames.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  bv384_toNat bv8_toNat
  off_8_add_8 off_16_add_8 off_24_add_4 off_24_add_8 off_32_add_8 off_40_add_8
  off_48_add_8 off_56_add_8 off_64_add_8 off_72_add_8 off_80_add_8 off_88_add_8
  off_96_add_8 off_104_add_8 off_112_add_8 off_120_add_8 off_128_add_8
  off_136_add_8 off_144_add_8 sub_160_add_160
  truncate_32_ofNat_64 setWidth_32_ofNat_64 truncate_8_zeroExtend_64
  setWidth_8_setWidth_64 setWidth_8_setWidth_32_setWidth_64

/-- Specialize a `withLsCodeLoaded` `subroutine_ok` contract at a call site whose memory `m`
    already satisfies `LibsignalCodeLoaded lsmpl m` (`withMemEq m spec`). -/
theorem subroutine_ok_withMemEq_of_withLsCodeLoaded [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α} {m : Memory}
    (hcallee : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono hcallee
    (fun _ _ s0 hp => by
      have ⟨hm, hpre⟩ := extract_withMemEq hp
      have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hm ▸ hcl
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- Sequence a `SepWPp` reaching an intermediate PC `mid` before a continuation `SepWPp` to `ret`,
    threading `LibsignalCodeLoaded lsmpl` via `Steps.keepsFrozen`. -/
theorem sepWPp_seq_mid_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm Pm →
      SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps1, hout1⟩ := h1 R hm hL
  rcases hout1 with ⟨hpcm, hrunm, Pm, hmm, hqm⟩ | hpan | hoom
  · have hclm : LibsignalCodeLoaded lsmpl sm.mem := hcl.of_keepsFrozen hsteps1.keepsFrozen
    obtain ⟨sf, hsteps2, hout2⟩ := h2 sm Pm hpcm hrunm hclm hqm R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inr hoom)⟩

private def withSaved19_20_setLr (s0 : State) (decA out lr : BitVec 64) : State :=
  ((s0.writeReg64 .x19 decA).writeReg64 .x20 out).writeReg64 (Reg.gpr 30#5) lr

private theorem withSaved19_20_setLr_lr (s0 : State) (decA out lr : BitVec 64) :
    (withSaved19_20_setLr s0 decA out lr).readReg64 (Reg.gpr 30#5) = lr := by
  simp [withSaved19_20_setLr, wp_norm]

private theorem withSaved19_20_setLr_x19 (s0 : State) (decA out lr : BitVec 64) :
    (withSaved19_20_setLr s0 decA out lr).readReg64 .x19 = decA := by
  simp [withSaved19_20_setLr, wp_norm]

private theorem withSaved19_20_setLr_x20 (s0 : State) (decA out lr : BitVec 64) :
    (withSaved19_20_setLr s0 decA out lr).readReg64 .x20 = out := by
  simp [withSaved19_20_setLr, wp_norm]

private theorem withSaved19_20_setLr_x28 (s0 : State) (decA out lr : BitVec 64) :
    (withSaved19_20_setLr s0 decA out lr).readReg64 .x28 = s0.readReg64 .x28 := by
  simp [withSaved19_20_setLr, wp_norm]

private theorem withSaved19_20_setLr_trace (s0 : State) (decA out lr : BitVec 64) :
    (withSaved19_20_setLr s0 decA out lr).trace = s0.trace := rfl

private theorem withSaved19_20_setLr_vregs (s0 : State) (decA out lr : BitVec 64) :
    calleeSavedVRegs (withSaved19_20_setLr s0 decA out lr) = calleeSavedVRegs s0 := rfl

private theorem withSaved19_20_setLr_onPanic (s0 sf : State) (decA out lr : BitVec 64) :
    intoPbOnPanic (withSaved19_20_setLr s0 decA out lr) sf = intoPbOnPanic s0 sf := rfl

/-- Placed epilogue of `<PolyDecoder>::into_pb` (`+328` to `s0.lr`) with `withLsCodeLoaded` on `hdrop`. -/
theorem into_pb_epilogue_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
    (s0 : State) (fsp out decA : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 160#64))
    (ptsNeeded polys : BitVec 32) (v4 : BitVec 64) (isComplete : BitVec 8)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (vecs : List (List Pt)) (hvecs : vecs.length = NUM_POLYS)
    (w0 w1 w2 w5 w6 w7 v11 d0 d1 d2 d3 d4 : BitVec 64) (s : State) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_377).base + 328#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64) (hx19 : s.readReg64 .x19 = decA) (hx20 : s.readReg64 .x20 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
        ((fsp + 24#64) ↦₃₂ ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ polys) ∗
        ((fsp + 32#64) ↦₈ isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w5) ∗ ((fsp + 48#64) ↦₆₄ w6) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A decA vecs ∗ memRegion (decA + 384#64) 16 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢
          (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
          ((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys) ∗
          ((out + 32#64) ↦₈ isComplete) ∗ memRegion (out + 33#64) 7 ∗
          memRegion decA 400 ∗ A.pool ∗ stackAt s0.sp decoderIntoPbStack ∗ Frame) ∧
        sf.sp = s0.sp ∧
        sf.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) ∧
        sf.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
        sf.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
        sf.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
        sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
        sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
        sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
        sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
        sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
        sf.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sf.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5) ∧
        sf.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) := by
  conv => arg 4; rw [
    ← sepConj_assoc ((fsp + 24#64) ↦₃₂ ptsNeeded) ((fsp + 28#64) ↦₃₂ polys),
    pointsTo32_off24_merge64 fsp ptsNeeded polys,
    ← sepConj_assoc ((fsp + 32#64) ↦₈ isComplete) ((fsp + 33#64) ↦ₛ (unpack64 v4).tail),
    pointsTo64_off32_merge_low8 fsp v4 isComplete]
  wp_steps_lscl (lsmpl.base 264)
  have hdrop_call := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop ‹LibsignalCodeLoaded lsmpl _›
  simp only [withMemEq, dropGlueSortedSetPt16Spec, BitVec.ofNat_eq_ofNat] at hdrop_call
  wp_call hdrop_call (⟨decA, vecs⟩ : DropGlueSortedSetPt16Ghost); wp_steps
  have hsp_ret : fsp + 160#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  conv => arg 3; rw [hsp_ret]
  conv => arg 4; rw [hsp]
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl))
    (into_pb_epilogue_post_entails A s0.sp fsp out decA hfsp.eq ptsNeeded polys v4 isComplete
      w0 w1 w2 w5 w6 w7 v11 (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) Frame)) (by wp_done)

/-- Placed prologue and header initialization of `<PolyDecoder>::into_pb` (`+0 -> +148`, or OOM panic at `+396`)
    threading `LibsignalCodeLoaded lsmpl`. -/
theorem into_pb_prologue_and_init_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp out decA : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 160#64))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (ptsNeeded : Nat) (isComplete : Bool)
    (v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19 : BitVec 64) (Frame : SepProp)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_377).base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out) (hx1 : s0.readReg64 .x1 = decA)
    (hnext : ∀ (sm : State) (ptr_pts : BitVec 64),
      LibsignalCodeLoaded lsmpl sm.mem →
      ptr_pts ≠ 0 → sm.pc = (blkPl_377).base + 148#64 → sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 → sm.readReg64 .x19 = decA → sm.readReg64 .x20 = out →
      sm.readReg64 .x22 = 0#64 → sm.readReg64 .x23 = 24#64 → sm.readReg64 .x24 = 1#64 →
      sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ memRegion (decA + 384#64) 16 ∗
          A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s0
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
        ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗ ((fsp + 104#64) ↦₆₄ v13) ∗
        ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗ ((fsp + 128#64) ↦₆₄ v16) ∗
        ((fsp + 136#64) ↦₆₄ v17) ∗ ((fsp + 144#64) ↦₆₄ v18) ∗ ((fsp + 152#64) ↦₆₄ v19) ∗
        ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗ ((decA + 392#64) ↦₈ boolByte isComplete) ∗
        memRegion (decA + 393#64) 7 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hshim : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec := SpqrV1.Alloc.spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := SpqrV1.Alloc.spqr_hook_ok_of_mem halloc_sat
  simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay384 : LayoutOk 384 8 := ⟨by decide, hpow8, by decide⟩
  refine SepWPp.seq_frozen (mid := (blkPl_377).base + 64#64)
    (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl0 ?_
  wp_step; (conv => arg 3; simp only [← hfsp.eq])
  wp_steps; wp_apply; wp_steps; (conv => arg 4; simp only [← h_1]); wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl_sf1
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun htr_oom => ?_
    refine SepWPp.seq_clean (mid := (blkPl_377).base + 396#64)
      (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗
        ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
        ((decA + 392#64) ↦₈ boolByte isComplete) ∗ memRegion (decA + 393#64) 7 ∗ Frame)
      (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
      (by wp_steps; wp_done)
      (fun sm hpcm hrunm htrm => into_pb_panic_396_placed h_panic s0 sm _ R hpcm hrunm htrm)
  · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
    have hsp_sf1 : sf_1.sp = fsp := hsp_sf.trans h_1
    conv => arg 4; simp only [h_1, hsp_sf1]
    let ptr_pts := sf_1.readReg64 (Reg.gpr 0#5)
    conv => arg 4; rw [pointsTo64_off24_split32 fsp v3, pointsTo64_off32_split_low8 fsp v4]
    refine SepWPp.seq_frozen (mid := (blkPl_377).base + 148#64)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl_sf1 ?_
    refine SepWP.mono (post := fun sm Pm =>
        (Pm ⊢ (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ memRegion (decA + 384#64) 16 ∗
          A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x29 = fsp + 64#64 ∧ sm.readReg64 .x19 = decA ∧
        sm.readReg64 .x20 = out ∧ sm.readReg64 .x22 = 0#64 ∧ sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧ sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) ?_ ?_
    · wp_steps
      have htail := decA_tail_rejoin_16 decA (BitVec.ofNat 64 ptsNeeded) (boolByte isComplete)
      refine SepWP.weaken_pre (P' :=
        (((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
          ((decA + 392#64) ↦₈ boolByte isComplete) ∗ memRegion (decA + 393#64) 7) ∗
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) (Entails.of_eq (by ac_rfl)) ?_
      exact SepWP.weaken_pre (Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))) (by wp_done)
    · intro sm Pm hpcm hrunm ⟨hent, hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx24m, hx28m, htrm, hvregsm⟩ hclm
      exact SepWPp.weaken_pre hent
        (hnext sm ptr_pts hclm hoom hpcm hrunm hspm hx29m hx19m hx20m hx22m hx23m hx24m hx28m htrm hvregsm)

theorem decoder_into_pb_cl_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdrop : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A))) :
    subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (blkPl_377).base (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, decA, dec⟩ R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [decoderIntoPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion out protoPolynomialDecoderSize ∗ polyDecoderAt A decA dec ∗
      A.pool ∗ stackAt s0.sp decoderIntoPbStack, R, by simpa [sepConj_assoc] using hmem, ?_⟩
  dsimp only [withLsCodeLoaded, decoderIntoPbSpec, polyDecoderAt, polyDecoderPtsNeededOff,
    polyDecoderIsCompleteOff, polyDecoderPadOff, polyDecoderPadSize, protoPolynomialDecoderSize,
    polyDecoderSize, BitVec.ofNat_eq_ofNat] at *
  let fsp := s0.sp - 160#64
  have hfsp : HiddenEq fsp (s0.sp - 160#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 160#64 hsp0 (by decide)
  conv => arg 4; rw [stackAt_decoderIntoPb_split s0.sp, ← hfsp.eq, stackAt_dropGluePoly16_split_bottom fsp]
  conv => arg 4; simp only [sepConj_assoc]
  refine SepWPp.weaken_pre (P' :=
      ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗ memRegion out 40 ∗ cells fsp 20 ∗
      sortedSetPtListOf A decA dec.pts ∗ ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((decA + 392#64) ↦₈ boolByte dec.isComplete) ∗ memRegion (decA + 393#64) 7 ∗
      A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack) (Entails.of_eq (by ac_rfl)) ?_
  refine sepWPp_elim_pure fun ⟨hpts_len, _⟩ => ?_
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; simp only [memRegion_40_split out, cells20_fsp_eq fsp, sepConj_assoc, sepExists_sepConj_left]
  conv => arg 4; simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun d3 => SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun v0 =>
    SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 =>
    SepWPp.exists_elim fun v7 => SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 => SepWPp.exists_elim fun v12 =>
    SepWPp.exists_elim fun v13 => SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 => SepWPp.exists_elim fun v18 =>
    SepWPp.exists_elim fun v19 => ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (into_pb_prologue_and_init_cl_placed h_panic hshim_sat halloc_sat s0 fsp out decA hfsp hfsp_align
      dec.ptsNeeded dec.isComplete v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19
      (vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗ (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗
        ((out + 16#64) ↦₆₄ d2) ∗ ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 88#64) ↦₆₄ v11) ∗ memRegion (fsp - 4128#64) 32) hcl0 ‹_› ‹_› ‹_› ‹_› ?_)
  intro s1 ptr_pts hcl1 hptr_pts hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
  let s_ref328 := withSaved19_20_setLr s0 decA out ((blkPl_377).base + 328#64)
  have hrem_len : (dec.pts.map SortedSetPt.vec).length = 16 := by simp [hpts_len, NUM_POLYS, CHUNK_SIZE]
  have hrem_ne : dec.pts.map SortedSetPt.vec ≠ [] := by intro h; simp [h] at hrem_len
  let Frame_loop : SepProp :=
    ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
      ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
      ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
      ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
      (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
      ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
      memRegion (decA + 384#64) 16 ∗ A.live ptr_pts 384 8 ∗ memRegion (fsp - 4128#64) 32
  let Q328 : State → SepProp → Prop := fun s2 P2 =>
    ∃ w40 w48 w56 : BitVec 64,
      (P2 ⊢
        (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
          ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
          arrayAt (fun pts addr => vecPtOf A addr pts) 24 decA (dec.pts.map SortedSetPt.vec) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
            ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame_loop) ∧
      s2.sp = fsp ∧ s2.readReg64 .x29 = fsp + 64#64 ∧ s2.readReg64 .x19 = decA ∧
      s2.readReg64 .x20 = out ∧ s2.readReg64 .x28 = s0.readReg64 .x28 ∧
      s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0
  have hloop := pts_outer_loop_placed (R := R) (Q := Q328) h_panic hshim_sat halloc_sat s_ref328 fsp ptr_pts hfsp_align
    (dec.pts.map SortedSetPt.vec) hrem_ne 0 (by omega) v5 v6 v7 s1 Frame_loop
    hpc1 hrun1 hsp1 hx29_1 (by simpa [s_ref328, withSaved19_20_setLr_x19] using hx19_1)
    (by simpa [s_ref328, withSaved19_20_setLr_x20] using hx20_1)
    hx22_1 hx23_1 hx24_1 (by simpa [s_ref328, withSaved19_20_setLr_x28] using hx28_1)
    (by simpa [s_ref328, withSaved19_20_setLr_trace] using htr1)
    (by simpa [s_ref328, withSaved19_20_setLr_vregs] using hvregs1)
  dsimp only [s_ref328] at hloop
  simp only [withSaved19_20_setLr_lr, withSaved19_20_setLr_x19, withSaved19_20_setLr_x20, withSaved19_20_setLr_x28,
    withSaved19_20_setLr_trace, withSaved19_20_setLr_vregs, withSaved19_20_setLr_onPanic,
    Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrem_len] at hloop
  change _ → SepWPp _ _ _ _ _ _ at hloop
  refine sepWPp_seq_mid_lscl hcl1
    (SepWPp.weaken_pre (by dsimp only [vecPtListOf, Frame_loop]; exact Entails.of_eq (by ac_rfl))
      (hloop fun s2 w40 w48 w56 hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx28_2 htr2 hvregs2 =>
        SepWPp.done hpc2 hrun2 ⟨w40, w48, w56, Entails.refl _, hsp2, hx29_2, hx19_2, hx20_2, hx28_2, htr2, hvregs2⟩))
    ?_
  intro s2 P2 hpc2 hrun2 hcl2 ⟨w40, w48, w56, hent2, hsp2, hx29_2, hx19_2, hx20_2, hx28_2, htr2, hvregs2⟩
  refine SepWPp.weaken_pre hent2 ?_
  have hep := into_pb_epilogue_cl_placed hdrop s0 fsp out decA hfsp
    (BitVec.ofNat 32 dec.ptsNeeded) 16#32 v4 (boolByte dec.isComplete)
    hfsp_align (dec.pts.map SortedSetPt.vec) (by simp [hpts_len])
    16#64 ptr_pts 16#64 w40 w48 w56 v11 d0 d1 d2 d3 d4 s2
    (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
        ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗ A.live ptr_pts 384 8)
    hcl2 hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 htr2 hvregs2
  have hpre2 :
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        arrayAt (fun pts addr => vecPtOf A addr pts) 24 decA (dec.pts.map SortedSetPt.vec) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
          ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame_loop) ⊢
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
        ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗ memRegion (decA + 384#64) 16 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
            ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗ A.live ptr_pts 384 8)) := by
    dsimp only [Frame_loop, vecPtListOf]
    rw [stackAt_dropGluePoly16_split_bottom fsp]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre2 (SepWPp.seq_clean hep ?_)
  intro sf hpcf hrunf ⟨hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩
  have hpost_dec := protoPolynomialDecoderAt_entails A out ptr_pts dec hpts_len hptr_pts
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f,
    hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f.trans hx28_2, hx29f, hvregsf⟩⟩
  exact Entails.pure_right htrf (Entails.trans (Entails.of_eq (by ac_rfl))
    (Entails.trans (sepConj_mono_left (Q := memRegion decA 400 ∗ A.pool ∗ stackAt s0.sp decoderIntoPbStack) hpost_dec)
      (Entails.of_eq (by ac_rfl))))

end CryptoVerification.SpqrV1.Poly.DecoderPb
