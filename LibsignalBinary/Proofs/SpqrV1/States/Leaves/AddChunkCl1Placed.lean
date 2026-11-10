/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk` (Block `419`, `withLsCodeLoaded`)

Relocatable `[LibsignalPlacement]` verification of `<PolyDecoder as Decoder>::add_chunk` (Block `419`)
with `withLsCodeLoaded lsmpl`, discharging Block `357` (`RawVec<Pt>::grow_one`) and lifting to
`addChunkSpecX` and `withLsCodeRoLoaded lsmpl`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Poly.AddChunk

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open AddChunkNorm
open CryptoVerification.SpqrV1.States.Leaves (of_sepWP_lscl)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWPp_call_frozen {α : Type} {Inv : Memory → Prop}
    (hpres : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    {prog : Program} {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : Inv s.mem) (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Inv sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post x s sm ∗ F)
      Qp oom :=
    SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr hpre hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      hoom
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan_out | hoom_out⟩
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hpres s.mem sm.mem hinv hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan_out)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

private theorem addChunkSpecX_cl_of_addChunkSpec_cl [LibsignalPlacement]
    {prog : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog addr (withLsCodeLoaded lsmpl (addChunkSpec A))) :
    subroutine_ok prog addr (withLsCodeLoaded lsmpl (addChunkSpecX A)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hle : addChunkStack ≤ addChunkStackX := by decide
  have hsplit : stackAt s0.sp addChunkStackX =
      memRegion (s0.sp - BitVec.ofNat 64 addChunkStackX) (addChunkStackX - addChunkStack) ∗
        stackAt s0.sp addChunkStack := by
    have h1 := stackAt_split_bottom s0.sp addChunkStack (addChunkStackX - addChunkStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 addChunkStackX) (addChunkStackX - addChunkStack) ∗ R
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (addChunkSpec A)).pre x s0 ∗ R' := by
    dsimp only [withLsCodeLoaded, addChunkSpecX, addChunkSpec, R'] at hpre ⊢
    rw [hsplit] at hpre; ac_nf at hpre ⊢
  refine subroutine_ok.mono_outcome h x R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, addChunkSpecX, addChunkSpec, R'] at hpost ⊢
    rw [hsplit]; ac_nf at hpost ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeLoaded, addChunkSpecX, addChunkSpec, R'] at hpost ⊢
    have h1 : ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        memRegion (s0.sp - BitVec.ofNat 64 addChunkStackX) (addChunkStackX - addChunkStack) ∗ R) ⊢
        (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      rw [sepConj_assoc _ anyHeap _, ← sepConj_assoc anyHeap _ R, sepConj_assoc _ anyHeap R]
      exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))
    exact Satisfies.mono h1 hpost
  · dsimp only [withLsCodeLoaded, addChunkSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 1. Callee Call Wrappers (`grow_one_pt` with `withLsCodeLoaded lsmpl`) -/

theorem call_grow_one_pt_full_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtFullSpec A)))
    {ret_pc target_pc : BitVec 64} {s0 s : State} {Q : State → SepProp → Prop} {R F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (v cap ptr : BitVec 64) (vec : List Pt)
    (h1 : 1 ≤ vec.length) (hlen : vec.length ≤ 65536)
    (hcap_eq : cap.toNat = vec.length) (hptr : ptr ≠ 0#64)
    (hpc : s.pc = lsmpl.base 357) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = v) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.trace = s0.trace →
      CalleeSavedPreserved s sf →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtGrownAt A v vec ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
        A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  have hcap_ne0 : cap ≠ 0#64 := by intro hc0; subst hc0; change 0 = vec.length at hcap_eq; omega
  have hbs_len : (ptListBytes vec).length = cap.toNat * 4 := by
    rw [ptListBytes_length, hcap_eq, Nat.mul_comm]
  have hmax_bound : max (2 * cap.toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by omega
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (x := (v, cap, ptr, ptListBytes vec))
    (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗ F)
    hgrow_full hpc hrun hsp hlr ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [growOnePtFullSpec, growOneStrideFullSpec, hcap_ne0, ↓reduceIte,
      hbs_len, ← ptSliceAt_eq_pointsToBytes, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, trivial, hptr, hmax_bound⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withLsCodeLoaded, growOnePtFullSpec, growOneStrideFullSpec, addChunkOnPanic] at hm ⊢
    exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f hcl_f
    simp only [withLsCodeLoaded, growOnePtFullSpec, growOneStrideFullSpec, sepConj_assoc]
    apply SepWPp.pure_elim; intro htr_f
    have hgrown := growOnePtFull_post_entails_grown A v cap vec h1 hcap_eq hlen
    refine SepWPp.weaken_pre ?_ (hnext sf hcl_f hpc_f hrun_f hsp_f (htr_f.trans htr) hcs_f)
    rw [show (∃∗ p' : BitVec 64,
        ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * cap.toNat) 4 * 4) 2 ∗ (p' ↦ₛ ptListBytes vec) ∗
        memRegion (p' + BitVec.ofNat 64 (ptListBytes vec).length) ((max (2 * cap.toNat) 4 - cap.toNat) * 4)) ∗
        A.pool ∗ stackAt s.sp growOneStack ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗ F =
      ((∃∗ p' : BitVec 64,
        ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * cap.toNat) 4 * 4) 2 ∗ (p' ↦ₛ ptListBytes vec) ∗
        memRegion (p' + BitVec.ofNat 64 (ptListBytes vec).length) ((max (2 * cap.toNat) 4 - cap.toNat) * 4)) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length)) ∗
        (A.pool ∗ stackAt s.sp growOneStack ∗ F) by ac_rfl]
    exact sepConj_mono_left hgrown

theorem call_grow_one_pt_empty_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtSpec A)))
    {ret_pc target_pc : BitVec 64} {s0 s : State} {Q : State → SepProp → Prop} {R F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (v ptr lenOld : BitVec 64) (hptr : ptr ≠ 0#64)
    (hpc : s.pc = lsmpl.base 357) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = v) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hnext : ∀ (sf : State) (p' : BitVec 64), LibsignalCodeLoaded lsmpl sf.mem → p' ≠ 0#64 →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.trace = s0.trace →
      CalleeSavedPreserved s sf →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        ((v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
          A.live p' 16 2 ∗ memRegion p' 16 ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc s
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  have hmax_bound : max (2 * (0#64 : BitVec 64).toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by decide
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (x := (v, 0#64, ptr)) (F := ((v + 16#64) ↦₆₄ lenOld) ∗ F)
    hgrow_empty hpc hrun hsp hlr ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [growOnePtSpec, growOneStrideEmptySpec, ↓reduceIte, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hptr, hmax_bound⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withLsCodeLoaded, growOnePtSpec, growOneStrideEmptySpec, addChunkOnPanic] at hm ⊢
    exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f hcl_f
    have hmax0 : max (2 * (0#64 : BitVec 64).toNat) 4 = 4 := rfl
    simp only [withLsCodeLoaded, growOnePtSpec, growOneStrideEmptySpec, hmax0,
      sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.pure_elim; intro htr_f
    apply SepWPp.exists_elim; intro p'
    apply SepWPp.pure_elim; rintro ⟨hp', _⟩
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sf p' hcl_f hp' hpc_f hrun_f hsp_f (htr_f.trans htr) hcs_f)

/-! ## 2. Placed `bsearchReplace` (`+236 -> +64`, `withLsCodeLoaded lsmpl`) -/

theorem bsearchReplace_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtFullSpec A)))
    {target_pc : BitVec 64} {s0 st : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (v cap ptr : BitVec 64) (s : SortedSetPt) (pt : Pt)
    (h1 : 1 ≤ s.vec.length) (hlen : s.vec.length ≤ 65536)
    (hle_cap : s.vec.length ≤ cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hpc : st.pc = (blkPl_419).base + 236#64) (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true) (htr : st.trace = s0.trace)
    (hx8 : st.readReg64 .x8 = ptr) (hx14 : st.readReg64 .x14 = 1#64) (hx21 : st.readReg64 .x21 = v)
    (hx24 : st.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : st.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : st.readReg64 .x28 = BitVec.ofNat 64 s.vec.length)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_419).base + 64#64 → sf.status = .Running → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = st.readReg64 .x19 →
      sf.readReg64 .x20 = st.readReg64 .x20 → sf.readReg64 .x23 = st.readReg64 .x23 →
      sf.readReg64 .x24 = st.readReg64 .x24 → sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtOf A v (bsearchReplace s pt) ∗ A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
      (ptSliceAt ptr s.vec ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
        A.pool ∗ stackAt st.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 296#64)
  refine bsearch_to_296_placed_sepWP h1 (by omega) st _ _ hpc hrun hx8 hx24 hx28
    (fun s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx9_1 hx14_1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 _ hvregs_1 => ?_)
  apply SepWP.done hpc1 hrun1; intro hcl1
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hsp1_al : s1.spAligned = true := by unfold State.spAligned at hsp_al ⊢; rwa [hsp1]
  let base := bsearchLoop s.vec pt.x.value 0 s.vec.length
  change s1.readReg64 .x9 = BitVec.ofNat 64 base at hx9_1
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds s.vec pt.x.value 0 s.vec.length h1 (by omega)
  have hb_lt : base < s.vec.length := by omega
  have hb_get : s.vec[base]?.getD default = s.vec[base]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  let baseX := (s.vec[base]'hb_lt).x.value
  have hlsl_base : (BitVec.ofNat 64 base) <<< 2 = BitVec.ofNat 64 (4 * base) := bv64_lsl2_ofNat (by omega)
  unfold bsearchReplace at hnext; dsimp only at hnext; rw [hb_get] at hnext
  by_cases heq : ((s.vec[base]'hb_lt).x.value == pt.x.value) = true
  · simp only [heq, ↓reduceIte] at hnext
    change ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_419).base + 64#64 → sf.status = .Running → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = st.readReg64 .x19 →
      sf.readReg64 .x20 = st.readReg64 .x20 → sf.readReg64 .x23 = st.readReg64 .x23 →
      sf.readReg64 .x24 = st.readReg64 .x24 → sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtOf A v { vec := s.vec.set base pt } ∗ A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) at hnext
    have hbaseX_eq : (s.vec[base]'hb_lt).x.value = pt.x.value := beq_iff_eq.mp heq
    apply of_sepWP_lscl hcl1 (mid := (blkPl_419).base + 64#64)
    rw [ptSliceAt_focus s.vec base ptr hb_lt]; unfold ptAt; wp_steps 6
    have hreasm := reassemble_sortedSetPtOf_set A v cap ptr s.vec base pt hb_lt hle_cap hcap hptr
    refine SepWP.weaken_pre
      (show (((ptSliceAt ptr (List.take base s.vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * base)) ↦₁₆ (s.vec[base]'hb_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * base) + 2#64) ↦₁₆ pt.y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          A.live ptr (cap.toNat * 4) 2 ∗
          memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F)) ⊢
        sortedSetPtOf A v { vec := s.vec.set base pt } ∗ A.pool ∗ stackAt st.sp growOneStack ∗ F by
        rw [hbaseX_eq]; refine Entails.trans ?_ (sepConj_mono_left hreasm); exact Entails.of_eq (by ac_rfl)) ?_
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    intro hcl2
    exact hnext _ hcl2 (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simpa [wp_norm, arm64_norm] using hsp1) (by simpa [wp_norm, arm64_norm] using htr1')
      (by simpa [wp_norm, arm64_norm, hx14] using hx14_1) (by simpa [wp_norm, arm64_norm] using hx19_1)
      (by simpa [wp_norm, arm64_norm] using hx20_1) (by simpa [wp_norm, arm64_norm] using hx23_1)
      (by simpa [wp_norm, arm64_norm] using hx24_1) (by simpa [wp_norm, arm64_norm] using hx25_1)
      (by simpa [wp_norm, arm64_norm] using hx29_1) (by simpa [wp_norm, arm64_norm] using hvregs_1)
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hnext
    let insertIdx := if baseX.toNat < pt.x.value.toNat then base + 1 else base
    change ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_419).base + 64#64 → sf.status = .Running → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = st.readReg64 .x19 →
      sf.readReg64 .x20 = st.readReg64 .x20 → sf.readReg64 .x23 = st.readReg64 .x23 →
      sf.readReg64 .x24 = st.readReg64 .x24 → sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtOf A v { vec := s.vec.take insertIdx ++ (pt :: s.vec.drop insertIdx) } ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) at hnext
    have hins_le : insertIdx ≤ s.vec.length := by dsimp [insertIdx]; split_ifs <;> omega
    have hfold_slice :
        ((ptSliceAt ptr (List.take base s.vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * base)) ↦₁₆ (s.vec[base]'hb_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * base) + 2#64) ↦₁₆ (s.vec[base]'hb_lt).y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          A.live ptr (cap.toNat * 4) 2 ∗
          memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F) =
        (ptSliceAt ptr s.vec ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          A.live ptr (cap.toNat * 4) 2 ∗
          memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F) := by
      change ((ptSliceAt ptr (List.take base s.vec) ∗
        ptAt (s.vec[base]'hb_lt) (ptr + BitVec.ofNat 64 (4 * base)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗ _) = _
      rw [← ptSliceAt_focus s.vec base ptr hb_lt]
    by_cases hlt_cap : s.vec.length < cap.toNat
    · have hcap_ne : ¬ s.vec.length = cap.toNat := by omega
      apply of_sepWP_lscl hcl1 (mid := (blkPl_419).base + 64#64)
      have hins336 := @bsearch_insert_at_336_placed_sepWP _ A ext hmemmove_sat v cap ptr
        (BitVec.ofNat 64 s.vec.length) s.vec insertIdx pt hins_le hlt_cap hcap hptr
      rw [ptSliceAt_focus s.vec base ptr hb_lt]
      unfold ptAt
      wp_steps 4
      rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from
        Bool.eq_false_iff.mpr heq]
      simp only [Bool.not_false, ↓reduceIte]
      wp_steps 4
      rw [hfold_slice, bv64_beq_cap_ofNat (by omega)]
      simp only [hcap_ne, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [← hsp1]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (hins336 _ (A.pool ∗ F) _
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
          (by simpa [wp_norm, arm64_norm] using hsp1_al) (by simp [wp_norm, arm64_norm, hx8_1])
          (by simp [wp_norm, arm64_norm, hx14_1, hx14]) (by simp [wp_norm, arm64_norm, hx21_1, hx21])
          (by simp [wp_norm, arm64_norm, hx24_1, hx24])
          (by simp only [wp_norm, arm64_norm]; exact cinc_insertIdx_eq baseX pt.x.value base)
          (by simp [wp_norm, arm64_norm, hx27_1, hx27]) (by simp [wp_norm, arm64_norm, hx28_1, hx28])
          (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      apply SepWP.done hpc_f hrun_f; intro hcl_f
      have hsp_f' : sf.sp = st.sp := by simpa [wp_norm, arm64_norm, hsp1] using hsp_f
      rw [← hsp_f, hsp_f']
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hnext sf hcl_f hpc_f hrun_f hsp_f' (by simpa [wp_norm, arm64_norm, htr1'] using htr_f) hx14_f
          (by simpa [wp_norm, arm64_norm, hx19_1] using hx19_f) (by simpa [wp_norm, arm64_norm, hx20_1] using hx20_f)
          (by simpa [wp_norm, arm64_norm, hx23_1] using hx23_f) (by simpa [wp_norm, arm64_norm, hx24_1] using hx24_f)
          (by simpa [wp_norm, arm64_norm, hx25_1] using hx25_f) (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
          (by simpa [wp_norm, arm64_norm, hvregs_1] using hvregs_f))
    · have hcall := @call_grow_one_pt_full_cl_placed_wpp _ A ext hgrow_full
        ((blkPl_419).base + 452#64) target_pc s0
      have hins452 := @bsearch_insert_at_452_placed_sepWP _ A ext hmemmove_sat v s.vec insertIdx pt hins_le
      apply of_sepWP_lscl hcl1 (mid := lsmpl.base 357)
      rw [ptSliceAt_focus s.vec base ptr hb_lt]; unfold ptAt; wp_steps 4
      rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from
        Bool.eq_false_iff.mpr heq]
      simp only [Bool.not_false, ↓reduceIte]; wp_steps 4
      rw [hfold_slice, bv64_beq_cap_ofNat (by omega),
        show decide (s.vec.length = cap.toNat) = true from decide_eq_true (by omega)]
      simp only [↓reduceIte]; wp_steps 2
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      intro hcl2
      have hcap_eq : cap.toNat = s.vec.length := by omega
      have hmem_zero :
          memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) = emp := by
        rw [hcap_eq, Nat.sub_self, Nat.zero_mul, memRegion_zero]
      rw [hmem_zero, ← hsp1]; simp only [emp_sepConj]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcall (F := F) hcl2 v cap ptr s.vec h1 hlen hcap_eq hptr
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
          (by simpa [wp_norm, arm64_norm] using hsp1_al) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using htr1')
          (fun s2 hcl_s2 hpc2 hrun2 hsp2 htr2 hcs2 => ?_))
      have hsp2' : s2.sp = st.sp := by rw [hsp2]; simpa [wp_norm, arm64_norm] using hsp1
      have hsp2_al : s2.spAligned = true := by unfold State.spAligned at hsp_al ⊢; rwa [hsp2']
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
      have hx26_s2 : s2.readReg64 .x26 = BitVec.ofNat 64 insertIdx := by
        rw [hx26_2]; simp only [wp_norm, arm64_norm]; exact cinc_insertIdx_eq baseX pt.x.value base
      rw [← hsp2]
      apply of_sepWP_lscl hcl_s2 (mid := (blkPl_419).base + 64#64)
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (hins452 s2 (A.pool ∗ F) _ hpc2 hrun2 hsp2_al
          (by rw [hx21_2]; simpa [wp_norm, arm64_norm, hx21] using hx21_1)
          (by rw [hx24_2]; simpa [wp_norm, arm64_norm, hx24] using hx24_1) hx26_s2
          (by rw [hx27_2]; simpa [wp_norm, arm64_norm, hx27] using hx27_1)
          (by rw [hx28_2]; simpa [wp_norm, arm64_norm, hx28] using hx28_1)
          (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      apply SepWP.done hpc_f hrun_f; intro hcl_f; rw [hsp2']
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hnext sf hcl_f hpc_f hrun_f (hsp_f.trans hsp2') (htr_f.trans htr2) hx14_f
          (by rw [hx19_f, hx19_2]; simpa [wp_norm, arm64_norm] using hx19_1)
          (by rw [hx20_f, hx20_2]; simpa [wp_norm, arm64_norm] using hx20_1)
          (by rw [hx23_f, hx23_2]; simpa [wp_norm, arm64_norm] using hx23_1)
          (by rw [hx24_f, hx24_2]; simpa [wp_norm, arm64_norm] using hx24_1)
          (by rw [hx25_f, hx25_2]; simpa [wp_norm, arm64_norm] using hx25_1)
          (by rw [hx29_f, hx29_2]; simpa [wp_norm, arm64_norm] using hx29_1)
          (by rw [hvregs_f, hvregs_2]; simpa [wp_norm, arm64_norm] using hvregs_1))

/-! ## 3. Placed `bsearchPush` (`+128 -> +64`, `withLsCodeLoaded lsmpl`) -/

theorem bsearchPush_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtFullSpec A)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtSpec A)))
    {target_pc : BitVec 64} {s0 st : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (v : BitVec 64) (s : SortedSetPt) (pt : Pt)
    (hlen : s.vec.length ≤ 65536)
    (hpc : st.pc = (blkPl_419).base + 128#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (htr : st.trace = s0.trace)
    (hx14 : st.readReg64 .x14 = 1#64)
    (hx21 : st.readReg64 .x21 = v)
    (hx24 : st.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : st.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : st.readReg64 .x28 = BitVec.ofNat 64 s.vec.length)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running →
      sf.sp = st.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = st.readReg64 .x19 →
      sf.readReg64 .x20 = st.readReg64 .x20 →
      sf.readReg64 .x23 = st.readReg64 .x23 →
      sf.readReg64 .x24 = st.readReg64 .x24 →
      sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtOf A v (bsearchPush s pt) ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
      (sortedSetPtOf A v s ∗ A.pool ∗ stackAt st.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (sepConj_mono_left (sortedSetPtOf_expose A v s)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_elim; rintro ⟨hle_cap, hcap, hptr⟩
  rcases Nat.eq_zero_or_pos s.vec.length with hlen0 | h1
  · have hvec_nil : s.vec = [] := List.eq_nil_of_length_eq_zero hlen0
    have hpush_nil : bsearchPush s pt = { vec := [pt] } := by
      unfold bsearchPush; rw [hvec_nil]; rfl
    rw [hpush_nil] at hnext
    rw [hlen0] at hx28
    have hslice_nil : ptSliceAt ptr [] = emp := rfl
    simp only [hvec_nil, List.length_nil, Nat.zero_mul, Nat.sub_zero,
      BitVec.add_zero, hslice_nil, emp_sepConj]
    by_cases hcap0 : cap = 0#64
    · subst hcap0
      simp only [↓reduceIte, emp_sepConj]
      have hcall := @call_grow_one_pt_empty_cl_placed_wpp _ A ext hgrow_empty
        ((blkPl_419).base + 396#64) target_pc s0
      have hpush216 := @bsearch_push_empty_at_216_placed_sepWP _ A ext v 4#64
      apply of_sepWP_lscl hcl (mid := lsmpl.base 357)
      wp_steps 5
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      intro hcl1
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcall (F := F) hcl1 v ptr 0#64 hptr
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simpa [wp_norm, arm64_norm] using hsp_al)
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using htr)
          (fun s2 p' hcl_s2 hp' hpc2 hrun2 hsp2 htr2 hcs2 => ?_))
      have hsp2' : s2.sp = st.sp := by
        simpa [wp_norm, arm64_norm] using hsp2
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, hx27_2, _, hx29_2, hvregs_2⟩
      rw [← hsp2]
      apply of_sepWP_lscl hcl_s2 (mid := (blkPl_419).base + 64#64)
      wp_steps 2
      have h4_16 : (4#64 : BitVec 64).toNat * 4 = 16 := rfl
      refine SepWP.weaken_pre (by rw [h4_16]; exact Entails.of_eq (by ac_rfl))
        (hpush216 p' 0#64 pt (by decide) (by decide) hp' _
          (A.pool ∗ stackAt s2.sp growOneStack ∗ F) _
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun2])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hx21_2, hx21])
          (by simp [wp_norm, arm64_norm, hx24_2, hx24])
          (by simp [wp_norm, arm64_norm, hx27_2, hx27])
          (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      apply SepWP.done hpc_f hrun_f; intro hcl_f
      have hsp_f' : sf.sp = st.sp := by
        simpa [wp_norm, arm64_norm, hsp2'] using hsp_f
      rw [hsp2']
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hnext sf hcl_f hpc_f hrun_f hsp_f'
          (by simpa [wp_norm, arm64_norm, htr2] using htr_f) hx14_f
          (by simpa [wp_norm, arm64_norm, hx19_2] using hx19_f) (by simpa [wp_norm, arm64_norm, hx20_2] using hx20_f)
          (by simpa [wp_norm, arm64_norm, hx23_2] using hx23_f) (by simpa [wp_norm, arm64_norm, hx24_2] using hx24_f)
          (by simpa [wp_norm, arm64_norm, hx25_2] using hx25_f) (by simpa [wp_norm, arm64_norm, hx29_2] using hx29_f)
          (by simpa [wp_norm, arm64_norm, hvregs_2] using hvregs_f))
    · simp only [hcap0, ↓reduceIte]
      have hlt0 : 0 < cap.toNat := by
        by_contra hle0; apply hcap0; apply BitVec.eq_of_toNat_eq; change cap.toNat = 0; omega
      have hbeq0 : (cap == 0#64) = false := beq_false_of_ne hcap0
      have hpush216 := @bsearch_push_empty_at_216_placed_sepWP _ A ext v cap ptr 0#64 pt hlt0 hcap hptr
      apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 64#64)
      wp_steps 3
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (hpush216 _ (A.pool ∗ stackAt st.sp growOneStack ∗ F) _
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          (by simp [wp_norm, arm64_norm, hx14]) (by simp [wp_norm, arm64_norm, hx21])
          (by simp [wp_norm, arm64_norm, hx24]) (by simp [wp_norm, arm64_norm, hx27])
          (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      apply SepWP.done hpc_f hrun_f; intro hcl_f
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hnext sf hcl_f hpc_f hrun_f (by simpa [wp_norm, arm64_norm] using hsp_f)
          (by simpa [wp_norm, arm64_norm, htr] using htr_f) hx14_f
          (by simpa [wp_norm, arm64_norm] using hx19_f) (by simpa [wp_norm, arm64_norm] using hx20_f)
          (by simpa [wp_norm, arm64_norm] using hx23_f) (by simpa [wp_norm, arm64_norm] using hx24_f)
          (by simpa [wp_norm, arm64_norm] using hx25_f) (by simpa [wp_norm, arm64_norm] using hx29_f)
          (by simpa [wp_norm, arm64_norm] using hvregs_f))
  · have hcap0 : cap ≠ 0#64 := by
      intro hc; subst hc; have h0 : (0#64 : BitVec 64).toNat = 0 := rfl; omega
    simp only [hcap0, ↓reduceIte]
    let lastIdx := s.vec.length - 1
    have hlast_lt : lastIdx < s.vec.length := by omega
    let lastPt := s.vec[lastIdx]'hlast_lt
    have hlast_eq : s.vec.getLast? = some lastPt := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlast_lt]
    have hne0 : (BitVec.ofNat 64 s.vec.length == 0#64) = false := bv64_ne_zero_of_pos h1 hlen
    have hlsl_len : (BitVec.ofNat 64 s.vec.length) <<< 2 = BitVec.ofNat 64 (4 * s.vec.length) :=
      bv64_lsl2_ofNat (by omega)
    have hsub4 : ptr + BitVec.ofNat 64 (4 * s.vec.length) + bv% (2 ^ 64 - 4) =
        ptr + BitVec.ofNat 64 (4 * lastIdx) := ptr_add_len_sub4 ptr h1 hlen
    have hsub2 : ptr + BitVec.ofNat 64 (4 * s.vec.length) + bv% (2 ^ 64 - 2) =
        ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64 := ptr_add_len_sub2 ptr h1 hlen
    unfold bsearchPush at hnext
    rw [hlast_eq] at hnext
    dsimp only at hnext
    cases hcmp : Pt.cmp pt lastPt with
    | eq =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hset_eq : s.vec.dropLast ++ [pt] = s.vec.set lastIdx pt :=
        dropLast_append_singleton_eq_set s.vec pt h1
      rw [hset_eq] at hnext
      have hcmp' : pt.x.value.toNat = (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_eq_iff_eq.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 64#64)
      rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      wp_steps 11
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      intro hcl1
      rw [hsub4, hsub2]
      have hreasm := reassemble_sortedSetPtOf_set A v cap ptr s.vec lastIdx pt hlast_lt hle_cap hcap hptr
      refine SepWPp.weaken_pre
        (P' := sortedSetPtOf A v { vec := s.vec.set lastIdx pt } ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F)
        (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
            exact Entails.of_eq (by ac_rfl))
        (hnext _ hcl1
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using htr)
          (by simp [wp_norm, arm64_norm, hx14])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]))
    | lt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : pt.x.value.toNat < (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_lt_iff_lt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hrep := @bsearchReplace_cl_placed_wpp _ A ext hmemmove_sat hgrow_full target_pc s0
      apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 236#64)
      rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      wp_steps 11
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      intro hcl1
      rw [hsub4, hsub2]
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      rw [hfold_slice]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hrep (F := F) hcl1 v cap ptr s pt h1 hlen hle_cap hcap hptr
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          (by simpa [wp_norm, arm64_norm] using hsp_al) (by simpa [wp_norm, arm64_norm] using htr)
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx14])
          (by simp [wp_norm, arm64_norm, hx21]) (by simp [wp_norm, arm64_norm, hx24])
          (by simp [wp_norm, arm64_norm, hx27]) (by simp [wp_norm, arm64_norm, hx28])
          (fun sf hcl_f hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      have hsp_f' : sf.sp = st.sp := by simpa [wp_norm, arm64_norm] using hsp_f
      simp only [wp_norm, arm64_norm]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hnext sf hcl_f hpc_f hrun_f hsp_f' htr_f hx14_f
          (by simpa [wp_norm, arm64_norm] using hx19_f) (by simpa [wp_norm, arm64_norm] using hx20_f)
          (by simpa [wp_norm, arm64_norm] using hx23_f) (by simpa [wp_norm, arm64_norm] using hx24_f)
          (by simpa [wp_norm, arm64_norm] using hx25_f) (by simpa [wp_norm, arm64_norm] using hx29_f)
          (by simpa [wp_norm, arm64_norm] using hvregs_f))
    | gt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : (s.vec[lastIdx]'hlast_lt).x.value.toNat < pt.x.value.toNat :=
        compare_gt_iff_gt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      by_cases hlt_cap : s.vec.length < cap.toNat
      · have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = false := by
          rw [bv64_beq_cap_ofNat (by omega), decide_eq_false_iff_not]; omega
        have hule_succ :
            (BitVec.ofNat 64 s.vec.length).ule (BitVec.ofNat 64 (s.vec.length + 1)) = true :=
          bv64_ule_succ (by omega)
        apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 64#64)
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
        unfold ptAt
        rw [← hsub2, ← hsub4]
        rw [memRegion_spare_split_one ptr hlt_cap hcap]
        wp_pull_exists
        rename_i v1 v0
        wp_steps 19
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        intro hcl1
        rw [hsub4, hsub2]
        have hreasm := reassemble_sortedSetPtOf_snoc A v cap ptr s.vec pt hlt_cap hcap hptr
        rw [← hfold_slice] at hreasm
        refine SepWPp.weaken_pre
          (P' := sortedSetPtOf A v { vec := s.vec ++ [pt] } ∗
            A.pool ∗ stackAt st.sp growOneStack ∗ F)
          (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
              exact Entails.of_eq (by ac_rfl))
          (hnext _ hcl1 (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
            (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using htr)
            (by simp [wp_norm, arm64_norm, hx14]) (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
      · have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = true := by
          rw [bv64_beq_cap_ofNat (by omega), decide_eq_true_eq]; omega
        have hcall := @call_grow_one_pt_full_cl_placed_wpp _ A ext hgrow_full
          ((blkPl_419).base + 412#64) target_pc s0
        have hgrown := @bsearch_push_grown_at_412_placed_sepWP _ A ext v s.vec pt
        apply of_sepWP_lscl hcl (mid := lsmpl.base 357)
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
        unfold ptAt
        rw [← hsub2, ← hsub4]
        wp_steps 16
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        intro hcl1
        rw [hsub4, hsub2, hfold_slice]
        have hcap_eq : cap.toNat = s.vec.length := by omega
        have hmem_zero :
            memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) = emp := by
          rw [hcap_eq, Nat.sub_self, Nat.zero_mul, memRegion_zero]
        rw [hmem_zero]
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (hcall (F := F) hcl1 v cap ptr s.vec h1 hlen hcap_eq hptr
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
            (by simpa [wp_norm, arm64_norm] using hsp_al) (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using htr)
            (fun s2 hcl_s2 hpc2 hrun2 hsp2 htr2 hcs2 => ?_))
        have hsp2' : s2.sp = st.sp := by simpa [wp_norm, arm64_norm] using hsp2
        rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, hx27_2, hx28_2, hx29_2, hvregs_2⟩
        rw [← hsp2]
        apply of_sepWP_lscl hcl_s2 (mid := (blkPl_419).base + 64#64)
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (hgrown s2 (A.pool ∗ stackAt s2.sp growOneStack ∗ F) _ hpc2 hrun2
            (by rw [hx21_2]; simp [wp_norm, arm64_norm, hx21]) (by rw [hx24_2]; simp [wp_norm, arm64_norm, hx24])
            (by rw [hx27_2]; simp [wp_norm, arm64_norm, hx27]) (by rw [hx28_2]; simp [wp_norm, arm64_norm, hx28])
            (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        apply SepWP.done hpc_f hrun_f; intro hcl_f
        have hsp_f' : sf.sp = st.sp := by simpa [wp_norm, arm64_norm, hsp2'] using hsp_f
        rw [hsp2']
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (hnext sf hcl_f hpc_f hrun_f hsp_f' (by simpa [wp_norm, arm64_norm, htr2] using htr_f) hx14_f
            (by rw [hx19_f, hx19_2]; simp [wp_norm, arm64_norm]) (by rw [hx20_f, hx20_2]; simp [wp_norm, arm64_norm])
            (by rw [hx23_f, hx23_2]; simp [wp_norm, arm64_norm]) (by rw [hx24_f, hx24_2]; simp [wp_norm, arm64_norm])
            (by rw [hx25_f, hx25_2]; simp [wp_norm, arm64_norm]) (by rw [hx29_f, hx29_2]; simp [wp_norm, arm64_norm])
            (by rw [hvregs_f, hvregs_2]; simp [wp_norm, arm64_norm]))

/-! ## 4. Placed Outer 16-Iteration Loop (`addChunk_body_cl_placed_wpp`, `addChunk_loop_cl_placed_wpp`) -/

theorem addChunk_body_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtFullSpec A)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtSpec A)))
    {target_pc : BitVec 64} {s0 st : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (decA chunkA : BitVec 64) (self : PolyDecoder) (chunk : Chunk) (i : Nat)
    (hi : i < 16) (hpts_len : self.pts.length = 16) (hneed : self.ptsNeeded < 2 ^ 64)
    (hcap_i : (self.pts[i]'(by omega)).vec.length ≤ 65536)
    (hpc : st.pc = (blkPl_419).base + 76#64)
    (hrun : st.status = .Running) (hsp_al : st.spAligned = true) (htr : st.trace = s0.trace)
    (hx14 : st.readReg64 .x14 = 1#64) (hx19 : st.readReg64 .x19 = chunkA) (hx20 : st.readReg64 .x20 = decA)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 i) (hx24 : st.readReg64 .x24 = chunk.index.zeroExtend 64)
    (hx25 : st.readReg64 .x25 = 24#64)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = chunkA → sf.readReg64 .x20 = decA →
      sf.readReg64 .x23 = BitVec.ofNat 64 i → sf.readReg64 .x24 = chunk.index.zeroExtend 64 →
      sf.readReg64 .x25 = 24#64 → sf.readReg64 .x29 = st.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtListOf A decA (addChunkBsearchStep chunk i self).pts ∗
          ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
          (chunkA ↦ₛ chunk.data.toList) ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
      (sortedSetPtListOf A decA self.pts ∗
        ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
        (chunkA ↦ₛ chunk.data.toList) ∗
        A.pool ∗ stackAt st.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  have hi_pts : i < self.pts.length := by omega
  let nec := self.necessaryPoints i
  have hnec : nec < 2 ^ 64 := necessaryPoints_lt self i hneed
  have hmadd : decA + BitVec.ofNat 64 i * 24#64 = decA + BitVec.ofNat 64 (24 * i) :=
    bv64_madd24_ofNat decA hi
  have _hlsr4 : (BitVec.ofNat 64 self.ptsNeeded) >>> 4 = BitVec.ofNat 64 (self.ptsNeeded / 16) :=
    bv64_lsr4_ofNat hneed
  have _hand15 : (BitVec.ofNat 64 self.ptsNeeded) &&& 15#64 = BitVec.ofNat 64 (self.ptsNeeded % 16) :=
    bv64_and15_ofNat hneed
  have _hcinc_nec := cinc_necessaryPoints_eq self hi hneed
  have hskip_cond := addChunk_skip_cond_eq chunk.index hnec
    (by omega : (self.pts[i]'hi_pts).vec.length < 2 ^ 64)
  have hget_i : self.pts[(chunk.index.toNat * 16 + i) % 16]?.getD SortedSetPt.new = self.pts[i]'hi_pts := by
    rw [addChunk_poly_eq chunk hi, List.getElem?_eq_getElem hi_pts, Option.getD_some]
  by_cases hcond : (decide (chunk.index.toNat < nec) || decide ((self.pts[i]'hi_pts).vec.length < nec)) = true
  · have hstep_eq :
        (addChunkBsearchStep chunk i self).pts =
          self.pts.set i
            (bsearchPush (self.pts[i]'hi_pts)
              { x := GF16.new chunk.index
                y := GF16.new
                  (((chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 16 <<< 8) +
                    (chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 16) }) := by
      unfold addChunkBsearchStep SortedSetPt.len
      dsimp only
      rw [hget_i, addChunk_poly_eq chunk hi, addChunk_x_eq chunk hi, addChunk_polyIdx_eq chunk hi, hcond]
      rfl
    rw [hstep_eq] at hnext
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let pt : Pt := { x := GF16.new chunk.index, y := y }
    have hlsl1 : (BitVec.ofNat 64 i) <<< 1 = BitVec.ofNat 64 (i * 2) := bv64_lsl1_ofNat hi
    have hpush := @bsearchPush_cl_placed_wpp _ A ext hmemmove_sat hgrow_full hgrow_empty target_pc s0
    apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 128#64)
    dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat] at hpush hpc hnext ⊢
    have _hbr_false :
        (if (if (BitVec.ofNat 64 (self.necessaryPoints i)).ule (BitVec.zeroExtend 64 chunk.index) = true then
            (BitVec.ofNat 64 (self.necessaryPoints i)).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length)
          else ConditionHolds CondCode.CS { }) = true then
          (blkPl_419).base + 64#64
        else (blkPl_419).base + 116#64) = (blkPl_419).base + 116#64 := by
      change (if (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 chunk.index) = true then
          (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length) else false) = true then
          (blkPl_419).base + 64#64 else (blkPl_419).base + 116#64) = (blkPl_419).base + 116#64
      rw [hskip_cond, hcond]; rfl
    rw [sortedSetPtListOf_focus A self.pts i decA hi_pts]
    rw [sortedSetPtOf_eq_len_sep A (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts), ← hmadd]
    rw [chunk_data_focus16 chunkA chunk i hi]
    rw [← hlsl1]
    wp_steps 13
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    intro hcl1
    rw [hmadd, ← sortedSetPtOf_eq_len_sep A (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts)]
    rw [hlsl1]
    have hfold_chunk :
        ((chunkA ↦ₛ chunk.data.toList.take (i * 2)) ∗
          ((chunkA + BitVec.ofNat 64 (i * 2)) ↦₁₆ (y2 ++ y1)) ∗
          ((chunkA + BitVec.ofNat 64 (i * 2 + 2)) ↦ₛ chunk.data.toList.drop (i * 2 + 2))) =
        (chunkA ↦ₛ chunk.data.toList) :=
      (chunk_data_focus16 chunkA chunk i hi).symm
    refine SepWPp.weaken_pre
      (by rw [← hfold_chunk]; dsimp only [y1, y2]; simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by ac_rfl))
      (hpush (F := sortedSetPtListOf A decA (self.pts.take i) ∗
          sortedSetPtListOf A (decA + BitVec.ofNat 64 (24 * (i + 1))) (self.pts.drop (i + 1)) ∗
          ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
          (chunkA ↦ₛ chunk.data.toList) ∗ F)
        hcl1 (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts) pt hcap_i
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simpa [wp_norm, arm64_norm] using hsp_al) (by simpa [wp_norm, arm64_norm] using htr)
        (by simp [wp_norm, arm64_norm, hx14]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx24, pt, GF16.new])
        (by simp only [wp_norm, arm64_norm, pt, y, GF16.new]; exact rev16_64_pair y1 y2)
        (by simp [wp_norm, arm64_norm])
        (fun sf hcl_f hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
    have hsp_f' : sf.sp = st.sp := by simpa [wp_norm, arm64_norm] using hsp_f
    simp only [wp_norm, arm64_norm]
    refine SepWPp.weaken_pre
      (by rw [sortedSetPtListOf_set A self.pts i (bsearchPush (self.pts[i]'hi_pts) pt) decA hi_pts]
          exact Entails.of_eq (by ac_rfl))
      (hnext sf hcl_f hpc_f hrun_f hsp_f' htr_f hx14_f
        (by simpa [wp_norm, arm64_norm, hx19] using hx19_f) (by simpa [wp_norm, arm64_norm, hx20] using hx20_f)
        (by simpa [wp_norm, arm64_norm, hx23] using hx23_f) (by simpa [wp_norm, arm64_norm, hx24] using hx24_f)
        (by simpa [wp_norm, arm64_norm, hx25] using hx25_f) (by simpa [wp_norm, arm64_norm] using hx29_f)
        (by simpa [wp_norm, arm64_norm] using hvregs_f))
  · have hcond_f : (decide (chunk.index.toNat < nec) || decide ((self.pts[i]'hi_pts).vec.length < nec)) = false :=
       Bool.eq_false_iff.mpr hcond
    have hstep_eq : (addChunkBsearchStep chunk i self).pts = self.pts := by
      unfold addChunkBsearchStep SortedSetPt.len; dsimp only
      rw [hget_i, addChunk_polyIdx_eq chunk hi, hcond_f]; rfl
    rw [hstep_eq] at hnext
    apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 64#64)
    dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
    rw [sortedSetPtListOf_focus A self.pts i decA hi_pts]
    rw [sortedSetPtOf_eq_len_sep A (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts), ← hmadd]
    wp_steps 10
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm]
          change (if (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 chunk.index) = true then
              (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length) else false) = true then
              (blkPl_419).base + 64#64 else (blkPl_419).base + 116#64) = (blkPl_419).base + 64#64
          rw [hskip_cond, hcond_f]; rfl)
      (by simp [wp_norm, arm64_norm, hrun])
    intro hcl1
    rw [hmadd, ← sortedSetPtOf_eq_len_sep A (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts)]
    refine SepWPp.weaken_pre
      (by rw [sortedSetPtListOf_focus A self.pts i decA hi_pts]; exact Entails.of_eq (by ac_rfl))
      (hnext _ hcl1
        (by simp only [wp_norm, arm64_norm]
            change (if (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 chunk.index) = true then
                (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length) else false) = true then
                (blkPl_419).base + 64#64 else (blkPl_419).base + 116#64) = (blkPl_419).base + 64#64
            rw [hskip_cond, hcond_f]; rfl)
        (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
        (by simpa [wp_norm, arm64_norm] using htr) (by simp [wp_norm, arm64_norm, hx14])
        (by simp [wp_norm, arm64_norm, hx19]) (by simp [wp_norm, arm64_norm, hx20])
        (by simp [wp_norm, arm64_norm, hx23]) (by simp [wp_norm, arm64_norm, hx24])
        (by simp [wp_norm, arm64_norm, hx25]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))

theorem addChunk_loop_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtFullSpec A)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtSpec A)))
    {target_pc : BitVec 64} {s0 : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (decA chunkA sp : BitVec 64) (chunk : Chunk)
    (rem : Nat) :
    ∀ (i : Nat) (self : PolyDecoder) (st : State),
      LibsignalCodeLoaded lsmpl st.mem →
      i + (rem + 1) = 16 →
      self.pts.length = 16 →
      self.ptsNeeded < 2 ^ 64 →
      (∀ j (hj : j < self.pts.length), i ≤ j → (self.pts[j]'hj).vec.length ≤ 65536) →
      st.pc = (blkPl_419).base + 76#64 →
      st.status = .Running →
      st.sp = sp →
      st.spAligned = true →
      st.trace = s0.trace →
      st.readReg64 .x14 = 1#64 →
      st.readReg64 .x19 = chunkA →
      st.readReg64 .x20 = decA →
      st.readReg64 .x23 = BitVec.ofNat 64 i →
      st.readReg64 .x24 = chunk.index.zeroExtend 64 →
      st.readReg64 .x25 = 24#64 →
      (∀ sf : State,
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_419).base + 476#64 →
        sf.status = .Running →
        sf.sp = sp →
        sf.trace = s0.trace →
        sf.readReg64 .x29 = st.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs st →
        SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
          (sortedSetPtListOf A decA (addChunkBsearchLoop chunk i (rem + 1) self).pts ∗
            ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
            (chunkA ↦ₛ chunk.data.toList) ∗
            A.pool ∗ stackAt sp growOneStack ∗ F)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
        (sortedSetPtListOf A decA self.pts ∗
          ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
          (chunkA ↦ₛ chunk.data.toList) ∗
          A.pool ∗ stackAt sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  induction rem with
  | zero =>
    intro i self st hcl hirem hpts_len hneed hcap hpc hrun hsp hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25 hnext
    have hi : i < 16 := by omega
    have hcap_i : (self.pts[i]'(by omega)).vec.length ≤ 65536 := hcap i (by omega) (Nat.le_refl i)
    have _hbeq16 : (BitVec.ofNat 64 (i + 1) == 16#64) = true := by
      rw [bv64_add1_beq16 hi, decide_eq_true_eq]; omega
    rw [← hsp]
    refine addChunk_body_cl_placed_wpp hmemmove_sat hgrow_full hgrow_empty hcl decA chunkA self chunk i hi hpts_len hneed hcap_i
      hpc hrun hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25
      (fun s1 hcl1 hpc1 hrun1 hsp1 htr1 _hx14_1 _hx19_1 _hx20_1 _hx23_1 _hx24_1 _hx25_1 hx29_1 hvregs_1 => ?_)
    rw [hsp]
    apply of_sepWP_lscl hcl1 (mid := (blkPl_419).base + 476#64); wp_steps 3
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    intro hcl2
    exact hnext _ hcl2 (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simpa [wp_norm, arm64_norm, hsp] using hsp1) (by simpa [wp_norm, arm64_norm] using htr1)
      (by simpa [wp_norm, arm64_norm] using hx29_1) (by simpa [wp_norm, arm64_norm] using hvregs_1)
  | succ rem ih =>
    intro i self st hcl hirem hpts_len hneed hcap hpc hrun hsp hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25 hnext
    have hi : i < 16 := by omega
    have hcap_i : (self.pts[i]'(by omega)).vec.length ≤ 65536 := hcap i (by omega) (Nat.le_refl i)
    have _hbeq16 : (BitVec.ofNat 64 (i + 1) == 16#64) = false := by
      rw [bv64_add1_beq16 hi, decide_eq_false_iff_not]; omega
    rw [← hsp]
    refine addChunk_body_cl_placed_wpp hmemmove_sat hgrow_full hgrow_empty hcl decA chunkA self chunk i hi hpts_len hneed hcap_i
      hpc hrun hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25
      (fun s1 hcl1 hpc1 hrun1 hsp1 htr1 hx14_1 hx19_1 hx20_1 _hx23_1 hx24_1 hx25_1 hx29_1 hvregs_1 => ?_)
    rw [hsp]
    have hsp_al1 : s1.spAligned = true := by unfold State.spAligned at hsp_al ⊢; rwa [hsp1]
    have hpts_len' : (addChunkBsearchStep chunk i self).pts.length = 16 := by
      rw [addChunkBsearchStep_pts_length]; exact hpts_len
    have hneed' : (addChunkBsearchStep chunk i self).ptsNeeded < 2 ^ 64 := by
      rw [addChunkBsearchStep_ptsNeeded]; exact hneed
    have hcap' : ∀ j (hj : j < (addChunkBsearchStep chunk i self).pts.length),
        i + 1 ≤ j → ((addChunkBsearchStep chunk i self).pts[j]'hj).vec.length ≤ 65536 := by
      intro j hj hij
      have hj0 : j < self.pts.length := by rw [← addChunkBsearchStep_pts_length chunk i self]; exact hj
      rw [addChunkBsearchStep_getElem_after chunk self hi (by omega) hj0]
      exact hcap j hj0 (by omega)
    have hstep := ih (i + 1) (addChunkBsearchStep chunk i self)
    apply of_sepWP_lscl hcl1 (mid := (blkPl_419).base + 76#64); wp_steps 3
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    intro hcl2
    rw [← addChunkBsearchStep_ptsNeeded chunk i self]
    refine hstep _ hcl2 (by omega) hpts_len' hneed' hcap'
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simpa [wp_norm, arm64_norm, hsp] using hsp1) (by simpa [wp_norm, arm64_norm] using hsp_al1)
      (by simpa [wp_norm, arm64_norm] using htr1) (by simp [wp_norm, arm64_norm, hx14_1])
      (by simp [wp_norm, arm64_norm, hx19_1]) (by simp [wp_norm, arm64_norm, hx20_1])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx24_1])
      (by simp [wp_norm, arm64_norm, hx25_1])
      (fun sf hcl_f hpc_f hrun_f hsp_f htr_f hx29_f hvregs_f => ?_)
    rw [addChunkBsearchStep_ptsNeeded chunk i self]
    exact hnext sf hcl_f hpc_f hrun_f hsp_f htr_f
      (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
      (by simpa [wp_norm, arm64_norm, hvregs_1] using hvregs_f)

/-! ## 5. Placed Top-Level Theorems (`withLsCodeLoaded lsmpl` & `withLsCodeRoLoaded lsmpl`) -/

private theorem subroutine_ok_lscl_of_sepWPp {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {pl : Obj.MultiPlacement}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      LibsignalCodeLoaded pl s0.mem →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_comm (spec.pre x s0), sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h x R s0 hpc hrun hpre.1 hpre.2 hsp

open Lean Elab Tactic Meta in
local elab "wpp_init_lscl " a:ident s0:ident hcl:ident : tactic => do
  let rId := mkIdent `R
  let hpcId := mkIdent `hpc
  let hrunId := mkIdent `hrun
  let hpreId := mkIdent `hpre
  let hspId := mkIdent `hsp_align
  evalTactic (← `(tactic| (
    apply subroutine_ok_lscl_of_sepWPp
    wp_unfold_specs
    intro $a:ident $rId:ident $s0:ident $hpcId:ident $hrunId:ident $hcl:ident $hpreId:ident $hspId:ident)))
  wpSplitAndNormHyps (unpackProds := false)
  let g ← getMainGoal
  let (pExpr, fExpr) ← g.withContext do
    let lctx ← getLCtx
    let rFVar := (lctx.findFromUserName? rId.getId).map (·.toExpr)
    let mut fullPreOpt : Option Expr := none
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``SepProp.Satisfies 2 then
          fullPreOpt := some (ty.getArg! 0)
          break
    let fullPre := fullPreOpt.getD (rFVar.getD (mkConst ``SepProp.emp))
    let atoms := SepSolver.atoms fullPre
    let spatial := atoms.filter (fun (e : Expr) => rFVar != some e)
    let conj : Expr :=
      if spatial.isEmpty then mkConst ``SepProp.emp
      else
        let n := spatial.size
        (List.range (n - 1)).foldr
          (fun i acc => mkApp2 (mkConst ``SepProp.sepConj) spatial[i]! acc) spatial[n - 1]!
    Pure.pure (conj, rFVar.getD (mkConst ``SepProp.emp))
  let pStx ← g.withContext (PrettyPrinter.delab pExpr)
  let fStx ← g.withContext (PrettyPrinter.delab fExpr)
  evalTactic (← `(tactic| (
    refine ⟨$pStx, $fStx, ?_, ?_⟩
    wp_focus_close arm64_sep_close)))

set_option maxHeartbeats 800000 in
/-- `<PolyDecoder as Decoder>::add_chunk` (Block `419`, 129 instructions) satisfies
    `withLsCodeLoaded lsmpl (addChunkBsearchSpec A)` under `[LibsignalPlacement]`. -/
theorem add_chunk_bsearch_cl_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtFullSpec A)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtSpec A))) :
    subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkBsearchSpec A)) := by
  conv => arg 3; arg 2; simp only [addChunkBsearchSpec, polyDecoderAt, chunkAt, chunkIndexOff,
    stackAt_addChunk_split, addChunkBsearch_pts_length, addChunkBsearch_ptsNeeded,
    addChunkBsearch_isComplete, sepExists_sepConj_right, sepConj_assoc]
  wpp_init_lscl x s0 hcl0
  have hsp0 : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
  have hloop := @addChunk_loop_cl_placed_wpp _ A ext hmemmove_sat hgrow_full hgrow_empty (s0.readReg64 .lr) s0
  apply of_sepWP_lscl hcl0 (mid := (blkPl_419).base + 76#64); wp_steps 14
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  intro hcl1
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hloop (F := ((x.decA + polyDecoderIsCompleteOff) ↦₈ boolByte x.dec.isComplete) ∗
        memRegion (x.decA + polyDecoderPadOff) polyDecoderPadSize ∗ ((x.chunkA + 32#64) ↦₁₆ x.chunk.index) ∗
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      x.decA x.chunkA (s0.sp - 96#64) x.chunk 15 0 x.dec _ hcl1 rfl h_3 h
      (fun j hj _ => h_1 (x.dec.pts[j]'hj) (List.getElem_mem hj))
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
      (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (fun sf hcl_f hpc_f hrun_f hsp_f htr_f _hx29_f _hvregs_f => ?_))
  change SepWPp _ _ sf (sortedSetPtListOf A x.decA (addChunkBsearch x.dec x.chunk).pts ∗ _) _ _
  apply SepWPp.of_sepWP_ret
  wp_steps 7
  wp_done

/-- `<PolyDecoder as Decoder>::add_chunk` (Block `419`, 129 instructions) satisfies
    `withLsCodeLoaded lsmpl (addChunkSpec A)` under `[LibsignalPlacement]`. -/
theorem add_chunk_cl_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtFullSpec A)))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (growOnePtSpec A))) :
    subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  simp only [withLsCodeLoaded, addChunkSpec, polyDecoderAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hsort⟩, ⟨hlen, hneed⟩, hmem_cl⟩
  have hcap : ∀ s ∈ x.dec.pts, s.vec.length ≤ 65536 :=
    fun s hs => ptListStrictSorted_length_le (hsort s hs)
  have hpre_b : s0.mem ⊨ (withLsCodeLoaded lsmpl (addChunkBsearchSpec A)).pre x s0 ∗ R := by
    simp only [withLsCodeLoaded, addChunkBsearchSpec, polyDecoderAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hcap⟩, ⟨hlen, hneed⟩, hmem_cl⟩
  refine subroutine_ok.mono_outcome
    (add_chunk_bsearch_cl_placed_ok_ext hmemmove_sat hgrow_full hgrow_empty)
    x R s0 hpc hrun hpre_b hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hb_eq, hsort'⟩ := addChunkBsearch_eq_addChunkTotal x.dec x.chunk hlen hsort
    simp only [withLsCodeLoaded, addChunkBsearchSpec, addChunkSpec, hb_eq, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1, hsort'⟩, hq.2⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

/-- Closed `[LibsignalPlacement]` contract for `<PolyDecoder as Decoder>::add_chunk` (Block `419`)
with `withLsCodeLoaded lsmpl (addChunkSpec A)`, discharging Block `357` (`grow_one_pt_full_placed_ok` /
`grow_one_pt_placed_ok`) purely from `HookSat` contracts. -/
theorem add_chunk_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack)) :
    subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpec A)) :=
  add_chunk_cl_placed_ok_ext hmemmove_sat
    (ls_subroutine_ok_of_block (i := 419) (j := 357)
      (grow_one_pt_full_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (i := 419) (j := 357)
      (grow_one_pt_placed_ok h_panic hshim halloc hrealloc))

/-- Closed `[LibsignalPlacement]` contract for `<PolyDecoder as Decoder>::add_chunk` (Block `419`)
with `withLsCodeLoaded lsmpl (addChunkSpecX A)`. -/
theorem add_chunk_cl_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack)) :
    subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX A)) :=
  addChunkSpecX_cl_of_addChunkSpec_cl
    (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove_sat)

/-- Closed `[LibsignalPlacement]` contract for `<PolyDecoder as Decoder>::add_chunk` (Block `419`)
with `withLsCodeRoLoaded lsmpl (addChunkSpec A)`. -/
theorem add_chunk_cro_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack)) :
    subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeRoLoaded lsmpl (addChunkSpec A)) :=
  LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (add_chunk_cl_placed_ok h_panic hshim halloc hrealloc hmemmove_sat)

/-- Closed `[LibsignalPlacement]` contract for `<PolyDecoder as Decoder>::add_chunk` (Block `419`)
with `withLsCodeRoLoaded lsmpl (addChunkSpecX A)`. -/
theorem add_chunk_cro_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack)) :
    subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeRoLoaded lsmpl (addChunkSpecX A)) :=
  LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (add_chunk_cl_placed_ok_x h_panic hshim halloc hrealloc hmemmove_sat)

end CryptoVerification.SpqrV1.Poly.AddChunk

namespace CryptoVerification.SpqrV1.States.Leaves
export CryptoVerification.SpqrV1.Poly.AddChunk (
  add_chunk_bsearch_cl_placed_ok_ext
  add_chunk_cl_placed_ok_ext
  add_chunk_cl_placed_ok
  add_chunk_cl_placed_ok_x
  add_chunk_cro_placed_ok
  add_chunk_cro_placed_ok_x
)
end CryptoVerification.SpqrV1.States.Leaves
