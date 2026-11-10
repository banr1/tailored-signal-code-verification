/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Mid
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Proof
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<Ct1SentEkReceived>::send_ct2`: Closed `[LibsignalPlacement]` Contract (Block `347`)

Discharges the cross-block callees `do_reserve_and_handle` (Block `320`) and `slice::Concat::concat`
(Block `386`) of `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` (Block `347`) from
`HookSat` and panic hooks under `withLsCodeLoaded` and `withLsCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open NextKeyInternalFacts AgreeStateSimp DoReserveNorm

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length ctLabel_length

theorem SepWPp.call_allowPanic_mid_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {x : α} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧ (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl hcall
    hpc hrun hsp_align hlr ?_ ?_ ?_ hnext ?_
  · intro R' hm
    have hm' := hpre R' hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hm'⟩
  · intro sf code R' _ hpost
    rw [hexit_eq.1] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sf _ hm'
    exact Satisfies.mono (sepConj_mono_left (hpan sf)) hm'
  · intro sf R' _ hpost
    rw [hexit_eq.2] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

open Lean Elab Tactic in
elab "wpp_call_sendCt2_lscl " hcall:term:max hcl:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hclId ← freshIdent `hcl_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_mid_lscl $hcall $hcl (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_sendCt2_lscl: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR'
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm, *]
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_entails_of_trace_eq (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hclId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

set_option maxHeartbeats 1200000 in
theorem send_ct2_reserve_ct1_cl_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (x : UnchunkedSendCt2Ghost F)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_347).base + 656#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64),
      LibsignalCodeLoaded lsmpl st'.mem →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (blkPl_347).base + 676#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          A.pool ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PlacedPostQ A F K x s0 R)
        (sendCt2PlacedPostQp A F K x s0 R)) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (vecU8At A (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      (sendCt2PlacedPostQ A F K x s0 R)
      (sendCt2PlacedPostQp A F K x s0 R) := by
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm
  refine SepWPp.fold (vecU8At_expose_sp_304_cells_heap A s0.sp cap_ct1 ptr_ct1 x.st.ct1) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hct1_le, hct1_lt, hptr_ct1_ne⟩
  by_cases hls : ¬ (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true
  · have hls_f : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = false :=
      Bool.eq_false_iff.mpr hls
    have hge128 : x.st.ct1.length + 128 ≤ cap_ct1.toNat :=
      le_of_not_ule_sub_len hct1_le hct1_lt hls
    have hcap_ct1_ne : cap_ct1 ≠ 0#64 := cap_ne_zero_of_add_128_le hge128
    refine SepWPp.fold (vecU8HeapAt_expose_of_ne_zero A cap_ct1 ptr_ct1 x.st.ct1 hcap_ct1_ne) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
    refine of_sepWP_lscl hcl (mid := (blkPl_347).base + 676#64) ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hcl'
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ cap_ct1 ptr_ct1 hcl' hcap_ct1_ne hge128 hct1_lt hptr_ct1_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]))
  · have hls_t : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true := Classical.not_not.mp hls
    have hbound := reserveCap_bound_of_ule_sub_len hct1_le hct1_lt32 hls_t
    refine of_sepWP_lscl hcl (mid := lsmpl.base 320) ?_
    wp_steps
    refine SepWP.fold (fold_vecU8At_sp_304 A s0.sp cap_ct1 ptr_ct1 x.st.ct1) (by sep_focus) ?_
    have hstack_res :
        stackAt (s0.sp - 336#64) extHookStack ⊢
          memRegion (s0.sp - 16720#64) 12176 ∗ stackAt (s0.sp - 336#64) doReserveStack :=
      Entails.of_eq (stackAt_extHook_eq_doReserve s0.sp)
    refine SepWP.fold hstack_res (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hcl_call
    wpp_call_sendCt2_lscl h_res hcl_call
      (⟨s0.sp - 304#64, cap_ct1, ptr_ct1, x.st.ct1, 128⟩ : DoReserveCall)
    let ptr_ct1' := w
    have hcap_ct1'_ne : BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128) ≠ 0#64 :=
      reserveCap_ne_zero_len hbound
    refine SepWPp.fold
      (vecU8At_expose_sp_304_of_ne_zero A s0.sp
        (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128))
        ptr_ct1' x.st.ct1 hcap_ct1'_ne)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, hmax_ct1', hptr_ct1'_ne⟩
    have hge128' :
        x.st.ct1.length + 128 ≤ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat :=
      reserveCap_ge_add_128 hbound
    refine of_sepWP_lscl hcl_sf (mid := (blkPl_347).base + 676#64) ?_
    wp_steps
    have hstack_back :
        memRegion (s0.sp - 16720#64) 12176 ∗ stackAt st.sp doReserveStack ⊢
          stackAt (s0.sp - 336#64) extHookStack := by
      rw [hsp, ← stackAt_extHook_eq_doReserve s0.sp]
      exact Entails.refl _
    refine SepWP.fold hstack_back (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hcl'
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ptr_ct1'
        hcl' hcap_ct1'_ne hge128' hmax_ct1' hptr_ct1'_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]))

set_option maxHeartbeats 1200000 in
theorem send_ct2_5d8_to_604_cl_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpySpec)
    (hpan : ((blkPC_347).rebase (blkPl_347).base H).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked)
    (x : UnchunkedSendCt2Ghost F) (esPtr : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 0x1d8#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      LibsignalCodeLoaded lsmpl st'.mem →
      esWorkPtr ≠ 0#64 →
      st'.pc = (blkPl_347).base + 0x204#64 →
      st'.status = .Running → st'.sp = s0.sp - 336#64 → st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x8 = 0#64 →
      st'.readReg64 .x19 = esPtr → st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 → st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 → st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 → st'.readReg64 .x28 = 2080#64 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (esWorkPtr ↦ₛ x.st.es) ∗
          A.live esWorkPtr 2080 1 ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        (sendCt2PlacedPostQ A F K x s0 R) (sendCt2PlacedPostQp A F K x s0 R)) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (sendCt2PlacedPostQ A F K x s0 R) (sendCt2PlacedPostQp A F K x s0 R) := by
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19
  refine of_sepWP_lscl hcl (mid := (blkPl_347).base + 488#64) ?_
  wp_steps; wp_apply; wp_steps
  have hstack_alloc :
      stackAt (s0.sp - 336#64) extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine SepWP.fold hstack_alloc (by sep_focus) ?_
  have hlay_2080 : LayoutOk 2080 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine call_rustAlloc halloc 2080 1 hlay_2080
    (s0 := s0) (ret_pc := (blkPl_347).base + 488#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hcl1
  by_cases hoom : sf1.readReg64 (Reg.gpr 0#5) = 0
  · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_oom => ?_
    refine SepWPp.of_sepWP_mid
      (mid := lsρ spqrHandleErrorSym) ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
      (by simpa [wp_norm, arm64_norm] using hpan) fun hm => ?_
    dsimp only [sendCt2PlacedPostQp, sendCt2PostQp, unchunkedCt1SentEkReceivedSendCt2Spec]
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htr_ok⟩ => ?_
    have hoom_false : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
    refine of_sepWP_lscl hcl1 (mid := (blkPl_347).base + 0x204#64) ?_
    have hstack_back :
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
          stackAt (s0.sp - 336#64) extHookStack :=
      Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
    refine SepWP.fold hstack_back (by sep_focus) ?_
    have hmr_es :
        memRegion (sf1.readReg64 (Reg.gpr 0#5)) 2080 ⊢
          memRegion (sf1.readReg64 (Reg.gpr 0#5)) x.st.es.length := by
      rw [hes_len]; exact Entails.refl _
    refine SepWP.fold hmr_es (by sep_focus) ?_
    wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hcl'
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ (sf1.readReg64 (Reg.gpr 0#5)) hcl' hoom
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [Reg.x8, wp_norm, arm64_norm, *])
        (by simp only [Reg.x19, wp_norm, arm64_norm, *])
        (by simp only [Reg.x20, wp_norm, arm64_norm, *])
        (by simp only [Reg.x22, wp_norm, arm64_norm, *])
        (by simp only [Reg.x23, wp_norm, arm64_norm, *])
        (by simp only [Reg.x24, wp_norm, arm64_norm, *])
        (by simp only [Reg.x25, wp_norm, arm64_norm, *])
        (by simp only [Reg.x26, wp_norm, arm64_norm, *])
        (by simp only [Reg.x27, wp_norm, arm64_norm, *])
        (by simp only [Reg.x28, wp_norm, arm64_norm, *])
        (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

set_option maxHeartbeats 1200000 in
theorem send_ct2_scan_to_628_cl_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpySpec)
    (hpan : ((blkPC_347).rebase (blkPl_347).base H).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked)
    (x : UnchunkedSendCt2Ghost F) (esPtr : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 0x88#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64) (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64) (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64) (hx19 : st.readReg64 .x19 = esPtr)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      LibsignalCodeLoaded lsmpl st'.mem →
      st'.pc = (blkPl_347).base + 0x228#64 →
      st'.status = .Running → st'.sp = s0.sp - 336#64 → st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr → st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64) →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 → st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 → st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)) →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (sendCt2EsWorkAt A esPtr esWorkPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        (sendCt2PlacedPostQ A F K x s0 R) (sendCt2PlacedPostQp A F K x s0 R)) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (sendCt2PlacedPostQ A F K x s0 R) (sendCt2PlacedPostQp A F K x s0 R) := by
  have hlen512 : ((x.st.es.drop 1536).take 512).length = 512 := by
    rw [List.length_take, List.length_drop, hes_len]; rfl
  have hbs_ne : (x.st.es.drop 1536).take 512 ≠ [] := by intro hnil; rw [hnil] at hlen512; contradiction
  have hbs_mod : ((x.st.es.drop 1536).take 512).length % 2 = 0 := by rw [hlen512]
  have hbs_le : ((x.st.es.drop 1536).take 512).length ≤ 512 := by omega
  have hrem_eq : (512#64 : BitVec 64) = BitVec.ofNat 64 ((x.st.es.drop 1536).take 512).length := by rw [hlen512]
  have hpre_eq :
      ((esPtr ↦ₛ x.st.es) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) =
      (((esPtr + 1536#64) ↦ₛ ((x.st.es.drop 1536).take 512)) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
    rw [es_scan_split esPtr x.st.es hes_len]; ac_rfl
  by_cases hflip : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = false
  · refine of_sepWP_lscl hcl (mid := (blkPl_347).base + 0x228#64) ?_
    rw [hpre_eq]
    refine SepWP.mono
      (scan_loop_false_placed_ok (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hbs_ne hbs_mod hbs_le hrem_eq hflip hpc hrun hx8 hx9 hx10 hx11 hx13 hx28) ?_
    rintro sf Pf hpc_sf hrun_sf ⟨hPf, hx21_sf, hx22_sf, hx28_sf, hsaved⟩ hcl_sf
    have hwork : (esPtr ↦ₛ x.st.es) ⊢ sendCt2EsWorkAt A esPtr esPtr x.st.es := by
      unfold sendCt2EsWorkAt; simp only [hflip, Bool.false_eq_true, ↓reduceIte]
      exact Entails.pure_right trivial (Entails.refl _)
    have hPf_back : Pf ⊢
        sendCt2EsWorkAt A esPtr esPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf, ← hpre_eq]; exact sepConj_mono_left hwork
    refine SepWPp.fold hPf_back (sepConj_emp _).symm (SepWPp.rw_pre (sepConj_emp _) ?_)
    exact hcont sf esPtr hcl_sf hpc_sf hrun_sf
      (hsaved.sp.trans hsp) (hsaved.trace.trans htr) (hsaved.vregs.trans hvregs) (hsaved.x19.trans hx19) hsaved.x20
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx21_sf]) (hx22_sf.trans hx19)
      hsaved.x23 hsaved.x24 hsaved.x25 hsaved.x26 hsaved.x27
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx28_sf]) hsaved.x29
  · have hflip_t : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = true :=
      Bool.eq_true_of_not_eq_false hflip
    refine of_sepWP_lscl hcl (mid := (blkPl_347).base + 0x1d8#64) ?_
    rw [hpre_eq]
    refine SepWP.mono
      (scan_loop_true_placed_ok (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hbs_ne hbs_mod hbs_le hrem_eq hflip_t hpc hrun hx8 hx9 hx10 hx11 hx13) ?_
    rintro s5d8 P5d8 hpc_5d8 hrun_5d8 ⟨hP5d8, hsaved1⟩ hcl_5d8
    have hP5d8_eq : P5d8 =
        (esPtr ↦ₛ x.st.es) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame) := by
      rw [hP5d8, ← hpre_eq]; ac_rfl
    rw [hP5d8_eq]
    refine send_ct2_5d8_to_604_cl_placed_wpp hshim halloc hmemcpy hpan x esPtr s0 s5d8
      ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame) R hcl_5d8
      hes_len hpc_5d8 hrun_5d8 (hsaved1.sp.trans hsp) hsp_s0 (hsaved1.trace.trans htr)
      (hsaved1.vregs.trans hvregs) (hsaved1.x19.trans hx19) ?_
    intro s604 esWorkPtr hcl604 hwork_ne hpc604 hrun604 hsp604 htr604 hvregs604 hx8_604 hx19_604 hx20_604 hx22_604 hx23_604 hx24_604 hx25_604 hx26_604 hx27_604 hx28_604 hx29_604
    refine of_sepWP_lscl hcl604 (mid := (blkPl_347).base + 0x228#64) ?_
    have h2048_len : (x.st.es.take 2048).length = 2048 := by rw [List.length_take, hes_len]; rfl
    have h2048_ne : x.st.es.take 2048 ≠ [] := by intro hnil; rw [hnil] at h2048_len; contradiction
    have h2048_mod : (x.st.es.take 2048).length % 2 = 0 := by rw [h2048_len]
    have h2048_sum : (0#64 : BitVec 64).toNat + (x.st.es.take 2048).length = 2048 := by rw [h2048_len]; rfl
    have hsplit_swap :
        (esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame) =
        (((esWorkPtr + 0#64) ↦ₛ (x.st.es.take 2048)) ∗
          (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
            (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
      rw [es_swap_split esWorkPtr x.st.es hes_len]; ac_rfl
    rw [hsplit_swap]
    refine SepWP.mono
      (swap_loop_placed_ok esWorkPtr (x.st.es.take 2048) 0#64 s604
        (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
          (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        h2048_ne h2048_mod h2048_sum hpc604 hrun604 hx22_604 hx8_604) ?_
    rintro st' Pf2 hpc' hrun' ⟨hPf2, hx21', hsaved2⟩ hcl'
    have hwork :
        (esPtr ↦ₛ x.st.es) ∗
          (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1 ⊢
          sendCt2EsWorkAt A esPtr esWorkPtr x.st.es := by
      unfold sendCt2EsWorkAt; simp only [hflip_t, ↓reduceIte]
      exact Entails.pure_right hwork_ne (Entails.of_eq (by ac_rfl))
    have hpost_ent : Pf2 ⊢
        sendCt2EsWorkAt A esPtr esWorkPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf2, ← sepConj_assoc, es_swap_join _ _ hes_len]
      refine Entails.trans (Entails.of_eq (show _ =
        ((esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1) ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) by ac_rfl)) ?_
      exact sepConj_mono_left hwork
    refine SepWPp.fold hpost_ent (sepConj_emp _).symm (SepWPp.rw_pre (sepConj_emp _) ?_)
    exact hcont st' esWorkPtr hcl' hpc' hrun'
      (hsaved2.sp.trans hsp604) (hsaved2.trace.trans htr604) (hsaved2.vregs.trans hvregs604)
      (hsaved2.x19.trans hx19_604)
      ((hsaved2.x20.trans hx20_604).trans hsaved1.x20)
      (by simp only [hflip_t, ↓reduceIte, hx21'])
      (hsaved2.x22.trans hx22_604)
      ((hsaved2.x23.trans hx23_604).trans hsaved1.x23)
      ((hsaved2.x24.trans hx24_604).trans hsaved1.x24)
      ((hsaved2.x25.trans hx25_604).trans hsaved1.x25)
      ((hsaved2.x26.trans hx26_604).trans hsaved1.x26)
      ((hsaved2.x27.trans hx27_604).trans hsaved1.x27)
      (by simp only [hflip_t, ↓reduceIte, hsaved2.x28.trans hx28_604])
      ((hsaved2.x29.trans hx29_604).trans hsaved1.x29)

set_option maxHeartbeats 1200000 in
theorem send_ct2_628_to_690_cl_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {H : String → Option (State → State)}
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (mlkemEncaps2Spec K))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (hpan : ((blkPC_347).rebase (blkPl_347).base H).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked)
    (x : UnchunkedSendCt2Ghost F)
    (esPtr ekPtr esWorkPtr : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hpc : st.pc = (blkPl_347).base + 0x228#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx21 : st.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64))
    (hx22 : st.readReg64 .x22 = esWorkPtr)
    (hx27 : st.readReg64 .x27 = 1152#64)
    (hx28 : st.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)))
    (hcont : ∀ (st' : State) (ptr_ct2 : BitVec 64),
      LibsignalCodeLoaded lsmpl st'.mem →
      ptr_ct2 ≠ 0#64 →
      st'.pc = (blkPl_347).base + 656#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = ekPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          A.pool ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PlacedPostQ A F K x s0 R)
        (sendCt2PlacedPostQp A F K x s0 R)) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (sendCt2EsWorkAt A esPtr esWorkPtr x.st.es ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        A.pool ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      (sendCt2PlacedPostQ A F K x s0 R)
      (sendCt2PlacedPostQp A F K x s0 R) := by
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hek_beq : (ekPtr == 0#64) = false := beq_false_of_ne hekPtr_ne
  have hct2_len : x.ct2.length = 128 := by rw [hct2_eq]; exact (K.encaps2 esVec ekVec).2
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx27 hx28
  refine SepWPp.fold (sendCt2EsWorkAt_entails A esPtr esWorkPtr x.st.es hesVec) (by sep_focus) ?_
  refine SepWPp.rw_pre (by rw [← hekVec]) ?_
  refine of_sepWP_lscl hcl (mid := (blkPl_347).base + 596#64) ?_
  wp_steps
  refine call_mlkemEncaps2 henc (s0.sp - 272#64) esWorkPtr ekPtr esVec ekVec
    (s0 := s0) (ret_pc := (blkPl_347).base + 580#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x8, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 htr1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1
  wp_steps; wp_apply; wp_steps
  have hstack_alloc :
      stackAt (s0.sp - 336#64) extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine SepWP.fold hstack_alloc (by sep_focus) ?_
  have hlay_128 : LayoutOk 128 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine call_rustAlloc halloc 128 1 hlay_128
    (s0 := s0) (ret_pc := (blkPl_347).base + 596#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hcl2
  by_cases hoom : sf2.readReg64 (Reg.gpr 0#5) = 0
  · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_oom => ?_
    refine SepWPp.of_sepWP_mid
      (mid := lsρ spqrHandleErrorSym) ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
      (by simpa [wp_norm, arm64_norm] using hpan) fun hm => ?_
    dsimp only [sendCt2PlacedPostQp, sendCt2PostQp, unchunkedCt1SentEkReceivedSendCt2Spec]
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htr_ok⟩ => ?_
    have hoom_false : (sf2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, hct2_cells⟩ :=
      exists_unpack64_of_length_128 hct2_len
    refine SepWPp.rw_pre (by
      rw [← hct2_eq, hekVec,
        hct2_cells (s0.sp - 272#64),
        memRegion_128_cells (sf2.readReg64 (Reg.gpr 0#5))]) ?_
    sep_elim_exists
    by_cases hflip : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = false
    · refine SepWPp.rw_pre (by
        unfold sendCt2EsAfterWorkAt
        simp only [hflip, Bool.false_eq_true, ↓reduceIte] at hesVec ⊢
        rw [hesVec]) ?_
      refine SepWPp.pure_left_focus (esWorkPtr = esPtr) (by sep_focus) fun hwork_eq => ?_
      subst hwork_eq
      refine of_sepWP_lscl hcl2 (mid := (blkPl_347).base + 656#64) ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (hct2_cells (sf2.readReg64 (Reg.gpr 0#5))).symm) (by sep_focus) ?_
      have hsp_cells_back :
          ((s0.sp - 272#64) ↦₆₄ w0) ∗ ((s0.sp - 272#64 + 8#64) ↦₆₄ w1) ∗
            ((s0.sp - 272#64 + 16#64) ↦₆₄ w2) ∗ ((s0.sp - 272#64 + 24#64) ↦₆₄ w3) ∗
            ((s0.sp - 272#64 + 32#64) ↦₆₄ w4) ∗ ((s0.sp - 272#64 + 40#64) ↦₆₄ w5) ∗
            ((s0.sp - 272#64 + 48#64) ↦₆₄ w6) ∗ ((s0.sp - 272#64 + 56#64) ↦₆₄ w7) ∗
            ((s0.sp - 272#64 + 64#64) ↦₆₄ w8) ∗ ((s0.sp - 272#64 + 72#64) ↦₆₄ w9) ∗
            ((s0.sp - 272#64 + 80#64) ↦₆₄ w10) ∗ ((s0.sp - 272#64 + 88#64) ↦₆₄ w11) ∗
            ((s0.sp - 272#64 + 96#64) ↦₆₄ w12) ∗ ((s0.sp - 272#64 + 104#64) ↦₆₄ w13) ∗
            ((s0.sp - 272#64 + 112#64) ↦₆₄ w14) ∗ ((s0.sp - 272#64 + 120#64) ↦₆₄ w15) ⊢
            memRegion (s0.sp - 272#64) 128 := by
        rw [← hct2_cells (s0.sp - 272#64)]
        exact hct2_len ▸ pointsToBytes_entails_memRegion (s0.sp - 272#64) x.ct2
      refine SepWP.fold hsp_cells_back (by sep_focus) ?_
      have hstack_back :
          memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
            stackAt (s0.sp - 336#64) extHookStack :=
        Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
      refine SepWP.fold hstack_back (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro hcl'
      refine SepWPp.rw_pre (by ac_rfl)
        (hcont _ (sf2.readReg64 (Reg.gpr 0#5)) hcl' hoom
          (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [Reg.x19, wp_norm, arm64_norm, *])
          (by simp only [Reg.x20, wp_norm, arm64_norm, *])
          (by simp only [Reg.x23, wp_norm, arm64_norm, *])
          (by simp only [Reg.x24, wp_norm, arm64_norm, *])
          (by simp only [Reg.x25, wp_norm, arm64_norm, *])
          (by simp only [Reg.x26, wp_norm, arm64_norm, *])
          (by simp only [Reg.x27, wp_norm, arm64_norm, *])
          (by simp only [Reg.x29, wp_norm, arm64_norm, *]))
    · have hflip_t : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = true :=
        Bool.eq_true_of_not_eq_false hflip
      refine SepWPp.rw_pre (by
        unfold sendCt2EsAfterWorkAt
        simp only [hflip_t, ↓reduceIte]; rfl) ?_
      refine SepWPp.pure_left_focus (esWorkPtr ≠ 0#64) (by sep_focus) fun hwork_ne => ?_
      refine of_sepWP_lscl hcl2 (mid := (blkPl_347).base + 656#64) ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (hct2_cells (sf2.readReg64 (Reg.gpr 0#5))).symm) (by sep_focus) ?_
      have hsp_cells_back :
          ((s0.sp - 272#64) ↦₆₄ w0) ∗ ((s0.sp - 272#64 + 8#64) ↦₆₄ w1) ∗
            ((s0.sp - 272#64 + 16#64) ↦₆₄ w2) ∗ ((s0.sp - 272#64 + 24#64) ↦₆₄ w3) ∗
            ((s0.sp - 272#64 + 32#64) ↦₆₄ w4) ∗ ((s0.sp - 272#64 + 40#64) ↦₆₄ w5) ∗
            ((s0.sp - 272#64 + 48#64) ↦₆₄ w6) ∗ ((s0.sp - 272#64 + 56#64) ↦₆₄ w7) ∗
            ((s0.sp - 272#64 + 64#64) ↦₆₄ w8) ∗ ((s0.sp - 272#64 + 72#64) ↦₆₄ w9) ∗
            ((s0.sp - 272#64 + 80#64) ↦₆₄ w10) ∗ ((s0.sp - 272#64 + 88#64) ↦₆₄ w11) ∗
            ((s0.sp - 272#64 + 96#64) ↦₆₄ w12) ∗ ((s0.sp - 272#64 + 104#64) ↦₆₄ w13) ∗
            ((s0.sp - 272#64 + 112#64) ↦₆₄ w14) ∗ ((s0.sp - 272#64 + 120#64) ↦₆₄ w15) ⊢
            memRegion (s0.sp - 272#64) 128 := by
        rw [← hct2_cells (s0.sp - 272#64)]
        exact hct2_len ▸ pointsToBytes_entails_memRegion (s0.sp - 272#64) x.ct2
      refine SepWP.fold hsp_cells_back (by sep_focus) ?_
      have hwork_mr : (esWorkPtr ↦ₛ esVec.toList) ⊢ memRegion esWorkPtr 2080 := by
        simpa only [esVec.toList_length] using pointsToBytes_entails_memRegion esWorkPtr esVec.toList
      refine SepWP.fold hwork_mr (by sep_focus) ?_
      refine call_rustDealloc hdealloc esWorkPtr 2080 1
        (s0 := s0) (ret_pc := (blkPl_347).base + 656#64) (sp_call := s0.sp - 336#64)
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *]) hfsp_align
        (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *])
        (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
        (by sep_focus)
        (fun sf3 hpc3 hrun3 hsp3 htr3 hcs3 => ?_)
      rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
      simp only [arm64_norm] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3
      have hstack_back :
          memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
            stackAt (s0.sp - 336#64) extHookStack :=
        Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
      refine SepWP.fold hstack_back (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro hcl'
      refine SepWPp.rw_pre (by ac_rfl)
        (hcont _ (sf2.readReg64 (Reg.gpr 0#5)) hcl' hoom
          (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [Reg.x19, wp_norm, arm64_norm, *])
          (by simp only [Reg.x20, wp_norm, arm64_norm, *])
          (by simp only [Reg.x23, wp_norm, arm64_norm, *])
          (by simp only [Reg.x24, wp_norm, arm64_norm, *])
          (by simp only [Reg.x25, wp_norm, arm64_norm, *])
          (by simp only [Reg.x26, wp_norm, arm64_norm, *])
          (by simp only [Reg.x27, wp_norm, arm64_norm, *])
          (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

set_option maxHeartbeats 1600000 in
theorem send_ct2_append_hmac_cl_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (withLsCodeLoaded lsmpl (sliceConcat3Spec A)))
    (h_hmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSafeSpec F A))
    (h_dealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (x : UnchunkedSendCt2Ghost F)
    (mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hct2_len : x.ct2.length = 128)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 : (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hmax_ct1' : cap_ct1'.toNat < 2 ^ 63)
    (hpc : st.pc = (blkPl_347).base + 676#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State),
      st'.pc = (blkPl_347).base + 836#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = ptr_ct1' →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = mkPtr →
      st'.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
          ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          memRegion ptr_ct1' cap_ct1'.toNat ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          (mkPtr ↦ₛ x.st.auth.macKey) ∗
          vecU8 A (s0.sp - 272#64) x.mac ∗
          memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 80 ∗
          memRegion (s0.sp - 144#64) 24 ∗
          ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
          ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
          A.pool ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PlacedPostQ A F K x s0 R)
        (sendCt2PlacedPostQp A F K x s0 R)) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        (ptr_ct1' ↦ₛ x.st.ct1) ∗
        memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
        A.pool ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      (sendCt2PlacedPostQ A F K x s0 R)
      (sendCt2PlacedPostQp A F K x s0 R) := by
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx1 hx25 hx26 hx27 hx29
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hct2_cells⟩ :=
    exists_unpack64_of_length_128 hct2_len
  refine SepWPp.rw_pre (by
    rw [memRegion_ct1_split_128_len ptr_ct1' hge128 hmax_ct1',
      memRegion_128_cells (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length),
      hct2_cells ptr_ct2,
      memRegion_sp_272_split_48_80 s0.sp]) ?_
  sep_elim_exists
  refine of_sepWP_lscl hcl (mid := lsmpl.base 386) ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (hct2_cells ptr_ct2).symm) (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (hct2_cells (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)).symm)
    (by sep_focus) ?_
  refine SepWP.fold
    (pointsToBytes_append_ct1_ct2 ptr_ct1' x.st.ct1 x.ct2)
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 120#64) x.st.epoch))
    (by sep_focus) ?_
  have hct1_full_len :
      BitVec.ofNat 64 x.st.ct1.length + 128#64 = BitVec.ofNat 64 (x.st.ct1 ++ x.ct2).length := by
    rw [List.length_append, hct2_len]; bv_omega
  have hconcat3_bound :
      35 + 8 + (x.st.ct1 ++ x.ct2).length < 9223372036854775808 := by
    have hd : (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length =
        35 + 8 + (x.st.ct1 ++ x.ct2).length := by
      rw [List.length_append, List.length_append, ctLabel_length, toBEBytes_8_length]
    omega
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hcl_call
  wpp_call_sendCt2_lscl h_concat3 hcl_call
    (⟨s0.sp - 144#64, s0.sp - 272#64,
      true, lsρ "spqr:.rodata..Lanon.137", Authenticator.ctLabel,
      false, s0.sp - 120#64, toBEBytes 8 x.st.epoch,
      false, ptr_ct1', x.st.ct1 ++ x.ct2⟩ : SliceConcat3Ghost)
  simp only [hsp, hx25, hx26, hx27, hx29] at hsp_sf h_6 h_7 h_8 hcs_sf
  rw [← List.append_assoc Authenticator.ctLabel]
  have hdata_pos :
      0 < (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length := by
    simp only [List.length_append, ctLabel_length]
    omega
  refine SepWPp.fold
    (vecU8_expose_nonempty_144 A s0.sp
      (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2))
      hdata_pos)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_md ptr_md
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_md_ne, hlay_md, hptr_md_ne, hle_md⟩
  have ⟨_, _, hmax_md⟩ := hlay_md
  have hcap_md_beq : (cap_md == 0#64) = false := beq_false_of_ne hcap_md_ne
  refine SepWPp.fold
    (fold_sp_272_24_24 s0.sp
      (lsρ "spqr:.rodata..Lanon.137") 35#64
      (s0.sp - 120#64) 8#64 ptr_ct1'
      (BitVec.ofNat 64 (x.st.ct1 ++ x.ct2).length))
    (by sep_focus) ?_
  have hfold_ct1 :
      (ptr_ct1' ↦ₛ (x.st.ct1 ++ x.ct2)) ∗
        memRegion (ptr_ct1' + BitVec.ofNat 64 (x.st.ct1.length + 128)) (cap_ct1'.toNat - (x.st.ct1.length + 128)) ⊢
        memRegion ptr_ct1' cap_ct1'.toNat := by
    rw [← show (x.st.ct1 ++ x.ct2).length = x.st.ct1.length + 128 by rw [List.length_append, hct2_len]]
    exact bytes_rem_entails_memRegion_cap ptr_ct1' cap_ct1' (x.st.ct1 ++ x.ct2)
      (by rw [List.length_append, hct2_len]; omega) hmax_ct1'
  refine SepWPp.fold hfold_ct1 (by sep_focus) ?_
  refine SepWPp.of_sepWP_mid (mid := lsρ spqrLibcruxHmacSym) ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (show stackAt st.sp extHookStack = stackAt sf.sp extHookStack by rw [hsp, hsp_sf]))
    (by sep_focus) ?_
  have hmk_toNat : (BitVec.ofNat 64 x.st.auth.macKey.length).toNat = x.st.auth.macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdata_toNat :
      (BitVec.ofNat 64 (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length).toNat =
        (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  wpp_call_sendCt2 h_hmac
    (⟨s0.sp - 272#64, mkPtr, x.st.auth.macKey,
      ptr_md, Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)⟩ : LibcruxHmacCall)
  rw [hsp_sf] at hsp_sf_1
  rw [hcs_sf] at hcs_sf_1
  rw [← List.append_assoc Authenticator.ctLabel, ← macCtUnchecked_eq_hmacWith F x.st.auth x.st.epoch (x.st.ct1 ++ x.ct2), ← hmac_eq]
  refine SepWPp.fold
    (bytes_rem_entails_memRegion_cap ptr_md cap_md
      (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2))
      hle_md hmax_md)
    (by sep_focus) ?_
  refine SepWPp.of_sepWP_mid (mid := (blkPl_347).base + 836#64) ?_
  wp_steps
  refine SepWP.fold
    (fold_sp_144_24 s0.sp cap_md ptr_md
      (BitVec.ofNat 64 (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length))
    (by sep_focus) ?_
  have hstack_alloc :
      stackAt sf.sp extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack := by
    rw [hsp_sf]
    exact Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine SepWP.fold hstack_alloc (by sep_focus) ?_
  have hcap_md_toNat : (cap_md).toNat = cap_md.toNat := rfl
  refine call_rustDealloc h_dealloc ptr_md cap_md.toNat 1
    (s0 := s0) (ret_pc := (blkPl_347).base + 836#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 htr_sf2 hcs2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2
  have hstack_back :
      memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
        stackAt (s0.sp - 336#64) extHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
  refine SepWP.fold hstack_back (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.rw_pre (by ac_rfl)
    (hcont sf2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.x19, wp_norm, arm64_norm, *]) (by simp only [Reg.x20, wp_norm, arm64_norm, *])
      (by simp only [Reg.x22, wp_norm, arm64_norm, *]) (by simp only [Reg.x23, wp_norm, arm64_norm, *])
      (by simp only [Reg.x24, wp_norm, arm64_norm, *]) (by simp only [Reg.x25, wp_norm, arm64_norm, *])
      (by simp only [Reg.x26, wp_norm, arm64_norm, *]) (by simp only [Reg.x27, wp_norm, arm64_norm, *])
      (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

/-- Relocatable `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` (Block `347`)
satisfies `withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)`
from `withLsCodeLoaded` contracts on Block `320` and Block `386`. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_of_contracts [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {H : String → Option (State → State)}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (withLsCodeLoaded lsmpl (sliceConcat3Spec A)))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpySpec)
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (mlkemEncaps2Spec K))
    (hhmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSpec F A))
    (hpan : ((blkPC_347).rebase (blkPl_347).base H).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)) := by
  have hhmac_safe := libcrux_hmac_safe_of_subroutine_ok hhmac
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre0 hsp
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre0
  refine ⟨(unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K).pre x s0, R, hpre, ?_⟩
  change SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) s0
    ((unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K).pre x s0)
    (sendCt2PlacedPostQ A F K x s0 R)
    (sendCt2PlacedPostQp A F K x s0 R)
  dsimp only [unchunkedCt1SentEkReceivedSendCt2PlacedSpec]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hx0, hx1, hmodel⟩
  obtain ⟨henc_ok, hmac_ok, houtUc⟩ := send_ct2_ok_elim hmodel
  obtain ⟨hes_len, hek_len, esVec, ekVec, hesVec, hekVec, hct2_eq⟩ := encaps2_ok_elim henc_ok
  obtain ⟨hmk_lt32, hdata_lt32, hmac_eq⟩ := macCt_ok_elim hmac_ok
  have hct2_len : x.ct2.length = 128 := by rw [hct2_eq]; exact (K.encaps2 esVec ekVec).2
  have hct1_lt32 : x.st.ct1.length < 2 ^ 32 := by
    simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len] at hdata_lt32
    omega
  unfold unchunkedCt1SentEkReceivedAt authenticatorAt
  refine SepWPp.fold (vecU8_entails_cells_and_heap A x.stA x.st.auth.rootKey) (by sep_focus) ?_
  sep_elim_exists; rename_i rkCap rkPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hrk_le, hrk_max, hrk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A (x.stA + 24#64) x.st.auth.macKey) (by sep_focus) ?_
  sep_elim_exists; rename_i mkCap mkPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hmk_le, hmk_max, hmk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A (x.stA + 48#64) x.st.es) (by sep_focus) ?_
  sep_elim_exists; rename_i esCap esPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hes_le, hes_max, hes_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A (x.stA + 72#64) x.st.ek) (by sep_focus) ?_
  sep_elim_exists; rename_i ekCap ekPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hek_le, hek_max, hek_ne⟩
  refine SepWPp.fold (vecU8_entails_cells_and_heap A (x.stA + 96#64) x.st.ct1) (by sep_focus) ?_
  sep_elim_exists; rename_i ct1Cap ct1Ptr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hct1_le, hct1_max, hct1_ne⟩
  refine SepWPp.rw_pre (by rw [stackAt_unchunkedSendCt2_split s0.sp]) ?_
  sep_elim_exists; rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 e0 s64 l0 l1 l2 l3 l4 l5
  refine SepWPp.rw_pre ?_
    (of_sepWP_lscl hcl0
      (mid := (blkPl_347).base + 0x88#64)
      (SepWP.mono
        (send_ct2_prologue_to_scan_placed A x.outA x.stA x.st
          rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr
          l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 s0
          (memRegion x.outA 104 ∗
            vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey ∗
            (mkPtr ↦ₛ x.st.auth.macKey) ∗ Unchunked.vecU8Tail A mkCap mkPtr x.st.auth.macKey ∗
            (esPtr ↦ₛ x.st.es) ∗ Unchunked.vecU8Tail A esCap esPtr x.st.es ∗
            (ekPtr ↦ₛ x.st.ek) ∗ Unchunked.vecU8Tail A ekCap ekPtr x.st.ek ∗
            unchunkedSendCt2PlacedRoAt ∗ A.pool ∗
            stackAt (s0.sp - 336#64) extHookStack ∗
            memRegion (s0.sp - 336#64) 8 ∗
            memRegion (s0.sp - 280#64) 8 ∗
            memRegion (s0.sp - 144#64) 24 ∗
            memRegion (s0.sp - 112#64) 16)
          hes_len hek_len hpc hrun hsp hx0 hx1)
        ?_))
  · ac_rfl
  rintro st1 _ hpc1 hrun1 ⟨rfl, hsp1, htr1, hvregs_1, hx8_1, hx9_1, hx10_1, hx11_1, hx13_1,
    hx19_1, hx20_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hcl1
  let F_base : SepProp :=
    memRegion x.outA 104 ∗
    (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
    ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
    ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
    ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
    memRegion (x.stA + 48#64) 80 ∗
    vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey ∗
    Unchunked.vecU8Tail A mkCap mkPtr x.st.auth.macKey ∗
    ((s0.sp - 328#64) ↦₆₄ esCap) ∗ Unchunked.vecU8Tail A esCap esPtr x.st.es ∗
    ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ Unchunked.vecU8Tail A ekCap ekPtr x.st.ek ∗
    memRegion (s0.sp - 336#64) 8 ∗
    memRegion (s0.sp - 280#64) 8 ∗
    memRegion (s0.sp - 112#64) 16 ∗
    sendCt2CalleeSavedAt s0
  refine SepWPp.rw_pre ?_
    (send_ct2_scan_to_628_cl_placed_wpp hshim halloc hmemcpy hpan x esPtr s0 st1
      (F_base ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) R hcl1
      hes_len hpc1 hrun1 hsp1 hsp htr1 hvregs_1
      hx8_1 hx9_1 hx10_1 hx11_1 hx13_1 hx19_1 hx28_1
      (fun st2 esWorkPtr hcl2 hpc2 hrun2 hsp2 htr2 hvregs_2 hx19_2 hx20_2 hx21_2 hx22_2
        hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => ?_))
  · unfold unchunkedSendCt2PlacedRoAt F_base; ac_rfl
  rw [hx20_1] at hx20_2; rw [hx23_1] at hx23_2; rw [hx24_1] at hx24_2; rw [hx25_1] at hx25_2
  rw [hx26_1] at hx26_2; rw [hx27_1] at hx27_2; rw [hx29_1] at hx29_2
  refine SepWPp.rw_pre ?_
    (send_ct2_628_to_690_cl_placed_wpp henc hshim halloc hdealloc hpan x esPtr ekPtr esWorkPtr esVec ekVec s0 st2
      (F_base ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) R hcl2
      hesVec hekVec hct2_eq hek_ne hpc2 hrun2 hsp2 hsp htr2 hvregs_2
      hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hx28_2
      (fun st3 ptr_ct2 hcl3 hptr_ct2_ne hpc3 hrun3 hsp3 htr3 hvregs_3
        hx19_3 hx20_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 => ?_))
  · ac_rfl
  rw [hx23_2] at hx23_3; rw [hx24_2] at hx24_3; rw [hx25_2] at hx25_3
  rw [hx26_2] at hx26_3; rw [hx29_2] at hx29_3
  refine SepWPp.rw_pre ?_
    (send_ct2_reserve_ct1_cl_placed_wpp h_res x ct1Cap ct1Ptr s0 st3
      (F_base ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗ A.live ptr_ct2 128 1 ∗
        memRegion (s0.sp - 272#64) 128 ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) R hcl3
      hct1_lt32 hpc3 hrun3 hsp3 hsp htr3 hvregs_3
      (fun st4 cap_ct1' ptr_ct1' hcl4 hcap_ct1'_ne hge128 hmax_ct1' hptr_ct1'_ne
        hpc4 hrun4 hsp4 htr4 hvregs_4 hx1_4 hx19_4 hx20_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 => ?_))
  · ac_rfl
  rw [hx19_3] at hx19_4; rw [hx20_3] at hx20_4; rw [hx23_3] at hx23_4; rw [hx24_3] at hx24_4
  rw [hx25_3] at hx25_4; rw [hx26_3] at hx26_4; rw [hx27_3] at hx27_4; rw [hx29_3] at hx29_4
  refine SepWPp.rw_pre ?_
    (send_ct2_append_hmac_cl_placed_wpp h_concat3 hhmac_safe hdealloc x mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 s0 st4
      (F_base ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        A.live ptr_ct2 128 1) R hcl4
      hct2_len hmk_lt32 hdata_lt32 hmac_eq hge128 hmax_ct1'
      hpc4 hrun4 hsp4 hsp htr4 hvregs_4 hx1_4 hx25_4 hx26_4 hx27_4 hx29_4
      (fun st5 hpc5 hrun5 hsp5 htr5 hvregs_5 hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx29_5 => ?_))
  · ac_rfl
  rw [hx19_4] at hx19_5; rw [hx20_4] at hx20_5; rw [hx23_4] at hx23_5; rw [hx24_4] at hx24_5
  refine SepWPp.rw_pre (by unfold unchunkedSendCt2PlacedRoAt F_base; ac_rfl)
    (send_ct2_epilogue_ret_placed_wpp hdealloc x rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr
      cap_ct1' ptr_ct1' ptr_ct2 s0 st5 R houtUc hct2_len hes_len hek_len
      hmk_le hmk_max hmk_ne hes_le hes_max hek_le hek_max hge128 hptr_ct2_ne
      hpc5 hrun5 hsp5 hsp htr5 hvregs_5 hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5)

/-- Closed `[LibsignalPlacement]` contract for `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`
(Block `347`) with `withLsCodeLoaded lsmpl`, discharging Block `320` (`do_reserve_7_placed_ok`) and
Block `386` (`slice_concat_3_placed_ok`) purely from `HookSat` contracts. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (mlkemEncaps2Spec K))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)) := by
  exact unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_of_contracts
    (ls_subroutine_ok_of_block (i := 347) (j := 320)
      (do_reserve_7_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (i := 347) (j := 386) (subroutine_ok_withLsCodeLoaded_of_plain
      (slice_concat_3_placed_ok h_panic hshim halloc hmemcpy hRO)))
    (spqr_hook_ok_of_mem (sym := spqrRustNoAllocShimSym) hshim)
    (spqr_hook_ok_of_mem (sym := spqrRustAllocSym) halloc)
    (spqr_hook_ok_of_mem (sym := spqrRustDeallocSym) hdealloc)
    (spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy)
    (spqr_hook_ok_of_mem (sym := spqrMlkemEncaps2Sym) hencaps2)
    (spqr_hook_ok_of_mem (sym := spqrLibcruxHmacSym) hhmac)
    ((spqr_externAt?_of_mem).trans h_panic)

/-- Closed `[LibsignalPlacement]` contract for `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`
(Block `347`) with `withLsCodeRoLoaded lsmpl`, purely from `HookSat` contracts. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (mlkemEncaps2Spec K))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)) :=
  LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
      h_panic hshim halloc hrealloc hdealloc hmemcpy hRO hencaps2 hhmac)

end CryptoVerification.SpqrV1.Unchunked

namespace CryptoVerification.SpqrV1.States.Leaves
export CryptoVerification.SpqrV1.Unchunked (
  unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_of_contracts
  unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
  unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok)
end CryptoVerification.SpqrV1.States.Leaves
