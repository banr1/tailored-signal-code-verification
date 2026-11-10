/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Placed
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Mid
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<Ct1SentEkReceived>::send_ct2`: Relocatable `[LibsignalPlacement]` Segments 2–5a

**Checked by Lean.**

Proves `[LibsignalPlacement]` Segments 2, 3, 4, and 5a (`+136 → +836`) for
`<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Keys CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ChainProofs CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open NextKeyInternalFacts AgreeStateSimp DoReserveNorm

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

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

abbrev spqrRustDeallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

abbrev spqrMlkemEncaps2Sym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2"

abbrev spqrLibcruxHmacSym : String :=
  "_RNvCs65XVORQObL2_12libcrux_hmac4hmac"

theorem libcrux_hmac_safe_of_subroutine_ok {prog : Program} {entry : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    (hraw : subroutine_ok prog entry (libcruxHmacSpec F A)) :
    subroutine_ok prog entry (libcruxHmacSafeSpec F A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [libcruxHmacSafeSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hk_lt, hd_lt⟩, hmem⟩
  have hpre' : s0.mem ⊨ (libcruxHmacSpec F A).pre x s0 ∗ R := by
    dsimp only [libcruxHmacSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hmem⟩
  refine hraw.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [libcruxHmacSpec, libcruxHmacSafeSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.2.2, hpost.2⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [libcruxHmacSpec, libcruxHmacSafeSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨haf | hk_ge | hd_ge, hpref⟩, hmem'⟩
    · exact ⟨⟨haf, hpref⟩, hmem'⟩
    · omega
    · omega
  · exact Or.inr (Or.inr hex)

/-! ## Segment 4: `ct1.reserve(128)` (`+656 → +676`) -/

set_option maxHeartbeats 1200000 in
theorem send_ct2_reserve_ct1_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec A))
    (x : UnchunkedSendCt2Ghost F)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_347).base + 656#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64),
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
    refine SepWPp.of_sepWP_mid (mid := (blkPl_347).base + 676#64) ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ cap_ct1 ptr_ct1 hcap_ct1_ne hge128 hct1_lt hptr_ct1_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hls_t : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true := Classical.not_not.mp hls
    have hbound := reserveCap_bound_of_ule_sub_len hct1_le hct1_lt32 hls_t
    refine SepWPp.of_sepWP_mid (mid := lsmpl.base 320) ?_
    wp_steps
    refine SepWP.fold (fold_vecU8At_sp_304 A s0.sp cap_ct1 ptr_ct1 x.st.ct1) (by sep_focus) ?_
    have hstack_res :
        stackAt (s0.sp - 336#64) extHookStack ⊢
          memRegion (s0.sp - 16720#64) 12176 ∗ stackAt (s0.sp - 336#64) doReserveStack :=
      Entails.of_eq (stackAt_extHook_eq_doReserve s0.sp)
    refine SepWP.fold hstack_res (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    wpp_call_sendCt2 h_res
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
    refine SepWPp.of_sepWP_mid (mid := (blkPl_347).base + 676#64) ?_
    wp_steps
    have hstack_back :
        memRegion (s0.sp - 16720#64) 12176 ∗ stackAt st.sp doReserveStack ⊢
          stackAt (s0.sp - 336#64) extHookStack := by
      rw [hsp, ← stackAt_extHook_eq_doReserve s0.sp]
      exact Entails.refl _
    refine SepWP.fold hstack_back (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ptr_ct1'
        hcap_ct1'_ne hge128' hmax_ct1' hptr_ct1'_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))

/-! ## Segment 2: Scan and Optional Endianness Flip (`+0x88 → +0x228`) -/

set_option maxHeartbeats 1200000 in
theorem send_ct2_5d8_to_604_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
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
    (s0 st : State) (F_frame R : SepProp) (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 0x1d8#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
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
  refine SepWPp.of_sepWP_mid (mid := (blkPl_347).base + 488#64) ?_
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
    refine SepWPp.of_sepWP_mid (mid := (blkPl_347).base + 0x204#64) ?_
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
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ (sf1.readReg64 (Reg.gpr 0#5)) hoom
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
theorem send_ct2_scan_to_628_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
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
  · refine SepWPp.of_sepWP_mid
      (mid := (blkPl_347).base + 0x228#64) ?_
    rw [hpre_eq]
    refine SepWP.mono
      (scan_loop_false_placed_ok (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hbs_ne hbs_mod hbs_le hrem_eq hflip hpc hrun hx8 hx9 hx10 hx11 hx13 hx28) ?_
    rintro sf Pf hpc_sf hrun_sf ⟨hPf, hx21_sf, hx22_sf, hx28_sf, hsaved⟩
    have hwork : (esPtr ↦ₛ x.st.es) ⊢ sendCt2EsWorkAt A esPtr esPtr x.st.es := by
      unfold sendCt2EsWorkAt; simp only [hflip, Bool.false_eq_true, ↓reduceIte]
      exact Entails.pure_right trivial (Entails.refl _)
    have hPf_back : Pf ⊢
        sendCt2EsWorkAt A esPtr esPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf, ← hpre_eq]; exact sepConj_mono_left hwork
    refine SepWPp.fold hPf_back (sepConj_emp _).symm (SepWPp.rw_pre (sepConj_emp _) ?_)
    exact hcont sf esPtr hpc_sf hrun_sf
      (hsaved.sp.trans hsp) (hsaved.trace.trans htr) (hsaved.vregs.trans hvregs) (hsaved.x19.trans hx19) hsaved.x20
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx21_sf]) (hx22_sf.trans hx19)
      hsaved.x23 hsaved.x24 hsaved.x25 hsaved.x26 hsaved.x27
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx28_sf]) hsaved.x29
  · have hflip_t : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = true :=
      Bool.eq_true_of_not_eq_false hflip
    refine SepWPp.of_sepWP_mid
      (mid := (blkPl_347).base + 0x1d8#64) ?_
    rw [hpre_eq]
    refine SepWP.mono
      (scan_loop_true_placed_ok (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hbs_ne hbs_mod hbs_le hrem_eq hflip_t hpc hrun hx8 hx9 hx10 hx11 hx13) ?_
    rintro s5d8 P5d8 hpc_5d8 hrun_5d8 ⟨hP5d8, hsaved1⟩
    have hP5d8_eq : P5d8 =
        (esPtr ↦ₛ x.st.es) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame) := by
      rw [hP5d8, ← hpre_eq]; ac_rfl
    rw [hP5d8_eq]
    refine send_ct2_5d8_to_604_placed_wpp hshim halloc hmemcpy hpan x esPtr s0 s5d8
      ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame) R
      hes_len hpc_5d8 hrun_5d8 (hsaved1.sp.trans hsp) hsp_s0 (hsaved1.trace.trans htr)
      (hsaved1.vregs.trans hvregs) (hsaved1.x19.trans hx19) ?_
    intro s604 esWorkPtr hwork_ne hpc604 hrun604 hsp604 htr604 hvregs604 hx8_604 hx19_604 hx20_604 hx22_604 hx23_604 hx24_604 hx25_604 hx26_604 hx27_604 hx28_604 hx29_604
    refine SepWPp.of_sepWP_mid
      (mid := (blkPl_347).base + 0x228#64) ?_
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
    rintro st' Pf2 hpc' hrun' ⟨hPf2, hx21', hsaved2⟩
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
    exact hcont st' esWorkPtr hpc' hrun'
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

/-! ## Segment 3: `encapsulate2`, `ct2` Allocation, and Conditional Dealloc (`+0x228 → +656`) -/

set_option maxHeartbeats 1200000 in
theorem send_ct2_628_to_690_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
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
  refine SepWPp.of_sepWP_mid (mid := (blkPl_347).base + 596#64) ?_
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
      refine SepWPp.of_sepWP_mid (mid := (blkPl_347).base + 656#64) ?_
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
      refine SepWPp.rw_pre (by ac_rfl)
        (hcont _ (sf2.readReg64 (Reg.gpr 0#5)) hoom
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
      refine SepWPp.of_sepWP_mid (mid := (blkPl_347).base + 656#64) ?_
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
      refine SepWPp.rw_pre (by ac_rfl)
        (hcont _ (sf2.readReg64 (Reg.gpr 0#5)) hoom
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

/-! ## Segment 5a: `ct1.extend(ct2)`, `slice_concat_3`, and `libcrux_hmac::hmac` (`+676 → +836`) -/

set_option maxHeartbeats 1600000 in
theorem send_ct2_append_hmac_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec A))
    (h_hmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSafeSpec F A))
    (h_dealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (x : UnchunkedSendCt2Ghost F)
    (mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
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
  refine SepWPp.of_sepWP_mid (mid := lsmpl.base 386) ?_
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
  wpp_call_sendCt2 h_concat3
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
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.x19, wp_norm, arm64_norm, *])
      (by simp only [Reg.x20, wp_norm, arm64_norm, *])
      (by simp only [Reg.x22, wp_norm, arm64_norm, *])
      (by simp only [Reg.x23, wp_norm, arm64_norm, *])
      (by simp only [Reg.x24, wp_norm, arm64_norm, *])
      (by simp only [Reg.x25, wp_norm, arm64_norm, *])
      (by simp only [Reg.x26, wp_norm, arm64_norm, *])
      (by simp only [Reg.x27, wp_norm, arm64_norm, *])
      (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.Unchunked
