/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable Basic-Block Proofs for `get_signed_pre_key::{closure#0}`

Prologue, shared `Vec` deallocation, and post-call branch basic-block lemmas on Block `571`
(`lsProg_571 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CliSpkPollNorm

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] words6At words11At
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496

/-! ## 1. Prologue & pre-call basic blocks (`+0 → decimal`, `+68 → Dir::get`, `+88 → decode`) -/

theorem step_entry_to_decimal_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : PkPollGhost} {s0 : State}
    {r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : BitVec 64}
    (hpc : s0.pc = (blkPl_571).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.fut)
    (hx8 : s0.readReg64 .x8 = x.out) :
    SepWP (lsProg_571 H) (lsmpl.base 597) s0
      ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        ((s0.sp - 96#64) ↦₆₄ r0) ∗ ((s0.sp - 88#64) ↦₆₄ r1) ∗
        ((s0.sp - 80#64) ↦₆₄ r2) ∗ ((s0.sp - 72#64) ↦₆₄ r3) ∗
        ((s0.sp - 64#64) ↦₆₄ r4) ∗ ((s0.sp - 56#64) ↦₆₄ r5) ∗
        ((s0.sp - 48#64) ↦₆₄ r6) ∗ ((s0.sp - 40#64) ↦₆₄ r7) ∗
        ((s0.sp - 32#64) ↦₆₄ r8) ∗ ((s0.sp - 24#64) ↦₆₄ r9) ∗
        ((s0.sp - 16#64) ↦₆₄ r10) ∗ ((s0.sp - 8#64) ↦₆₄ r11))
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.trace = s0.trace ∧
          sm.fs.files = s0.fs.files ∧
          sm.readReg64 .x0 = s0.sp - 248#64 ∧
          sm.readReg32 .x1 = x.id ∧
          sm.readReg64 .x30 = (blkPl_571).base + bv% 68 ∧
          sm.readReg64 .x19 = x.fut ∧
          sm.readReg64 .x20 = x.out ∧
          sm.readReg64 .x21 = x.self ∧
          sm.readReg64 .x27 = s0.sp - 200#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64) ∧
        (Pm ⊢ (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
          spkSavedAt s0)) := by
  dsimp only [lsProg_571, spkSavedAt] at hpc ⊢
  wp_steps
  try
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨rfl, ?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [State.spAligned, wp_norm, arm64_norm] at hsp_align ⊢
    bv_omega
  · simp only [wp_norm, arm64_norm]
  · simp only [wp_norm, arm64_norm]
  · sep_frame

theorem step_68_to_dirGet_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : PkPollGhost} {s0 s : State} {nPtr : BitVec 64}
    (hpc : s.pc = (blkPl_571).base + bv% 68)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx21 : s.readReg64 .x21 = x.self)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) (lsmpl.base 589) s
      (((s0.sp - 240#64) ↦₆₄ nPtr) ∗ ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length))
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.fs.files = s.fs.files ∧
          sm.readReg64 .x0 = s0.sp - 200#64 ∧
          sm.readReg64 .x1 = x.self ∧
          sm.readReg64 .x2 = nPtr ∧
          sm.readReg64 .x3 = BitVec.ofNat 64 (keyName x.id).length ∧
          sm.readReg64 .x30 = (blkPl_571).base + bv% 88 ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = nPtr ∧
          sm.readReg64 .x27 = s.readReg64 .x27 ∧
          sm.readReg64 .x29 = s0.sp - 96#64) ∧
        (Pm ⊢ ((s0.sp - 240#64) ↦₆₄ nPtr) ∗
          ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length))) := by
  dsimp only [lsProg_571] at hpc ⊢
  wp_steps
  try
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx29⟩, ?_⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp
  · simp only [wp_norm, arm64_norm]
  · sep_frame

theorem step_88_to_decodeSpk_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {g0 g1 g2 g3 : BitVec 64} {b : BitVec 8} {bs : List (BitVec 8)}
    (hg0 : g0 = okTagVec)
    (hg3 : g3 = BitVec.ofNat 64 (b :: bs).length)
    (hlen_lt : (b :: bs).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_571).base + bv% 88)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) (lsmpl.base 595) s
      (((s0.sp - 200#64) ↦₆₄ g0) ∗ ((s0.sp - 192#64) ↦₆₄ g1) ∗
        ((s0.sp - 184#64) ↦₆₄ g2) ∗ ((s0.sp - 176#64) ↦₆₄ g3))
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x0 = s0.sp - 200#64 ∧
          sm.readReg64 .x1 = g2 ∧
          sm.readReg64 .x2 = BitVec.ofNat 64 (b :: bs).length ∧
          sm.readReg64 .x30 = (blkPl_571).base + bv% 124 ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x23 = g1 ∧
          sm.readReg64 .x24 = g2 ∧
          sm.readReg64 .x27 = s.readReg64 .x27 ∧
          sm.readReg64 .x29 = s0.sp - 96#64) ∧
        (Pm ⊢ ((s0.sp - 200#64) ↦₆₄ g0) ∗ ((s0.sp - 192#64) ↦₆₄ g1) ∗
          ((s0.sp - 184#64) ↦₆₄ g2) ∗ ((s0.sp - 176#64) ↦₆₄ g3))) := by
  subst hg0; subst hg3
  have _hlen_beq : (BitVec.ofNat 64 (b :: bs).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (len_bv_ne_zero hlen_lt)
  dsimp only [lsProg_571, okTagVec] at hpc ⊢
  wp_steps
  try
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx29⟩, ?_⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp
  · simp only [wp_norm, arm64_norm]
  · sep_frame

/-! ## 2. Shared `Vec` deallocation basic blocks -/

theorem freeBytes_180_to_200_placed [LibsignalPlacement] {H : LibsignalHooks}
    {A : RustAlloc} {calleeStk : Nat}
    {s : State} {fsp bCap bPtr : BitVec 64} {bBytes : List (BitVec 8)}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_571).base + bv% 180)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = fsp)
    (hx23 : s.readReg64 .x23 = bCap)
    (hx24 : s.readReg64 .x24 = bPtr) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 200) s
      (SpqrV1.Alloc.vecU8Buf A bCap bPtr bBytes ∗ stackAt fsp calleeStk ∗ A.pool)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = fsp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s.trace) ∧
        (Pm ⊢ stackAt fsp calleeStk ∗ A.pool)) := by
  dsimp only [lsProg_571] at hDeallocCells hpc ⊢
  by_cases hbCap : bCap = 0#64
  · rw [hbCap] at hx23 ⊢
    apply sepWP_entails_step (vecU8Buf_zero_elim A bPtr bBytes)
    rw [emp_sepConj]
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_, rfl⟩, Entails.refl _⟩
    · simpa only [wp_norm, arm64_norm] using hsp_align
    · simpa only [wp_norm, arm64_norm] using hsp
    · rw [CalleeSavedPreserved.iff_regs]
      simp only [wp_norm, arm64_norm]
  · have hbCap_beq : (bCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbCap
    apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl_d
      (bCap, bPtr, bBytes, fsp)
    clear hcrl hcrl_d hcrl_sf
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hsp' : sf.sp = fsp := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    refine ⟨hsp_align', ⟨hsp', ?_, by simp only [wp_norm, arm64_norm, *]⟩, ?_⟩
    · rw [CalleeSavedPreserved.iff_regs]
      simp only [wp_norm, arm64_norm, *]
    · sep_frame

theorem freeName_200_to_220_placed [LibsignalPlacement] {H : LibsignalHooks}
    {A : RustAlloc} {calleeStk : Nat}
    {s0 s : State} {nCap nPtr : BitVec 64} {id : BitVec 32}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_571).base + bv% 200)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx22 : s.readReg64 .x22 = nPtr) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 220) s
      (SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName id) ∗
        ((s0.sp - 248#64) ↦₆₄ nCap) ∗ stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧ CalleeSavedPreserved s sm ∧ sm.trace = s.trace) ∧
        (Pm ⊢ ((s0.sp - 248#64) ↦₆₄ nCap) ∗ stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)) := by
  dsimp only [lsProg_571] at hDeallocCells hpc ⊢
  by_cases hnCap : nCap = 0#64
  · rw [hnCap]
    apply sepWP_entails_step (vecU8Buf_zero_elim A nPtr (keyName id))
    rw [emp_sepConj]
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_, rfl⟩, Entails.refl _⟩
    · simpa only [wp_norm, arm64_norm] using hsp_align
    · simpa only [wp_norm, arm64_norm] using hsp
    · rw [CalleeSavedPreserved.iff_regs]
      simp only [wp_norm, arm64_norm]
  · have hnCap_beq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl_d
      (nCap, nPtr, keyName id, s0.sp - 384#64)
    clear hcrl hcrl_d hcrl_sf
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    refine ⟨hsp_align', ⟨hsp', ?_, by simp only [wp_norm, arm64_norm, *]⟩, ?_⟩
    · rw [CalleeSavedPreserved.iff_regs]
      simp only [wp_norm, arm64_norm, *]
    · sep_frame

theorem freeName_280_to_344_placed [LibsignalPlacement] {H : LibsignalHooks}
    {A : RustAlloc} {calleeStk : Nat}
    {s0 s : State} {nCap nPtr : BitVec 64} {id : BitVec 32}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_571).base + bv% 280)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx22 : s.readReg64 .x22 = nPtr) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 344) s
      (SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName id) ∗
        ((s0.sp - 248#64) ↦₆₄ nCap) ∗ stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x26 = 0xFFFFFFFFFFFFFFFF#64 ∧
          sm.readReg64 .x25 = s.readReg64 .x25 ∧
          sm.readReg64 .x23 = s.readReg64 .x23 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x21 = s.readReg64 .x21) ∧
        (Pm ⊢ ((s0.sp - 248#64) ↦₆₄ nCap) ∗ stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)) := by
  dsimp only [lsProg_571] at hDeallocCells hpc ⊢
  by_cases hnCap : nCap = 0#64
  · rw [hnCap]
    apply sepWP_entails_step (vecU8Buf_zero_elim A nPtr (keyName id))
    rw [emp_sepConj]
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Entails.refl _⟩
    · simpa only [wp_norm, arm64_norm] using hsp_align
    · simpa only [wp_norm, arm64_norm] using hsp
    · simp only [wp_norm, arm64_norm]
  · have hnCap_beq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl_d
      (nCap, nPtr, keyName id, s0.sp - 384#64)
    clear hcrl hcrl_d hcrl_sf
    have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simpa only [wp_norm, arm64_norm] using hsp_align',
      ⟨by simpa only [wp_norm, arm64_norm] using hsp',
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       rfl,
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *]⟩,
      by sep_frame⟩

/-! ## 3. Four post-`Dir::get` / post-`decode_kyber_pre_key` branch blocks -/

theorem step_readErr_88_to_280_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {g0 g1 g2 g3 g4 g5 b0 b1 : BitVec 64}
    (hg0 : g0 = speWord 1)
    (hpc : s.pc = (blkPl_571).base + bv% 88)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 200#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 280) s
      (words6At (s0.sp - 200#64) g0 g1 g2 g3 g4 g5 ∗
        ((s0.sp - 336#64) ↦₆₄ b0) ∗ ((s0.sp - 328#64) ↦₆₄ b1))
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x25 = g0 ∧
          sm.readReg64 .x23 = g1 ∧
          sm.readReg64 .x24 = g2 ∧
          sm.readReg64 .x21 = g3) ∧
        (Pm ⊢ words6At (s0.sp - 200#64) g0 g1 g2 g3 g4 g5 ∗
          ((s0.sp - 336#64) ↦₆₄ g4) ∗ ((s0.sp - 328#64) ↦₆₄ g5))) := by
  subst hg0
  dsimp only [lsProg_571, words6At, speWord] at hpc ⊢
  wp_steps
  try
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp
  · simp only [wp_norm, arm64_norm]
  · sep_frame

theorem step_missing_88_to_200_placed [LibsignalPlacement] {H : LibsignalHooks}
    {A : RustAlloc} {calleeStk : Nat}
    {s0 s : State} {g0 g1 g2 g3 c3 c4 b2 b3 d3 d4 : BitVec 64}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hg0 : g0 = okTagVec)
    (hg3 : g3 = 0#64)
    (hpc : s.pc = (blkPl_571).base + bv% 88)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 200) s
      (SpqrV1.Alloc.vecU8Buf A g1 g2 [] ∗
        ((s0.sp - 200#64) ↦₆₄ g0) ∗ ((s0.sp - 192#64) ↦₆₄ g1) ∗
        ((s0.sp - 184#64) ↦₆₄ g2) ∗ ((s0.sp - 176#64) ↦₆₄ g3) ∗
        ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
        ((s0.sp - 320#64) ↦₆₄ b2) ∗ ((s0.sp - 312#64) ↦₆₄ b3) ∗
        ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4) ∗
        stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x28 = s.readReg64 .x28 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x26 = 0xFFFFFFFFFFFFFFFF#64) ∧
        (Pm ⊢ ((s0.sp - 200#64) ↦₆₄ g0) ∗ ((s0.sp - 192#64) ↦₆₄ g1) ∗
          ((s0.sp - 184#64) ↦₆₄ g2) ∗ ((s0.sp - 176#64) ↦₆₄ g3) ∗
          ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
          ((s0.sp - 320#64) ↦₆₄ c3) ∗ ((s0.sp - 312#64) ↦₆₄ c4) ∗
          ((s0.sp - 224#64) ↦₆₄ c3) ∗ ((s0.sp - 216#64) ↦₆₄ c4) ∗
          stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)) := by
  subst hg0; subst hg3
  dsimp only [lsProg_571, okTagVec] at hDeallocCells hpc ⊢
  by_cases hg1 : g1 = 0#64
  · rw [hg1]
    apply sepWP_entails_step (vecU8Buf_zero_elim A g2 [])
    rw [emp_sepConj]
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, hx29, rfl⟩, ?_⟩
    · simpa only [wp_norm, arm64_norm] using hsp_align
    · simpa only [wp_norm, arm64_norm] using hsp
    · simp only [wp_norm, arm64_norm]
    · sep_frame
  · have hg1_beq : (g1 == 0#64) = false := beq_eq_false_iff_ne.mpr hg1
    apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl_d
      (g1, g2, [], s0.sp - 384#64)
    clear hcrl hcrl_d hcrl_sf
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    refine ⟨hsp_align',
      ⟨hsp',
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *]⟩,
      by sep_frame⟩

theorem step_missing_220_to_344_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {e0 : BitVec 64}
    (hpc : s.pc = (blkPl_571).base + bv% 220)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : s.readReg64 .x26 = 0xFFFFFFFFFFFFFFFF#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 344) s
      ((s0.sp - 200#64) ↦₆₄ e0)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x26 = 0xFFFFFFFFFFFFFFFF#64 ∧
          sm.readReg64 .x25 = speWord 14 ∧
          sm.readReg64 .x23 = s.readReg64 .x28 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x21 = s.readReg64 .x21) ∧
        (Pm ⊢ (s0.sp - 200#64) ↦₆₄ speWord 14)) := by
  dsimp only [lsProg_571, speWord] at hpc ⊢
  wp_steps
  try
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl, hx26, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp
  · simp only [wp_norm, arm64_norm]
  · sep_frame

theorem step_decodeErr_124_to_280_placed [LibsignalPlacement] {H : LibsignalHooks}
    {A : RustAlloc} {calleeStk : Nat}
    {s0 s : State} {g1 g2 w0 w1 w2 w3 w4 w5 w6 b0 b1 b2 b3 c3 c4 : BitVec 64}
    {b : BitVec 8} {bs : List (BitVec 8)}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hw0 : w0 = 0xFFFFFFFFFFFFFFFF#64)
    (hpc : s.pc = (blkPl_571).base + bv% 124)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx23 : s.readReg64 .x23 = g1)
    (hx24 : s.readReg64 .x24 = g2)
    (hx27 : s.readReg64 .x27 = s0.sp - 200#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 280) s
      (SpqrV1.Alloc.vecU8Buf A g1 g2 (b :: bs) ∗
        ((s0.sp - 200#64) ↦₆₄ w0) ∗ ((s0.sp - 192#64) ↦₆₄ w1) ∗
        ((s0.sp - 184#64) ↦₆₄ w2) ∗ ((s0.sp - 176#64) ↦₆₄ w3) ∗
        ((s0.sp - 168#64) ↦₆₄ w4) ∗ ((s0.sp - 160#64) ↦₆₄ w5) ∗
        ((s0.sp - 152#64) ↦₆₄ w6) ∗
        ((s0.sp - 336#64) ↦₆₄ b0) ∗ ((s0.sp - 328#64) ↦₆₄ b1) ∗
        ((s0.sp - 320#64) ↦₆₄ b2) ∗ ((s0.sp - 312#64) ↦₆₄ b3) ∗
        ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
        stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x25 = w1 ∧
          sm.readReg64 .x23 = w2 ∧
          sm.readReg64 .x24 = w3 ∧
          sm.readReg64 .x21 = w4) ∧
        (Pm ⊢ ((s0.sp - 200#64) ↦₆₄ w0) ∗ ((s0.sp - 192#64) ↦₆₄ w1) ∗
          ((s0.sp - 184#64) ↦₆₄ w2) ∗ ((s0.sp - 176#64) ↦₆₄ w3) ∗
          ((s0.sp - 168#64) ↦₆₄ w4) ∗ ((s0.sp - 160#64) ↦₆₄ w5) ∗
          ((s0.sp - 152#64) ↦₆₄ w6) ∗
          ((s0.sp - 336#64) ↦₆₄ w5) ∗ ((s0.sp - 328#64) ↦₆₄ w6) ∗
          ((s0.sp - 320#64) ↦₆₄ w5) ∗ ((s0.sp - 312#64) ↦₆₄ w6) ∗
          ((s0.sp - 272#64) ↦₆₄ w5) ∗ ((s0.sp - 264#64) ↦₆₄ w6) ∗
          stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)) := by
  subst hw0
  dsimp only [lsProg_571] at hDeallocCells hpc ⊢
  by_cases hg1 : g1 = 0#64
  · rw [hg1] at hx23 ⊢
    apply sepWP_entails_step (vecU8Buf_zero_elim A g2 (b :: bs))
    rw [emp_sepConj]
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · simpa only [wp_norm, arm64_norm] using hsp_align
    · simpa only [wp_norm, arm64_norm] using hsp
    · simp only [wp_norm, arm64_norm]
    · sep_frame
  · have hg1_beq : (g1 == 0#64) = false := beq_eq_false_iff_ne.mpr hg1
    apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl_d
      (g1, g2, b :: bs, s0.sp - 384#64)
    clear hcrl hcrl_d hcrl_sf
    have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    wp_steps
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simpa only [wp_norm, arm64_norm] using hsp_align',
      ⟨by simpa only [wp_norm, arm64_norm] using hsp',
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *]⟩,
      by sep_frame⟩

theorem step_found_124_to_180_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64}
    {a0 b2 b3 b4 c0 c1 c2 c3 c4 d3 d4 : BitVec 64}
    (hw0 : w0 ≠ 0xFFFFFFFFFFFFFFFF#64)
    (hpc : s.pc = (blkPl_571).base + bv% 124)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 200#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 180) s
      (words11At (s0.sp - 200#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
        ((s0.sp - 376#64) ↦₆₄ a0) ∗
        ((s0.sp - 320#64) ↦₆₄ b2) ∗ ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4) ∗
        ((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
        ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
        ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4))
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x23 = s.readReg64 .x23 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x26 = w0 ∧
          sm.readReg64 .x25 = w1 ∧
          sm.readReg64 .x28 = w2 ∧
          sm.readReg64 .x21 = w4) ∧
        (Pm ⊢ words11At (s0.sp - 200#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          ((s0.sp - 376#64) ↦₆₄ w3) ∗
          ((s0.sp - 320#64) ↦₆₄ w5) ∗ ((s0.sp - 312#64) ↦₆₄ w6) ∗ ((s0.sp - 304#64) ↦₆₄ w7) ∗
          ((s0.sp - 296#64) ↦₆₄ w8) ∗ ((s0.sp - 288#64) ↦₆₄ w9) ∗ ((s0.sp - 280#64) ↦₆₄ w10) ∗
          ((s0.sp - 272#64) ↦₆₄ w5) ∗ ((s0.sp - 264#64) ↦₆₄ w6) ∗
          ((s0.sp - 224#64) ↦₆₄ w5) ∗ ((s0.sp - 216#64) ↦₆₄ w6))) := by
  have _hcmn1 := cmn1_beq_zero hw0
  have _hcmn2 := cmn1_add_zero hw0
  dsimp only [lsProg_571, words11At] at hpc ⊢
  wp_steps
  try
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hx29, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp
  · simp only [wp_norm, arm64_norm]
  · sep_frame

theorem step_found_220_to_344_placed [LibsignalPlacement] {H : LibsignalHooks}
    {A : RustAlloc} {calleeStk : Nat}
    {s0 s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64}
    {a1 a2 a3 a4 b0 b1 : BitVec 64}
    (hDropCells : subroutine_ok (lsProg_571 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeWordCellsSpec A calleeStk)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hw0 : w0 ≠ 0xFFFFFFFFFFFFFFFF#64)
    (hpc : s.pc = (blkPl_571).base + bv% 220)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : s.readReg64 .x26 = w0)
    (hx25 : s.readReg64 .x25 = w1)
    (hx28 : s.readReg64 .x28 = w2)
    (hx21 : s.readReg64 .x21 = w4) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 344) s
      (words6At (s0.sp - 200#64) w0 w1 w2 w3 w4 w5 ∗
        ((s0.sp - 376#64) ↦₆₄ w3) ∗ ((s0.sp - 368#64) ↦₆₄ a1) ∗ ((s0.sp - 360#64) ↦₆₄ a2) ∗
        ((s0.sp - 352#64) ↦₆₄ a3) ∗ ((s0.sp - 344#64) ↦₆₄ a4) ∗
        ((s0.sp - 336#64) ↦₆₄ b0) ∗ ((s0.sp - 328#64) ↦₆₄ b1) ∗
        ((s0.sp - 304#64) ↦₆₄ w7) ∗ ((s0.sp - 296#64) ↦₆₄ w8) ∗
        ((s0.sp - 288#64) ↦₆₄ w9) ∗ ((s0.sp - 280#64) ↦₆₄ w10) ∗
        ((s0.sp - 224#64) ↦₆₄ w5) ∗ ((s0.sp - 216#64) ↦₆₄ w6) ∗
        stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x26 = w0 ∧
          sm.readReg64 .x25 = w1 ∧
          sm.readReg64 .x23 = w2 ∧
          sm.readReg64 .x24 = w3 ∧
          sm.readReg64 .x21 = w4) ∧
        (Pm ⊢ (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
            ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64,
              words6At (s0.sp - 200#64) e0 e1 e2 e3 e4 e5) ∗
          ((s0.sp - 376#64) ↦₆₄ w3) ∗ ((s0.sp - 368#64) ↦₆₄ w7) ∗ ((s0.sp - 360#64) ↦₆₄ w8) ∗
          ((s0.sp - 352#64) ↦₆₄ w9) ∗ ((s0.sp - 344#64) ↦₆₄ w10) ∗
          ((s0.sp - 336#64) ↦₆₄ w5) ∗ ((s0.sp - 328#64) ↦₆₄ w6) ∗
          ((s0.sp - 304#64) ↦₆₄ w7) ∗ ((s0.sp - 296#64) ↦₆₄ w8) ∗
          ((s0.sp - 288#64) ↦₆₄ w9) ∗ ((s0.sp - 280#64) ↦₆₄ w10) ∗
          ((s0.sp - 224#64) ↦₆₄ w5) ∗ ((s0.sp - 216#64) ↦₆₄ w6) ∗
          stackAt (s0.sp - 384#64) calleeStk ∗ A.pool)) := by
  have _hcmn1 := cmn1_beq_zero hw0
  have _hcmn2 := cmn1_add_zero hw0
  dsimp only [lsProg_571, words6At, speWord] at hDropCells hpc ⊢
  apply StoreKit.sepWP_seq_lscro (mid := lsmpl.base 553) hcrl
  wp_steps
  try
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_d
  wp_call_spec_lscro hDropCells (dropSpeWordCellsSpec A calleeStk) hcrl_d
    (s0.sp - 200#64, w1, w2, w3, w4, w5, s0.sp - 384#64)
  clear hcrl hcrl_d hcrl_sf
  have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
  have hsp_align' : sf.spAligned = true := by
    simp only [State.spAligned, hsp'] at hsp_align ⊢
    simpa only [hsp] using hsp_align
  wp_steps
  try
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨by simpa only [wp_norm, arm64_norm] using hsp_align',
    ⟨by simpa only [wp_norm, arm64_norm] using hsp',
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     rfl,
     by simp only [wp_norm, arm64_norm, *]⟩,
    by sep_frame⟩

end Placed

end CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
