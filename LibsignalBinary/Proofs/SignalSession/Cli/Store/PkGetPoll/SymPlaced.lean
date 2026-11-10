/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Blocks
public import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable Ok/Missing Branch and Symbolic Execution of `get_pre_key::{closure#0}`

Proves the `.missing` / `.found` branch helper (`step_ok_240_placed`) and full symbolic execution
`pkGetPollInner_placed_ok` on Block `573` (`lsProg_573 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.CodeLayout CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CliPkGetPollNorm

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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

/-! ## 1. Branch 3/4 Helper: `.missing` (`+236 -> +240`) and `.found rec` (`+240` .. `+344` -> `+348`) -/

theorem step_ok_240_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P : SepProp}
    (hDeallocCells : subroutine_ok (lsProg_573 H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)))
    (hDropCells : subroutine_ok (lsProg_573 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeWordCellsSpec A calleeStk)))
    (ans : PkAns PreKeyRecord) (bytes : List (BitVec 8))
    (w1 w2 nCap nPtr nLen r26 r25 r28 r27 r21 qlo qhi u0 u1 u2 u3 k0 k1
      g0 g1 g2 g3 g4 g5 g6 : BitVec 64)
    (payload : SepProp)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_573).base + bv% (240))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = r21)
    (hx22 : s.readReg64 .x22 = nPtr)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = w2)
    (hx25 : s.readReg64 .x25 = r25)
    (hx26 : s.readReg64 .x26 = r26)
    (hx27 : s.readReg64 .x27 = r27)
    (hx28 : s.readReg64 .x28 = r28)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hAns : ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)))
    (hMode :
      (ans = .missing ∧ r26 = errTag ∧ payload = emp) ∨
      (∃ rec : PreKeyRecord, ans = .found rec ∧ r26 + 1#64 ≠ 0#64 ∧
        payload = pkDecPayload A (.ok rec) r26 r25 r28 r27 r21 qlo qhi))
    (hP : P ⊢
      pkBoxKeep x s0 ∗ payload ∗
        (w2 ↦ₛ bytes) ∗ vecU8BufRest A w1 w2 bytes ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) :
    SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0) := by
  refine SepWP.weaken_pre hP ?_; clear hP
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  suffices hjoin272 : ∀ (s1 : State) (P1 : SepProp),
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.pc = (blkPl_573).base + bv% (272) →
      s1.status = .Running →
      s1.sp = s0.sp - 256#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = x.fut →
      s1.readReg64 .x20 = x.out →
      s1.readReg64 .x21 = r21 →
      s1.readReg64 .x22 = nPtr →
      s1.readReg64 .x25 = r25 →
      s1.readReg64 .x26 = r26 →
      s1.readReg64 .x27 = r27 →
      s1.readReg64 .x28 = r28 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢ pkBoxKeep x s0 ∗ payload ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) →
      SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s1 P1
        (pkEpiloguePost rd pathOk A calleeStk x s0) by
    by_cases hw1 : w1 = 0#64
    · subst hw1
      refine bytes_zero_elim_p (ptr := w2) (bs := bytes)
        (Rest := pkBoxKeep x s0 ∗ payload ∗
          (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
          dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
          ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
          ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
          ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
          ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
        (by ac_rfl) ?_
      apply StoreKit.sepWP_seq_lscro (mid := (blkPl_573).base + bv% (272)) hcrl
      wp_steps
      try
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
      intro hcrl1
      apply bind_sepWP_state; intro s1
      exact hjoin272 s1 _ hcrl1
        (by simp only [s1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
    · have hw1_eq : (w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hw1
      have hw1_ne : (w1 != 0#64) = true := bne_iff_ne.mpr hw1
      apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
      wp_steps
      try
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
      intro hcrl1
      wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl1
        (w2, w1, bytes, s0.sp - 256#64)
      exact hjoin272 sf _ hcrl_sf
        (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
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
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
  clear hcrl hpc hrun hsp hal htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs s
  intro s1 P1 hcrl1 hpc1 hrun1 hsp1 htr1 h19_1 h20_1 h21_1 h22_1 h25_1 h26_1 h27_1 h28_1 h29_1 hv1 hP1
  refine SepWP.weaken_pre hP1 ?_; clear hP1
  have hal1 : s1.spAligned = true := sp_sub_256_spAligned hal0 hsp1
  suffices hjoin292 : ∀ (s2 : State) (P2 : SepProp),
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
      s2.pc = (blkPl_573).base + bv% (292) →
      s2.status = .Running →
      s2.sp = s0.sp - 256#64 →
      s2.trace = s0.trace →
      s2.readReg64 .x19 = x.fut →
      s2.readReg64 .x20 = x.out →
      s2.readReg64 .x21 = r21 →
      s2.readReg64 .x25 = r25 →
      s2.readReg64 .x26 = r26 →
      s2.readReg64 .x27 = r27 →
      s2.readReg64 .x28 = r28 →
      s2.readReg64 .x29 = s0.sp - 96#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      (P2 ⊢ pkBoxKeep x s0 ∗ payload ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) →
      SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s2 P2
        (pkEpiloguePost rd pathOk A calleeStk x s0) by
    by_cases hnCap : nCap = 0#64
    · subst hnCap
      refine bytes_zero_elim_p (ptr := nPtr) (bs := keyName x.id)
        (Rest := pkBoxKeep x s0 ∗ payload ∗
          dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
          ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
          ((s0.sp - 200#64) ↦₆₄ 0#64) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
          ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
          ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
          ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
        (by ac_rfl) ?_
      apply StoreKit.sepWP_seq_lscro (mid := (blkPl_573).base + bv% (292)) hcrl1
      wp_steps
      try
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
      intro hcrl2
      apply bind_sepWP_state; intro s2
      exact hjoin292 s2 _ hcrl2
        (by simp only [s2, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
    · have hnCap_eq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
      have hnCap_ne : (nCap != 0#64) = true := bne_iff_ne.mpr hnCap
      apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl1
      wp_steps
      try
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
      intro hcrl2
      wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl2
        (nPtr, nCap, keyName x.id, s0.sp - 256#64)
      exact hjoin292 sf _ hcrl_sf
        (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
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
        (by simp only [wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
  clear hcrl1 hpc1 hrun1 hsp1 hal1 htr1 h19_1 h20_1 h21_1 h22_1 h25_1 h26_1 h27_1 h28_1 h29_1 hv1 s1
  intro s2 P2 hcrl2 hpc2 hrun2 hsp2 htr2 h19_2 h20_2 h21_2 h25_2 h26_2 h27_2 h28_2 h29_2 hv2 hP2
  refine SepWP.weaken_pre hP2 ?_; clear hP2
  have hal2 : s2.spAligned = true := sp_sub_256_spAligned hal0 hsp2
  rcases hMode with ⟨rfl, rfl, rfl⟩ | ⟨rec, rfl, hd0, rfl⟩
  · apply StoreKit.sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl2
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro _hcrl_ep
    apply bind_sepWP_state; intro s_ep
    have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    exact step_epilogue_348_placed .missing errTag (speWord 13) r28 r27 r21 u0 u1
      qlo qhi qlo qhi nCap nPtr nLen qlo qhi (speWord 13) g1 g2 g3 g4 g5 g6
      emp
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *]; rfl)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (by rw [sepConj_emp]; exact missing_reassemble A x.out r28 r27 r21 u0 u1)
      (Entails.of_eq (by ac_rfl))
  · have hd0_eq : (r26 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hd0
    have hd0_ne : (r26 + 1#64 != 0#64) = true := bne_iff_ne.mpr hd0
    apply StoreKit.sepWP_seq_lscro (mid := lsmpl.base 553) hcrl2
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro hcrl3
    have hspe13 : (0x800000000000000d#64 : BitVec 64) = speWord 13 := rfl
    rw [hspe13]
    wp_call_spec_lscro hDropCells (dropSpeWordCellsSpec A calleeStk) hcrl3
      (s0.sp - 152#64, g1, g2, g3, g4, g5, s0.sp - 256#64)
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl_sf
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro _hcrl_ep
    apply bind_sepWP_state; intro s_ep
    have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    exact step_epilogue_348_placed (.found rec) r26 r25 r28 r27 r21 qlo qhi
      qlo qhi qlo qhi nCap nPtr nLen qlo qhi w w_1 w_2 w_3 w_4 w_5 g6
      (pkDecPayload A (.ok rec) r26 r25 r28 r27 r21 qlo qhi)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (found_reassemble A x.out rec r26 r25 r28 r27 r21 qlo qhi)
      (Entails.of_eq (by ac_rfl))

/-! ## 2. Local Helpers & Main Symbolic Execution of Block `573` (`pkGetPollInner_placed_ok`) -/

private theorem sepWP_peek_err_tag_p {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {e : SignalProtocolError} {d0 d1 d2 d3 d4 d5 d6 : BitVec 64}
    {Rest : SepProp} {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗ Rest)
    (h : d0 = errTag → SepWP prog ret s P Q) :
    SepWP prog ret s P Q := by
  subst heq
  have hent :
      pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗ Rest ⊢
        ⌜d0 = errTag⌝ ∗ (pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗ Rest) := by
    dsimp only [pkDecPayload]
    apply Entails.pure_left; rintro ⟨he, rfl, hd1⟩
    exact Entails.pure_right rfl (Entails.pure_right ⟨he, rfl, hd1⟩ (Entails.refl _))
  exact SepWP.weaken_pre hent (SepWP.pure_elim h)

private theorem sepWP_peek_ok_hd0_p {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {rec : PreKeyRecord} {d0 d1 d2 d3 d4 d5 d6 : BitVec 64}
    {Rest : SepProp} {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ∗ Rest)
    (h : d0 + 1#64 ≠ 0#64 → SepWP prog ret s P Q) :
    SepWP prog ret s P Q := by
  subst heq
  have hent :
      pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ∗ Rest ⊢
        ⌜d0 + 1#64 ≠ 0#64⌝ ∗ (pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ∗ Rest) := by
    dsimp only [pkDecPayload]
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hφ
    exact Entails.pure_right hφ.1 (Entails.pure_right hφ (Entails.refl _))
  exact SepWP.weaken_pre hent (SepWP.pure_elim h)

private theorem sepWPp_exists_right_p {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Rest : SepProp} {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (Rest ∗ P a) Q Qp) :
    SepWPp prog ret s (Rest ∗ (∃∗ a, P a)) Q Qp := by
  rw [sepExists_sepConj_right]
  exact SepWPp.exists_elim h

private theorem sepWPp_exists_mid_p {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {L R : SepProp} {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (L ∗ (P a ∗ R)) Q Qp) :
    SepWPp prog ret s (L ∗ ((∃∗ a, P a) ∗ R)) Q Qp := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  exact SepWPp.exists_elim h

private theorem finish_epilogue_p [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} (pathOk : List (BitVec 8) → Prop)
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P R : SepProp}
    (h : SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0)) :
    SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (∃∗ ans,
              ⌜ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
                  sf.trace = s0.trace⌝ ∗
              pkGetAnsAt A x.out ans) ∗
              (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
              dirAt A x.self x.dir ∗ A.pool ∗
              stackAt (s0.sp - 256#64) calleeStk ∗ cells (s0.sp - 256#64) 32 ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.mono h fun sf P_f _ _ ⟨hsp, hcs, hent⟩ => ⟨fun hm => ?_, hsp, hcs⟩
  have hm' := Satisfies.mono (sepConj_mono_left hent) hm
  dsimp only [pkGetPollInnerSpec] at hm'
  simpa only [sepConj_assoc] using hm'

/-- Full symbolic proof of the inner specification `pkGetPollInnerSpec` on `lsProg_573 H`. -/
theorem pkGetPollInner_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok (lsProg_573 H) (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok (lsProg_573 H) (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok (lsProg_573 H) (lsmpl.base 65) (preKeyDeserializePlacedSpec A))
    (hDrop : subroutine_ok (lsProg_573 H) (lsmpl.base 553) (dropSpeWordSpecPlaced A))
    (hFs : TraceFsSound (lsProg_573 H))
    (hhi : max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)) ≤ 2 ^ 64) :
    subroutine_ok (lsProg_573 H) (blkPl_573).base
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pkGetPollInnerSpec rd pathOk A
          (max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))))) := by
  set calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
  have hDeallocCells := dealloc_buf_cells_placed_ok (prog := lsProg_573 H) (calleeStk := calleeStk)
    hC (by omega) hhi
  have hDecimalCells := decimal_cells_placed_ok (calleeStk := calleeStk) hDecimal hFs (by omega) hhi
  have hGetCells := dirGet_cells_placed_ok (calleeStk := calleeStk) hGet (by omega) hhi
  have hDecCells := pkDec_cells_placed_ok (calleeStk := calleeStk) hDec (by omega) hhi
  have hDropCells := dropSpeWord_cells_placed_ok (calleeStk := calleeStk) hDrop (by omega) hhi
  clear hC hDecimal hGet hDec hDrop hFs
  unfold StoreKit.withLsCodeRoLoaded
  dsimp only [pkGetPollInnerSpec]
  wpp_init x s0
  have hal0 : s0.spAligned = true := by assumption
  have hname0 : PkNameOk pathOk x.dir x.id := by assumption
  have hsize0 : PkSizeOk rd s0.fs.files x.dir x.id := by assumption
  obtain ⟨hnlen, hplen, hpok⟩ := hname0
  have hnlen_bv : (BitVec.ofNat 64 (keyName x.id).length).toNat = (keyName x.id).length :=
    Nat.mod_eq_of_lt (by omega)
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  refine SepWPp.weaken_pre
    (P' := ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
      dirAt A x.self x.dir ∗ memRegion x.out 56 ∗ A.pool ∗
      stackAt (s0.sp - 256#64) calleeStk ∗ pkPollSlack s0.sp) ∗
      (cells (s0.sp - 256#64) 6 ∗ (cells (s0.sp - 200#64) 3 ∗
        (cells (s0.sp - 176#64) 2 ∗ (cells (s0.sp - 152#64) 7 ∗ cells (s0.sp - 96#64) 12)))))
    (by rw [cells_32_split]; exact Entails.of_eq (by ac_rfl)) ?_
  rw [cells_sub_6_256_eq]
  apply sepWPp_exists_mid_p; intro v
  apply sepWPp_exists_mid_p; intro v_1
  apply sepWPp_exists_mid_p; intro v_2
  apply sepWPp_exists_mid_p; intro v_3
  apply sepWPp_exists_mid_p; intro v_4
  apply sepWPp_exists_mid_p; intro v_5
  rw [← sepConj_assoc, cells_sub_3_200_eq]
  apply sepWPp_exists_mid_p; intro v_6
  apply sepWPp_exists_mid_p; intro v_7
  apply sepWPp_exists_mid_p; intro v_8
  rw [← sepConj_assoc, cells_sub_2_176_eq]
  apply sepWPp_exists_mid_p; intro v_9
  apply sepWPp_exists_mid_p; intro v_10
  rw [← sepConj_assoc, cells_sub_7_152_eq]
  apply sepWPp_exists_mid_p; intro v_11
  apply sepWPp_exists_mid_p; intro v_12
  apply sepWPp_exists_mid_p; intro v_13
  apply sepWPp_exists_mid_p; intro v_14
  apply sepWPp_exists_mid_p; intro v_15
  apply sepWPp_exists_mid_p; intro v_16
  apply sepWPp_exists_mid_p; intro v_17
  rw [← sepConj_assoc, cells_sub_12_96_eq]
  apply sepWPp_exists_right_p; intro v_18
  apply sepWPp_exists_right_p; intro v_19
  apply sepWPp_exists_right_p; intro v_20
  apply sepWPp_exists_right_p; intro v_21
  apply sepWPp_exists_right_p; intro v_22
  apply sepWPp_exists_right_p; intro v_23
  apply sepWPp_exists_right_p; intro v_24
  apply sepWPp_exists_right_p; intro v_25
  apply sepWPp_exists_right_p; intro v_26
  apply sepWPp_exists_right_p; intro v_27
  apply sepWPp_exists_right_p; intro v_28
  apply sepWPp_exists_right_p; intro v_29
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 597) hcrl0
  wp_steps
  try
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
  intro hcrl1
  refine SepWPp.weaken_pre (Entails.of_eq (by unfold pkBoxKeep pkSavedRegs; ac_rfl))
    (P' := pkBoxKeep x s0 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
      ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
      ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
      ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
      ((s0.sp - 200#64) ↦₆₄ v_6) ∗ ((s0.sp - 192#64) ↦₆₄ v_7) ∗ ((s0.sp - 184#64) ↦₆₄ v_8) ∗
      ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10) ∗
      ((s0.sp - 152#64) ↦₆₄ v_11) ∗ ((s0.sp - 144#64) ↦₆₄ v_12) ∗
      ((s0.sp - 136#64) ↦₆₄ v_13) ∗ ((s0.sp - 128#64) ↦₆₄ v_14) ∗
      ((s0.sp - 120#64) ↦₆₄ v_15) ∗ ((s0.sp - 112#64) ↦₆₄ v_16) ∗ ((s0.sp - 104#64) ↦₆₄ v_17)) ?_
  wp_call_spec_lscro hDecimalCells (decimalCellsSpec A calleeStk) hcrl1
    (x.id, s0.sp - 200#64, _, _, _, s0.sp - 256#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 589) hcrl_sf
  wp_steps
  try
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
  intro hcrl2
  wp_call_spec_lscro hGetCells (dirGetCellsSpec rd pathOk A calleeStk) hcrl2
    (s0.sp - 152#64, x.self, x.dir, w_1, keyName x.id, _, _, _, _, _, _, s0.sp - 256#64)
  case panic =>
    intro sf_p _ hm
    exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
  have hget_post :
      w_2 = x.dir.get rd s0.fs.files (keyName x.id) ∧ sf_1.trace = s0.trace := by
    have htr_sf0 : sf.trace = s0.trace := by simp only [wp_norm, arm64_norm, *]
    have hfs_sf0 : sf.fs.files = s0.fs.files := by simp only [wp_norm, arm64_norm, *]
    exact ⟨by rw [← hfs_sf0]; exact ‹w_2 = _›, (‹sf_1.trace = sf.trace›).trans htr_sf0⟩
  refine SepWPp.weaken_pre
    (P' := dirGetPayload A w_2 w_3 w_4 w_5 w_6 w_7 w_8 ∗
      ((s0.sp - 152#64) ↦₆₄ w_3) ∗ ((s0.sp - 144#64) ↦₆₄ w_4) ∗
      ((s0.sp - 136#64) ↦₆₄ w_5) ∗ ((s0.sp - 128#64) ↦₆₄ w_6) ∗
      ((s0.sp - 120#64) ↦₆₄ w_7) ∗ ((s0.sp - 112#64) ↦₆₄ w_8) ∗
      ((s0.sp - 104#64) ↦₆₄ v_17) ∗
      (w_1 ↦ₛ keyName x.id) ∗ vecU8BufRest A w w_1 (keyName x.id) ∗
      pkBoxKeep x s0 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
      ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
      ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
      ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
      ((s0.sp - 200#64) ↦₆₄ w) ∗ ((s0.sp - 192#64) ↦₆₄ w_1) ∗
      ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
      ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
    (Entails.of_eq (by ac_rfl)) ?_
  rcases w_2 with ⟨⟩ | ⟨⟩ | ⟨b0, rest⟩
  · -- `r = .error ()`
    dsimp only [dirGetPayload]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hw0 => ?_
    subst hw0
    apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_573).base + bv% (200)) hcrl_sf_1
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro hcrl_err
    apply SepWPp.of_sepWP_ret
    apply bind_sepWP_state; intro s_err
    have htr_err : s_err.trace = sf_1.trace := by simp only [s_err, wp_norm, arm64_norm]
    have hAns_err :
        (PkAns.readErr : PkAns PreKeyRecord) =
            pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          s_err.trace = s0.trace :=
      ⟨by rw [← hget_post.1]; rfl, htr_err.trans hget_post.2⟩
    have hpc_err : s_err.pc = (blkPl_573).base + bv% (200) := by
      simp only [s_err, wp_norm, arm64_norm, *]; try bv_omega
    apply finish_epilogue_p pathOk
    refine step_err_200_placed hDeallocCells
      w_4 w_5 w_6 w_7 w_8 w w_1 (BitVec.ofNat 64 (keyName x.id).length)
      v v_1 v_2 v_3 v_4 v_5 v_9 v_10 v_17
      hcrl_err hpc_err
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      hAns_err
      ?_
    exact Entails.of_eq (by ac_rfl)
  · -- `r = .ok []`
    have ⟨hget_eq, htr_sf1⟩ :
        x.dir.get rd s0.fs.files (keyName x.id) = .ok [] ∧ sf_1.trace = s0.trace :=
      ⟨hget_post.1.symm, hget_post.2⟩
    have hAns_miss :
        PkAns.missing =
          pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) := by
      rw [hget_eq]; rfl
    dsimp only [dirGetPayload]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw0, hw3⟩ => ?_
    change w_6 = 0#64 at hw3
    subst hw0 hw3
    apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_573).base + bv% (240)) hcrl_sf_1
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro hcrl_miss
    apply SepWPp.of_sepWP_ret
    apply bind_sepWP_state; intro s_miss
    have hpc_miss : s_miss.pc = (blkPl_573).base + bv% (240) := by
      simp only [s_miss, wp_norm, arm64_norm, *]; try bv_omega
    have hm_run : s_miss.status = .Running := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_sp : s_miss.sp = s0.sp - 256#64 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_tr : s_miss.trace = s0.trace := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_19 : s_miss.readReg64 .x19 = x.fut := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_20 : s_miss.readReg64 .x20 = x.out := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_21 : s_miss.readReg64 .x21 = 0#64 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_22 : s_miss.readReg64 .x22 = w_1 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_23 : s_miss.readReg64 .x23 = w_4 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_24 : s_miss.readReg64 .x24 = w_5 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_25 : s_miss.readReg64 .x25 = okTagVec := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_26 : s_miss.readReg64 .x26 = errTag := by
      simp only [s_miss, wp_norm, arm64_norm, *]; rfl
    have hm_27 : s_miss.readReg64 .x27 = s0.sp - 152#64 := by
      simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_28 : s_miss.readReg64 .x28 = s0.readReg64 .x28 := by
      simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_29 : s_miss.readReg64 .x29 = s0.sp - 96#64 := by
      simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_vr : calleeSavedVRegs s_miss = calleeSavedVRegs s0 := by
      simp only [s_miss, wp_norm, arm64_norm, *]
    apply finish_epilogue_p pathOk
    refine step_ok_240_placed hDeallocCells hDropCells
      .missing []
      w_4 w_5 w w_1 (BitVec.ofNat 64 (keyName x.id).length)
      errTag okTagVec (s0.readReg64 .x28) (s0.sp - 152#64) 0#64
      v_4 v_5 v v_1 v_2 v_3 v_9 v_10
      okTagVec w_4 w_5 0#64 w_7 w_8 v_17
      emp
      hcrl_miss hpc_miss hm_run hm_sp hal0 hm_tr
      hm_19 hm_20 hm_21 hm_22 hm_23 hm_24 hm_25 hm_26 hm_27 hm_28 hm_29 hm_vr
      hAns_miss
      (Or.inl ⟨rfl, rfl, rfl⟩)
      ?_
    rw [emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · -- `r = .ok (b0 :: rest)`
    have ⟨hget_eq, htr_sf1⟩ :
        x.dir.get rd s0.fs.files (keyName x.id) = .ok (b0 :: rest) ∧ sf_1.trace = s0.trace :=
      ⟨hget_post.1.symm, hget_post.2⟩
    have hblen : (b0 :: rest).length < 2 ^ 32 := hsize0 (b0 :: rest) hget_eq
    have hpos : 0 < (b0 :: rest).length := by simp
    have hblen_bv : (BitVec.ofNat 64 (b0 :: rest).length).toNat = (b0 :: rest).length :=
      Nat.mod_eq_of_lt (by omega)
    have hblen_nz : BitVec.ofNat 64 (b0 :: rest).length ≠ 0#64 := by
      intro hz
      have h0 : (BitVec.ofNat 64 (b0 :: rest).length).toNat = 0 := congrArg BitVec.toNat hz
      omega
    have hblen_eq : (BitVec.ofNat 64 (b0 :: rest).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hblen_nz
    have hblen_ne : (BitVec.ofNat 64 (b0 :: rest).length != 0#64) = true :=
      bne_iff_ne.mpr hblen_nz
    dsimp only [dirGetPayload]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw0, hw3⟩ => ?_
    subst hw0 hw3
    apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 65) hcrl_sf_1
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro hcrl3
    wp_call_spec_lscro hDecCells (pkDecCellsSpec A calleeStk) hcrl3
      (w_5, b0 :: rest, s0.sp - 152#64, _, _, _, _, _, _, _, s0.sp - 256#64)
    case panic =>
      intro sf_p _ hm
      rw [← sepConj_assoc]
      exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
    rcases hdec : PreKeyRecord.deserialize (b0 :: rest) with e | rec
    · apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_573).base + bv% (152)) hcrl_sf_2
      refine sepWP_peek_err_tag_p (A := A) (e := e) (d0 := w_2) (d1 := w_3) (d2 := w_6) (d3 := w_9)
        (d4 := w_10) (d5 := w_11) (d6 := w_12)
        (Rest := ((s0.sp - 152#64) ↦₆₄ w_2) ∗ ((s0.sp - 144#64) ↦₆₄ w_3) ∗
          ((s0.sp - 136#64) ↦₆₄ w_6) ∗ ((s0.sp - 128#64) ↦₆₄ w_9) ∗
          ((s0.sp - 120#64) ↦₆₄ w_10) ∗ ((s0.sp - 112#64) ↦₆₄ w_11) ∗
          ((s0.sp - 104#64) ↦₆₄ w_12) ∗
          (w_5 ↦ₛ (b0 :: rest)) ∗ vecU8BufRest A w_4 w_5 (b0 :: rest) ∗
          (w_1 ↦ₛ keyName x.id) ∗ vecU8BufRest A w w_1 (keyName x.id) ∗
          pkBoxKeep x s0 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
          ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
          ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
          ((s0.sp - 200#64) ↦₆₄ w) ∗ ((s0.sp - 192#64) ↦₆₄ w_1) ∗
          ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
        (by simp only [pointsToBytes_cons]; ac_rfl) fun hd0_tag => ?_
      have hd0_eq : (w_2 + 1#64 == 0#64) = true := by rw [hd0_tag]; rfl
      have hd0_ne : (w_2 + 1#64 != 0#64) = false := by rw [hd0_tag]; rfl
      wp_steps
      try
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
      intro hcrl_de
      apply SepWPp.of_sepWP_ret
      apply bind_sepWP_state; intro s_de
      have hpc_de : s_de.pc = (blkPl_573).base + bv% (152) := by
        simp only [s_de, wp_norm, arm64_norm, *]; try bv_omega
      have hAns_de :
          PkAns.decodeErr e =
            pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) := by
        rw [hget_eq, pkAnsOf, hdec]
      apply finish_epilogue_p pathOk
      refine step_dec_err_152_placed hDeallocCells
        e (b0 :: rest)
        w_4 w_5 w w_1 (BitVec.ofNat 64 (keyName x.id).length)
        w_2 w_3 w_6 w_9 w_10 w_11 w_12
        v v_1 v_2 v_3 v_9 v_10
        hcrl_de hpc_de
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        hal0
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        hd0_tag hAns_de
        ?_
      exact Entails.of_eq (by simp only [pointsToBytes_cons]; ac_rfl)
    · apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_573).base + bv% (240)) hcrl_sf_2
      refine sepWP_peek_ok_hd0_p (A := A) (rec := rec) (d0 := w_2) (d1 := w_3) (d2 := w_6) (d3 := w_9)
        (d4 := w_10) (d5 := w_11) (d6 := w_12)
        (Rest := ((s0.sp - 152#64) ↦₆₄ w_2) ∗ ((s0.sp - 144#64) ↦₆₄ w_3) ∗
          ((s0.sp - 136#64) ↦₆₄ w_6) ∗ ((s0.sp - 128#64) ↦₆₄ w_9) ∗
          ((s0.sp - 120#64) ↦₆₄ w_10) ∗ ((s0.sp - 112#64) ↦₆₄ w_11) ∗
          ((s0.sp - 104#64) ↦₆₄ w_12) ∗
          (w_5 ↦ₛ (b0 :: rest)) ∗ vecU8BufRest A w_4 w_5 (b0 :: rest) ∗
          (w_1 ↦ₛ keyName x.id) ∗ vecU8BufRest A w w_1 (keyName x.id) ∗
          pkBoxKeep x s0 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
          ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
          ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
          ((s0.sp - 200#64) ↦₆₄ w) ∗ ((s0.sp - 192#64) ↦₆₄ w_1) ∗
          ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
        (by simp only [pointsToBytes_cons]; ac_rfl) fun hd0 => ?_
      have hd0_eq : (w_2 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hd0
      have hd0_ne : (w_2 + 1#64 != 0#64) = true := bne_iff_ne.mpr hd0
      wp_steps
      try
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
      intro hcrl_ok
      apply SepWPp.of_sepWP_ret
      apply bind_sepWP_state; intro s_ok
      have hpc_ok : s_ok.pc = (blkPl_573).base + bv% (240) := by
        simp only [s_ok, wp_norm, arm64_norm, *]; try bv_omega
      have hAns_ok :
          PkAns.found rec =
            pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) := by
        rw [hget_eq, pkAnsOf, hdec]
      apply finish_epilogue_p pathOk
      refine step_ok_240_placed hDeallocCells hDropCells
        (.found rec) (b0 :: rest)
        w_4 w_5 w w_1 (BitVec.ofNat 64 (keyName x.id).length)
        w_2 w_3 w_6 w_9 w_10 w_11 w_12
        v v_1 v_2 v_3 v_9 v_10
        w_2 w_3 w_6 w_9 w_10 w_11 w_12
        (pkDecPayload A (.ok rec) w_2 w_3 w_6 w_9 w_10 w_11 w_12)
        hcrl_ok hpc_ok
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        hal0
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        hAns_ok
        (Or.inr ⟨rec, rfl, hd0, rfl⟩)
        ?_
      exact Entails.of_eq (by simp only [pointsToBytes_cons]; ac_rfl)

end Placed

end CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
