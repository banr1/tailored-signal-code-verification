/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `.points` Deserialization for `<PolyEncoder>::from_pb`

Threads `RustCliAllocBudget M`, `encoderFromPbPtsLoopEvents`, `VmPreserved`, and
`AllocCallPreserved` through `.points` header initialization, inner decoding loop, and 16-slot outer
loop on Block `374`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoopPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_374 blkPl_374 lsρ)
open CryptoVerification.LibsignalSpqrV1 (GF16 Point PolynomialError u16FromBeBytes)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecAt vecBuf vecHeader vecOf vecU8)
open CryptoVerification.SpqrV1.Drop (
  vecGF16ListOf vecGF16Of
)
open CryptoVerification.SpqrV1.Poly (gf16Align gf16At gf16Stride)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (
  beq_false_of_gt beq_false_of_lt bit0_and_32_eq_one_of_odd
  bit0_and_32_eq_zero_of_even bit0_and_64_eq_one_of_odd bit0_and_64_eq_zero_of_even
  bne_of_gt bne_of_lt bv_add_lit_add_lit bv_lit_add_lit
  bytesToGF16ListTotal bytesToGF16ListTotal_length
  cells_456_eq decodePbPointsTotal emptySlotAt emptySlotAt_entails_vecGF16Of emptySlotsAt
  emptySlotsAt_entails_vecGF16ListOf exists_pow_two_eq_two fsp_add_201_add_255
  fsp_add_255_add_201 lsr_62_eq_zero lsr_62_nat_eq_zero madd_24_eq
  memRegion_two_cons mul_24_eq ofNat_beq_zero_false_of_pos ofNat_ne_zero_of_pos
  ofNat_succ_add_neg_one ofNat_succ_sub_one pointsToBytes_pair_cons
  rev16_pair_eq_u16FromBeBytes sepWP_cells_succ sepWP_cells_zero sepWPp_pure_mid
  shiftLeft_1_eq_mul_2 shiftLeft_1_nat_eq_mul_2 spqrRustAllocSym spqrRustNoAllocShimSym
  ule_false_of_lt ult_of_lt vecGF16ListOf_append vecU8Rest vecU8_close vecU8_open
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget
  RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (
  encoderFromPbPtsLoopEvents encoderFromPbPtsSlotEvents
)

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit ofNat_succ_sub_one
  ofNat_succ_add_neg_one madd_24_eq mul_24_eq fsp_add_201_add_255
  fsp_add_255_add_201 exists_pow_two_eq_two

private theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h01 : AllocCallPreserved s0 s1) (h12 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s : State} {tp : BitVec 64}
    {P P_mid : SepProp} {Q : State → Prop}
    (hent : P ⊢ P_mid)
    (hwp : SepWP prog target s P_mid (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.weaken_pre hent hwp

private theorem sync_pool_reg {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {target : BitVec 64}
    {s1 s2 : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hf : P = A.pool lim st s1 ∗ F := by sep_focus)
    (heq : A.pool lim st s1 = A.pool lim st s2)
    (hnext : SepWP prog target s2 (A.pool lim st s2 ∗ F) post) :
    SepWP prog target s2 P post := by
  rw [hf, heq]; exact hnext

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem seq_vm_wpp {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid ret : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q_mid : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q_mid sm →
      SepWPp (P.rebase b Hk) ret sm P_mid Q Qp) :
    SepWPp (P.rebase b Hk) ret s Pre Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQm⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hvm hQm))

private theorem encoderFromPbPtsLoopEvents_cons_odd {bs : List (BitVec 8)}
    {rest : List (List (BitVec 8))} (hodd : (bs.length % 2 != 0) = true) :
    encoderFromPbPtsLoopEvents (bs :: rest) = [] := by
  have hbeq : (bs.length % 2 == 0) = false := by
    rw [beq_eq_false_iff_ne]
    exact bne_iff_ne.mp hodd
  simp [encoderFromPbPtsLoopEvents, List.takeWhile, hbeq]

private theorem encoderFromPbPtsLoopEvents_cons_even {bs : List (BitVec 8)}
    {rest : List (List (BitVec 8))} (heven : bs.length % 2 = 0) :
    encoderFromPbPtsLoopEvents (bs :: rest) =
      encoderFromPbPtsSlotEvents bs ++ encoderFromPbPtsLoopEvents rest := by
  have hbeq : (bs.length % 2 == 0) = true := beq_iff_eq.mpr heven
  simp [encoderFromPbPtsLoopEvents, List.takeWhile, hbeq]

variable [LibsignalPlacement]

/-- Initializes 16 empty `Point` headers `(0, 2, 0)` at `fsp + 480 .. fsp + 864` (`+56 -> +260`)
    and stores `out` (`x0`) at `[fsp + 56]`, preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem pts_init_empty_headers_placed {ext : String → Option (State → State)}
    (s : State) (fsp out pbA ptsPtr v_out : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 56#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 260#64) s
      (memRegion (fsp + 480#64) 384 ∗
        ((fsp + 56#64) ↦₆₄ v_out) ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ emptySlotsAt (fsp + 480#64) 16 ∗
          ((fsp + 56#64) ↦₆₄ out) ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x21 = 2#64 ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 0#64 ∧
        sm.readReg64 .x25 = ptsPtr ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  rw [ProofLib.memRegion_cells (fsp + 480#64) 48 (by decide)]
  iterate 24 (apply sepWP_cells_succ; intro)
  iterate 24 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  by_vm_steps (
    wp_steps
    refine align_pre_vm ?_ ?_
    · simp only [emptySlotsAt, emptySlotAt, sepConj_emp, bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
      exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only [AllocCallPreserved]
      wp_done
  )

/-- Inner loop of `.points` (`+376 -> +440`) in `[LibsignalPlacement]`, preserving `VmPreserved`
    and `AllocCallPreserved`. -/
theorem pts_inner_loop_placed {ext : String → Option (State → State)}
    (n : Nat) :
    ∀ (bs : List (BitVec 8)) (k totalBytes : Nat)
      (s : State) (fsp hdrAddr bsPtr outPtr v_len : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
      (Frame : SepProp),
      bs.length = 2 * (n + 1) →
      2 * k + bs.length = totalBytes →
      totalBytes < 2 ^ 62 →
      s.pc = (blkPl_374).base + 376#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x8 = outPtr →
      s.readReg64 .x19 = BitVec.ofNat 64 totalBytes →
      s.readReg64 .x20 = hdrAddr →
      s.readReg64 .x22 = outPtr →
      s.readReg64 .x23 = BitVec.ofNat 64 (2 * k) →
      s.readReg64 .x28 = BitVec.ofNat 64 (k + 1) →
      SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
        ((blkPl_374).base + 440#64) s
        (((hdrAddr + 8#64) ↦₆₄ bsPtr) ∗
          ((hdrAddr + 16#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
          ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
          ((fsp + 472#64) ↦₆₄ v_len) ∗
          ((bsPtr + BitVec.ofNat 64 (2 * k)) ↦ₛ bs) ∗
          memRegion (outPtr + BitVec.ofNat 64 (2 * k)) bs.length ∗
          Frame)
        (fun sm Pm =>
          VmPreserved s sm ∧
          (Pm ⊢ ((hdrAddr + 8#64) ↦₆₄ bsPtr) ∗
            ((hdrAddr + 16#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
            ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (k + n + 1)) ∗
            ((bsPtr + BitVec.ofNat 64 (2 * k)) ↦ₛ bs) ∗
            arrayAt gf16At 2 (outPtr + BitVec.ofNat 64 (2 * k)) (bytesToGF16ListTotal bs) ∗
            Frame) ∧
          sm.sp = fsp ∧
          sm.readReg64 .x20 = hdrAddr ∧
          sm.readReg64 .x21 = s.readReg64 .x21 ∧
          sm.readReg64 .x22 = outPtr ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x25 = s.readReg64 .x25 ∧
          sm.readReg64 .x26 = s.readReg64 .x26 ∧
          sm.readReg64 .x29 = s.readReg64 .x29 ∧
          sm.trace = s.trace ∧
          AllocCallPreserved s sm ∧
          calleeSavedVRegs sm = calleeSavedVRegs s) := by
  induction n with
  | zero =>
    intro bs k totalBytes s fsp hdrAddr bsPtr outPtr v_len hfsp_align Frame
      hlen htot hmax hpc hrun hsp hx8 hx19 hx20 hx22 hx23 hx28
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · have htot' : 2 * k + 2 = totalBytes := by simpa using htot
      have hlt1 : 2 * k < totalBytes := by omega
      have hlt2 : 2 * k + 1 < totalBytes := by omega
      have hk_lt : k < totalBytes := by omega
      have hmax64 : totalBytes < 2 ^ 64 := by omega
      have h_ule1 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k)) = false :=
        ule_false_of_lt hlt1 hmax64
      have h_ult1 : BitVec.ult (BitVec.ofNat 64 (2 * k)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt1 hmax64
      have h_ule2 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k + 1)) = false :=
        ule_false_of_lt hlt2 hmax64
      have h_ult2 : BitVec.ult (BitVec.ofNat 64 (2 * k + 1)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt2 hmax64
      have h_bne : (BitVec.ofNat 64 k != BitVec.ofNat 64 totalBytes) = true :=
        bne_of_lt hk_lt hmax64
      have h_bne' : (BitVec.ofNat 64 totalBytes != BitVec.ofNat 64 k) = true :=
        bne_of_gt hk_lt hmax64
      have h_beq : (BitVec.ofNat 64 k == BitVec.ofNat 64 totalBytes) = false :=
        beq_false_of_lt hk_lt hmax64
      have h_beq' : (BitVec.ofNat 64 totalBytes == BitVec.ofNat 64 k) = false :=
        beq_false_of_gt hk_lt hmax64
      have h_end_eq : BitVec.ofNat 64 (2 * k + 2) = BitVec.ofNat 64 totalBytes :=
        congrArg (BitVec.ofNat 64) htot'
      rw [pointsToBytes_pair_cons (bsPtr + BitVec.ofNat 64 (2 * k)) b0 b1 []]
      dsimp only [pointsToBytes, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
      rw [ProofLib.memRegion_two (outPtr + BitVec.ofNat 64 (2 * k))]
      simp only [sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro d16
      by_vm_steps (
        wp_steps
        refine align_pre_vm ?_ ?_
        · dsimp only [bytesToGF16ListTotal, arrayAt, gf16At, GF16.new, pointsToBytes]
          simp only [Nat.add_zero, sepConj_emp, rev16_pair_eq_u16FromBeBytes]
          exact Entails.of_eq (by sep_ac_rfl)
        · dsimp only [AllocCallPreserved]
          wp_done
      )
    · simp at hlen
  | succ n ih =>
    intro bs k totalBytes s fsp hdrAddr bsPtr outPtr v_len hfsp_align Frame
      hlen htot hmax hpc hrun hsp hx8 hx19 hx20 hx22 hx23 hx28
    rcases bs with _ | ⟨b0, _ | ⟨b1, bs'⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · have hlen' : bs'.length = 2 * (n + 1) := by simp at hlen; omega
      have htot' : 2 * (k + 1) + bs'.length = totalBytes := by simp at htot; omega
      have hlt1 : 2 * k < totalBytes := by omega
      have hlt2 : 2 * k + 1 < totalBytes := by omega
      have hlt3 : 2 * k + 2 < totalBytes := by omega
      have hk_lt : k < totalBytes := by omega
      have hmax64 : totalBytes < 2 ^ 64 := by omega
      have h_ule1 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k)) = false :=
        ule_false_of_lt hlt1 hmax64
      have h_ult1 : BitVec.ult (BitVec.ofNat 64 (2 * k)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt1 hmax64
      have h_ule2 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k + 1)) = false :=
        ule_false_of_lt hlt2 hmax64
      have h_ult2 : BitVec.ult (BitVec.ofNat 64 (2 * k + 1)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt2 hmax64
      have h_ule3 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k + 2)) = false :=
        ule_false_of_lt hlt3 hmax64
      have h_ult3 : BitVec.ult (BitVec.ofNat 64 (2 * k + 2)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt3 hmax64
      have h_bne : (BitVec.ofNat 64 k != BitVec.ofNat 64 totalBytes) = true :=
        bne_of_lt hk_lt hmax64
      have h_bne' : (BitVec.ofNat 64 totalBytes != BitVec.ofNat 64 k) = true :=
        bne_of_gt hk_lt hmax64
      have h_beq : (BitVec.ofNat 64 k == BitVec.ofNat 64 totalBytes) = false :=
        beq_false_of_lt hk_lt hmax64
      have h_beq' : (BitVec.ofNat 64 totalBytes == BitVec.ofNat 64 k) = false :=
        beq_false_of_gt hk_lt hmax64
      have hbs_len_eq : (b0 :: b1 :: bs').length = 2 * ((n + 1) + 1) := by
        simp [hlen']; omega
      have hbs_addr : bsPtr + BitVec.ofNat 64 (2 * k + 2) = bsPtr + BitVec.ofNat 64 (2 * (k + 1)) := by
        congr 2
      rw [pointsToBytes_pair_cons (bsPtr + BitVec.ofNat 64 (2 * k)) b0 b1 bs',
          bv_add_lit_add_lit, hbs_addr, hbs_len_eq,
          memRegion_two_cons outPtr k (n + 1) (by omega),
          ← hlen']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro d16
      refine seq_vm_clean
        (mid := (blkPl_374).base + 376#64)
        (P_mid :=
          ((hdrAddr + 8#64) ↦₆₄ bsPtr) ∗
          ((hdrAddr + 16#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
          ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
          ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((bsPtr + BitVec.ofNat 64 (2 * (k + 1))) ↦ₛ bs') ∗
          memRegion (outPtr + BitVec.ofNat 64 (2 * (k + 1))) bs'.length ∗
          (((bsPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (b1 ++ b0)) ∗
            ((outPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ u16FromBeBytes b0 b1) ∗
            Frame))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x8 = outPtr ∧
          sm.readReg64 .x19 = BitVec.ofNat 64 totalBytes ∧
          sm.readReg64 .x20 = hdrAddr ∧
          sm.readReg64 .x21 = s.readReg64 .x21 ∧
          sm.readReg64 .x22 = outPtr ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 (2 * (k + 1)) ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x25 = s.readReg64 .x25 ∧
          sm.readReg64 .x26 = s.readReg64 .x26 ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 ((k + 1) + 1) ∧
          sm.readReg64 .x29 = s.readReg64 .x29 ∧
          sm.trace = s.trace ∧
          AllocCallPreserved s sm ∧
          calleeSavedVRegs sm = calleeSavedVRegs s)
        ?_ ?_
      · by_vm_steps (
          wp_steps
          refine align_pre_vm ?_ ?_
          · simp only [rev16_pair_eq_u16FromBeBytes]
            exact Entails.of_eq (by sep_ac_rfl)
          · have hk2 : BitVec.ofNat 64 (2 * k + 2) = BitVec.ofNat 64 (2 * (k + 1)) := by
              congr 1
            dsimp only [AllocCallPreserved]
            wp_done
        )
      · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1,
          hx24_1, hx25_1, hx26_1, hx28_1, hx29_1, htrace1, hacp1, hvregs1⟩
        have hrec := ih bs' (k + 1) totalBytes s1 fsp hdrAddr bsPtr outPtr
          (BitVec.ofNat 64 (k + 1)) hfsp_align
          (((bsPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (b1 ++ b0)) ∗
            ((outPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ u16FromBeBytes b0 b1) ∗
            Frame)
          hlen' htot' hmax hpc1 hrun1 hsp1 hx8_1 hx19_1 hx20_1 hx22_1 hx23_1 hx28_1
        refine SepWP.mono hrec ?_
        intro sf Pf _ _ ⟨hvmf, hPf, hspf, hx20f, hx21f, hx22f, hx24f, hx25f, hx26f, hx29f, htrf, hacpf, hvregsf⟩
        refine ⟨hvm1.trans hvmf, Entails.trans hPf ?_, hspf, hx20f, hx21f.trans hx21_1, hx22f,
          hx24f.trans hx24_1, hx25f.trans hx25_1, hx26f.trans hx26_1, hx29f.trans hx29_1,
          htrf.trans htrace1, allocCallPreserved_trans hacp1 hacpf, hvregsf.trans hvregs1⟩
        have hlen_idx : (k + 1) + n + 1 = k + (n + 1) + 1 := by omega
        have hout_addr : outPtr + BitVec.ofNat 64 (2 * k + 2) = outPtr + BitVec.ofNat 64 (2 * (k + 1)) := by
          congr 2
        rw [hlen_idx, ← hbs_addr]
        dsimp only [bytesToGF16ListTotal, arrayAt, gf16At, GF16.new, BitVec.ofNat_eq_ofNat]
        rw [bv_add_lit_add_lit, hout_addr]
        exact Entails.of_eq (by sep_ac_rfl)

/-- Odd-length error step (`+260 -> +1612`) in `[LibsignalPlacement]`, preserving `VmPreserved`
    and `AllocCallPreserved`. -/
theorem pts_elem_odd_step_placed {ext : String → Option (State → State)}
    (j : Nat) (bs : List (BitVec 8))
    (s : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hodd : bs.length % 2 ≠ 0)
    (hmax : bs.length < 2 ^ 62)
    (hpc : s.pc = (blkPl_374).base + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j)
    (hx25 : s.readReg64 .x25 = ptsPtr) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 1612#64)
      s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = s.readReg64 .x1 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hbit32 := bit0_and_32_eq_one_of_odd hodd hmax
  have hbit64 := bit0_and_64_eq_one_of_odd hodd hmax
  by_vm_steps (
    wp_steps
    dsimp only [AllocCallPreserved]
    wp_done
  )

/-- Empty-slice step (`+260 -> +476`) when `bs = []` in `[LibsignalPlacement]`, preserving
    `VmPreserved` and `AllocCallPreserved`. -/
theorem pts_elem_even_empty_step_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (j : Nat) (s : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 2#64)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j)
    (hx25 : s.readReg64 .x25 = ptsPtr) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 476#64)
      s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        cells (fsp + 456#64) 3 ∗
        Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          (∃∗ cap, ∃∗ outPtr,
            ((fsp + 456#64) ↦₆₄ cap) ∗
            ((fsp + 464#64) ↦₆₄ outPtr) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal []).length) ∗
            vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal [])) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) ∧
        sm.readReg64 .x21 = 2#64 ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 j ∧
        sm.readReg64 .x25 = ptsPtr ∧
        sm.readReg64 .x26 = s.readReg64 .x1 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  dsimp only [emptySlotAt]
  rw [cells_456_eq fsp]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v0
  apply ProofLib.SepWP.exists_left; intro v1
  apply ProofLib.SepWP.exists_left; intro v2
  by_vm_steps (
    wp_steps
    refine align_pre_vm ?_ ?_
    · dsimp only [emptySlotAt, bytesToGF16ListTotal, List.length_nil, BitVec.ofNat_eq_ofNat]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((fsp + 456#64) ↦₆₄ 0#64) ∗ ((fsp + 464#64) ↦₆₄ 2#64) ∗ ((fsp + 472#64) ↦₆₄ 0#64)) ∗
          (((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
           (((fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ↦₆₄ 0#64) ∗
            ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ 2#64) ∗
            ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64)) ∗
           Frame) by sep_ac_rfl)) ?_
      refine Entails.trans
        (sepConj_mono_left
          (show ((fsp + 456#64) ↦₆₄ 0#64) ∗ ((fsp + 464#64) ↦₆₄ 2#64) ∗ ((fsp + 472#64) ↦₆₄ 0#64) ⊢
            ∃∗ cap, ∃∗ outPtr,
              ((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗ ((fsp + 472#64) ↦₆₄ 0#64) ∗
              vecBuf A 2 2 gf16At cap outPtr [] by
            have hev := emptySlotAt_entails_vecGF16Of A (fsp + 456#64)
            have h1 : fsp + 456#64 + 8#64 = fsp + 464#64 := by bv_omega
            have h2 : fsp + 456#64 + 16#64 = fsp + 472#64 := by bv_omega
            unfold emptySlotAt vecGF16Of vecOf vecAt vecHeader gf16Stride gf16Align at hev
            dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hev
            rw [h1, h2] at hev
            simp only [sepConj_assoc] at hev
            exact hev))
        (Entails.of_eq (by sep_ac_rfl))
    · dsimp only [AllocCallPreserved]
      wp_done
  )

/-- Non-empty even-slice step (`+260 -> +476`) when `bs.length = 2 * (m + 1)` under `FitsEvents`. -/
theorem pts_elem_even_nonempty_step_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (j m : Nat) (bs : List (BitVec 8)) (st : M.σ)
    (hFit : FitsEvents M lim st (rustAllocEvents (2 * bs.length) 2))
    (s0 s : State) (fsp ptsPtr bsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hlen : bs.length = 2 * (m + 1)) (hmax : bs.length < 2 ^ 62)
    (hpc : s.pc = (blkPl_374).base + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 2#64) (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j) (hx25 : s.readReg64 .x25 = ptsPtr)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm,
      sm.pc = (blkPl_374).base + 476#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) →
      sm.readReg64 .x21 = 2#64 → sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = BitVec.ofNat 64 j → sm.readReg64 .x25 = ptsPtr →
      sm.readReg64 .x26 = s.readReg64 .x1 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      AllocCallPreserved s0 sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗ emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          (∃∗ cap, ∃∗ outPtr,
            ((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
            vecBuf A.repAlloc 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * bs.length) 2) st) sm ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗ emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        cells (fsp + 456#64) 3 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have heven : bs.length % 2 = 0 := by omega
  have hpos : 0 < bs.length := by omega
  have hn64 : bs.length < 2 ^ 64 := by omega
  have h2n64 : 2 * bs.length < 2 ^ 64 := by omega
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk (2 * bs.length) 2 := ⟨⟨by omega, hpow2, by omega⟩, by decide⟩
  have h2len_toNat : (BitVec.ofNat 64 (2 * bs.length)).toNat = 2 * bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2n64]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbit32 := bit0_and_32_eq_zero_of_even heven hmax
  have hbit64 := bit0_and_64_eq_zero_of_even heven hmax
  have hlsr1 := lsr_62_eq_zero hmax
  have hlsr2 := lsr_62_nat_eq_zero hmax
  have hne0 := ofNat_ne_zero_of_pos hpos hn64
  have hbeq0 := ofNat_beq_zero_false_of_pos hpos hn64
  have hlsl1 := shiftLeft_1_eq_mul_2 hmax
  have hlsl2 := shiftLeft_1_nat_eq_mul_2 hmax
  have hlen_fn : True → bs.length = 2 * (m + 1) := fun _ => hlen
  clear hlen
  have halloc_no_oom : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  simp only [rustAllocShimVmSpec] at hshim
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat] at halloc_no_oom
  apply SepWPp.of_sepWP (mid := (blkPl_374).base + 308#64)
  wp_steps
  wp_apply
  have hacp_sh : AllocCallPreserved s sf := by assumption
  wp_steps
  refine sync_pool_reg (heq := by
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
      RustCliAllocBudget.pool_advancePC]
    rw [A.pool_of_vmPreserved ‹VmPreserved _ sf›]
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
      RustCliAllocBudget.pool_advancePC]) (hnext := ?_)
  wp_apply
  have hacp_al : AllocCallPreserved sf sf_1 := by assumption
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  conv => arg 4; simp only [sepConj_assoc]
  have hbeq_oom : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  set outPtr := sf_1.readReg64 (Reg.gpr 0#5)
  let st' := M.stepEvents (rustAllocEvents (2 * bs.length) 2) st
  have hacp_sf1 : AllocCallPreserved s0 sf_1 := by
    have hacp_to_sh : AllocCallPreserved s0 sf := by
      rcases hacp with ⟨hfs, htr, hsig, htp, hbrk0, horacle, hsymtab⟩
      rcases hacp_sh with ⟨hfs1, htr1, hsig1, htp1, hbrk1, horacle1, hsymtab1⟩
      exact ⟨hfs1.trans (by simp only [arm64_norm, wp_norm, *]),
        htr1.trans (by simp only [arm64_norm, wp_norm, *]),
        hsig1.trans (by simp only [arm64_norm, wp_norm, *]),
        htp1.trans (by simp only [arm64_norm, wp_norm, *]),
        hbrk1.trans (by simp only [arm64_norm, wp_norm, *]),
        horacle1.trans (by simp only [arm64_norm, wp_norm, *]),
        hsymtab1.trans (by simp only [arm64_norm, wp_norm, *])⟩
    rcases hacp_to_sh with ⟨hfs, htr, hsig, htp, hbrk0, horacle, hsymtab⟩
    rcases hacp_al with ⟨hfs2, htr2, hsig2, htp2, hbrk2, horacle2, hsymtab2⟩
    exact ⟨hfs2.trans (by simp only [arm64_norm, wp_norm, *]),
      htr2.trans (by simp only [arm64_norm, wp_norm, *]),
      hsig2.trans (by simp only [arm64_norm, wp_norm, *]),
      htp2.trans (by simp only [arm64_norm, wp_norm, *]),
      hbrk2.trans (by simp only [arm64_norm, wp_norm, *]),
      horacle2.trans (by simp only [arm64_norm, wp_norm, *]),
      hsymtab2.trans (by simp only [arm64_norm, wp_norm, *])⟩
  have htr0 : sf_1.trace = s0.trace := hacp_sf1.2.1
  rw [cells_456_eq fsp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v1
  apply SepWPp.exists_elim; intro v2
  have hlen := hlen_fn trivial
  have hsplit_len : 2 * bs.length = bs.length + bs.length := by omega
  have hsplit_bound : bs.length + bs.length ≤ 2 ^ 64 := by omega
  refine seq_vm_wpp (mid := (blkPl_374).base + 376#64)
    (P_mid :=
      ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
      ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((fsp + 472#64) ↦₆₄ 0#64) ∗
      ((bsPtr + BitVec.ofNat 64 (2 * 0)) ↦ₛ bs) ∗
      memRegion (outPtr + BitVec.ofNat 64 (2 * 0)) bs.length ∗
      (A.live outPtr (bs.length + bs.length) 2 ∗
        memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length ∗
        ((fsp + 464#64) ↦₆₄ outPtr) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        A.pool lim st' sf_1 ∗ stackAt fsp allocHookStack ∗ Frame))
    (Q_mid := fun s2 =>
      s2.sp = fsp ∧
      s2.readReg64 .x8 = outPtr ∧
      s2.readReg64 .x19 = BitVec.ofNat 64 bs.length ∧
      s2.readReg64 .x20 = ptsPtr + BitVec.ofNat 64 (24 * j) ∧
      s2.readReg64 .x21 = 2#64 ∧
      s2.readReg64 .x22 = outPtr ∧
      s2.readReg64 .x23 = BitVec.ofNat 64 (2 * 0) ∧
      s2.readReg64 .x24 = BitVec.ofNat 64 j ∧
      s2.readReg64 .x25 = ptsPtr ∧
      s2.readReg64 .x26 = s.readReg64 .x1 ∧
      s2.readReg64 .x28 = BitVec.ofNat 64 (0 + 1) ∧
      s2.readReg64 .x29 = s.readReg64 .x29 ∧
      s2.trace = s0.trace ∧
      AllocCallPreserved s0 s2 ∧
      calleeSavedVRegs s2 = calleeSavedVRegs s0)
    ?_ ?_
  · rcases hacp_sf1 with ⟨hfs_a, _, hsig_a, htp_a, hbrk_a, horacle_a, hsymtab_a⟩
    by_vm_steps (
      wp_steps
      rw [hsplit_len, ProofLib.memRegion_split outPtr bs.length bs.length hsplit_bound]
      refine align_pre_vm ?_ ?_
      · dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        simp only [BitVec.add_zero]
        exact Entails.of_eq (by sep_ac_rfl)
      · dsimp only [AllocCallPreserved]
        wp_done
    )
  · intro s2 hpc2 hrun2 hvm2 ⟨hsp2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
      hx24_2, hx25_2, hx26_2, hx28_2, hx29_2, htr2, hacp2, hvregs2⟩
    rw [← A.pool_of_vmPreserved hvm2]
    have hloop := pts_inner_loop_placed (ext := ext) m bs 0 bs.length s2 fsp
      (ptsPtr + BitVec.ofNat 64 (24 * j)) bsPtr outPtr 0#64 hfsp_align
      (A.live outPtr (bs.length + bs.length) 2 ∗
        memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length ∗
        ((fsp + 464#64) ↦₆₄ outPtr) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        A.pool lim st' s2 ∗ stackAt fsp allocHookStack ∗ Frame)
      hlen (by omega) hmax hpc2 hrun2 hsp2 hx8_2 hx19_2 hx20_2 hx22_2 hx23_2 hx28_2
    refine seq_vm_wpp hloop ?_
    intro s3 hpc3 hrun3 hvm3 ⟨hsp3, hx20_3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx29_3, htr3, hacp3, hvregs3⟩
    rw [← A.pool_of_vmPreserved hvm3]
    have hacp_s3 : AllocCallPreserved s0 s3 := allocCallPreserved_trans hacp2 hacp3
    dsimp only [emptySlotAt, BitVec.ofNat_eq_ofNat]
    simp only [BitVec.add_zero, Nat.zero_add]
    refine seq_vm_wpp (mid := (blkPl_374).base + 476#64)
      (P_mid :=
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        (∃∗ cap, ∃∗ outPtr,
          ((fsp + 456#64) ↦₆₄ cap) ∗
          ((fsp + 464#64) ↦₆₄ outPtr) ∗
          ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
          vecBuf A.repAlloc 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
        A.pool lim st' s3 ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun s4 =>
        s4.sp = fsp ∧
        s4.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) ∧
        s4.readReg64 .x21 = 2#64 ∧
        s4.readReg64 .x23 = 24#64 ∧
        s4.readReg64 .x24 = BitVec.ofNat 64 j ∧
        s4.readReg64 .x25 = ptsPtr ∧
        s4.readReg64 .x26 = s.readReg64 .x1 ∧
        s4.readReg64 .x29 = s.readReg64 .x29 ∧
        s4.trace = s0.trace ∧
        AllocCallPreserved s0 s4 ∧
        calleeSavedVRegs s4 = calleeSavedVRegs s0)
      ?_ ?_
    · have hx24_s3 : s3.readReg64 .x24 = BitVec.ofNat 64 j := hx24_3.trans hx24_2
      have hx21_s3 : s3.readReg64 .x21 = 2#64 := hx21_3.trans hx21_2
      have hx25_s3 : s3.readReg64 .x25 = ptsPtr := hx25_3.trans hx25_2
      have hx26_s3 : s3.readReg64 .x26 = s.readReg64 .x1 := hx26_3.trans hx26_2
      have hx29_s3 : s3.readReg64 .x29 = s.readReg64 .x29 := hx29_3.trans hx29_2
      have htr_s3 : s3.trace = s0.trace := htr3.trans htr2
      have hvregs_s3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans hvregs2
      rcases hacp_s3 with ⟨hfs3, _, hsig3, htp3, hbrk3, horacle3, hsymtab3⟩
      by_vm_steps (
        wp_steps
        refine align_pre_vm ?_ ?_
        · have hpts_len := bytesToGF16ListTotal_length (m + 1) bs hlen
          have hcap_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
          dsimp only [emptySlotAt]
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
               ((fsp + 464#64) ↦₆₄ outPtr) ∗
               ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
               A.live outPtr (bs.length + bs.length) 2 ∗
               arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs) ∗
               memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length) ∗
              (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
               ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
               (bsPtr ↦ₛ bs) ∗
               (((fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ↦₆₄ 0#64) ∗
                ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ 2#64) ∗
                ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64)) ∗
               A.pool lim st' s3 ∗ stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
          refine Entails.trans
            (sepConj_mono_left
              (show ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
                ((fsp + 464#64) ↦₆₄ outPtr) ∗
                ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
                A.live outPtr (bs.length + bs.length) 2 ∗
                arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs) ∗
                memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length ⊢
                ∃∗ cap, ∃∗ outPtr,
                  ((fsp + 456#64) ↦₆₄ cap) ∗
                  ((fsp + 464#64) ↦₆₄ outPtr) ∗
                  ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
                  vecBuf A.repAlloc 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs) by
                refine Entails.sepExists_right (BitVec.ofNat 64 bs.length)
                  (Entails.sepExists_right outPtr ?_)
                unfold vecBuf
                have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := hne0
                rw [hpts_len, hcap_toNat]
                simp only [hcap_ne, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
                have hmul2 : bs.length * 2 = bs.length + bs.length := by omega
                have hm2 : (m + 1) * 2 = bs.length := by omega
                have hsub2 : (bs.length - (m + 1)) * 2 = bs.length := by omega
                rw [hmul2, hm2, hsub2]
                simp only [sepConj_pure_left_comm]
                refine Entails.pure_right ⟨by omega, by omega, hoom⟩ ?_
                exact Entails.of_eq (by sep_ac_rfl)))
            (Entails.of_eq (by sep_ac_rfl))
        · dsimp only [AllocCallPreserved]
          wp_done
      )
    · intro s4 hpc4 hrun4 hvm4 ⟨hsp4, hx19_4, hx21_4, hx23_4, hx24_4, hx25_4, hx26_4, hx29_4, htr4, hacp4, hvregs4⟩
      rw [← A.pool_of_vmPreserved hvm4]
      exact hcont s4 hpc4 hrun4 hsp4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 htr4 hacp4 hvregs4

/-- Combined even-slice step (`+260 -> +476`) for any `bs` with `bs.length % 2 = 0` under `FitsEvents`. -/
theorem pts_elem_even_step_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (j : Nat) (bs : List (BitVec 8)) (st : M.σ)
    (hFit : FitsEvents M lim st (encoderFromPbPtsSlotEvents bs))
    (s0 s : State) (fsp ptsPtr bsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp) (heven : bs.length % 2 = 0) (hmax : bs.length < 2 ^ 62)
    (hpc : s.pc = (blkPl_374).base + 260#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 2#64) (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j) (hx25 : s.readReg64 .x25 = ptsPtr)
    (htrace : s.trace = s0.trace) (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm,
      sm.pc = (blkPl_374).base + 476#64 → sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) →
      sm.readReg64 .x21 = 2#64 → sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = BitVec.ofNat 64 j → sm.readReg64 .x25 = ptsPtr →
      sm.readReg64 .x26 = s.readReg64 .x1 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace → AllocCallPreserved s0 sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          (∃∗ cap, ∃∗ outPtr,
            ((fsp + 456#64) ↦₆₄ cap) ∗
            ((fsp + 464#64) ↦₆₄ outPtr) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
            vecBuf A.repAlloc 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
          A.pool lim (M.stepEvents (encoderFromPbPtsSlotEvents bs) st) sm ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        cells (fsp + 456#64) 3 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  cases bs with
  | nil =>
    simp only [encoderFromPbPtsSlotEvents, List.isEmpty_nil, ↓reduceIte,
      AllocCostModel.stepEvents_nil] at hcont
    have hempty := pts_elem_even_empty_step_placed (A := A.repAlloc) (ext := ext)
      j s fsp ptsPtr hfsp_align
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        (bsPtr ↦ₛ []) ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc hrun hsp hx21 hx23 hx24 hx25
    refine SepWPp.weaken_pre
      (by dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by sep_ac_rfl))
      (seq_vm_wpp hempty ?_)
    intro sm hpcm hrunm hvmm ⟨hspm, hx19m, hx21m, hx23m, hx24m, hx25m, hx26m, hx29m, htrm, hacpm, hvregsm⟩
    rw [← A.pool_of_vmPreserved hvmm]
    refine SepWPp.weaken_pre
      (by dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by sep_ac_rfl))
      (hcont sm hpcm hrunm hspm hx19m hx21m hx23m hx24m hx25m hx26m hx29m
        (htrm.trans htrace) (allocCallPreserved_trans hacp hacpm) (hvregsm.trans hvregs))
  | cons b0 bs' =>
    simp only [encoderFromPbPtsSlotEvents, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      at hFit hcont
    have hlen_m : (b0 :: bs').length = 2 * ((b0 :: bs').length / 2 - 1 + 1) := by
      simp only [List.length_cons] at heven ⊢
      omega
    exact pts_elem_even_nonempty_step_placed hshim halloc j ((b0 :: bs').length / 2 - 1) (b0 :: bs')
      st hFit s0 s fsp ptsPtr bsPtr hfsp_align Frame hlen_m hmax
      hpc hrun hsp hx21 hx23 hx24 hx25 htrace hacp hvregs hcont

/-- Finish a single `.points` element (`+476 -> if j + 1 < 16 then +260 else +1648`) in
    `[LibsignalPlacement]`, preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem pts_elem_finish_step_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (j : Nat) (hj : j < 16) (bs : List (BitVec 8))
    (s : State) (fsp slotAddr ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 476#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = slotAddr) (hx21 : s.readReg64 .x21 = 2#64)
    (hx23 : s.readReg64 .x23 = 24#64) (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j)
    (hx25 : s.readReg64 .x25 = ptsPtr) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (if j + 1 < 16 then (blkPl_374).base + 260#64 else (blkPl_374).base + 1648#64) s
      (emptySlotAt slotAddr ∗
        (∃∗ cap, ∃∗ outPtr,
          ((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗
          ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
          vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ vecGF16Of A slotAddr (bytesToGF16ListTotal bs) ∗ cells (fsp + 456#64) 3 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x1 = s.readReg64 .x26 ∧
        sm.readReg64 .x21 = 2#64 ∧ sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 (j + 1) ∧ sm.readReg64 .x25 = ptsPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧ calleeSavedVRegs sm = calleeSavedVRegs s) := by
  dsimp only [emptySlotAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro outPtr
  have hj1 : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := (BitVec.ofNat_add j 1).symm
  by_cases hlt : j + 1 < 16
  · simp only [hlt, ↓reduceIte]
    have hne16 : (BitVec.ofNat 64 (j + 1) != 16#64) = true := bne_of_lt hlt (by decide)
    have hne16' : (16#64 != BitVec.ofNat 64 (j + 1)) = true := bne_of_gt hlt (by decide)
    have hbeq16 : (BitVec.ofNat 64 (j + 1) == 16#64) = false := beq_false_of_lt hlt (by decide)
    have hbeq16' : (16#64 == BitVec.ofNat 64 (j + 1)) = false := beq_false_of_gt hlt (by decide)
    clear hlt
    by_vm_steps (
      wp_steps
      refine align_pre_vm ?_ ?_
      · unfold vecGF16Of vecOf vecAt vecHeader
        rw [cells_456_eq fsp]
        refine Entails.trans
          (Entails.of_eq (show _ =
            ((slotAddr ↦₆₄ cap) ∗
             ((slotAddr + 8#64) ↦₆₄ outPtr) ∗
             ((slotAddr + 16#64) ↦₆₄
               BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
             vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
            (((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗
             ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length)) ∗
            Frame by sep_ac_rfl)) ?_
        refine sepConj_mono ?_ (sepConj_mono_left ?_)
        · exact Entails.sepExists_right cap (Entails.sepExists_right outPtr (Entails.of_eq (by sep_ac_rfl)))
        · exact Entails.sepExists_right cap (Entails.sepExists_right outPtr
            (Entails.sepExists_right (BitVec.ofNat 64 (bytesToGF16ListTotal bs).length)
              (Entails.of_eq (by sep_ac_rfl))))
      · dsimp only [AllocCallPreserved]
        wp_done
    )
  · simp only [hlt, ↓reduceIte]
    have hj15 : j = 15 := by omega
    subst hj15
    clear hlt
    by_vm_steps (
      wp_steps
      refine align_pre_vm ?_ ?_
      · unfold vecGF16Of vecOf vecAt vecHeader
        rw [cells_456_eq fsp]
        refine Entails.trans
          (Entails.of_eq (show _ =
            ((slotAddr ↦₆₄ cap) ∗
             ((slotAddr + 8#64) ↦₆₄ outPtr) ∗
             ((slotAddr + 16#64) ↦₆₄
               BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
             vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
            (((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗
             ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length)) ∗
            Frame by sep_ac_rfl)) ?_
        refine sepConj_mono ?_ (sepConj_mono_left ?_)
        · exact Entails.sepExists_right cap (Entails.sepExists_right outPtr (Entails.of_eq (by sep_ac_rfl)))
        · exact Entails.sepExists_right cap (Entails.sepExists_right outPtr
            (Entails.sepExists_right (BitVec.ofNat 64 (bytesToGF16ListTotal bs).length)
              (Entails.of_eq (by sep_ac_rfl))))
      · dsimp only [AllocCallPreserved]
        wp_done
    )

/-- Outer `.points` deserialization loop (`+260 -> +1612 / +1648`) under `FitsEvents`. -/
theorem pts_outer_loop_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (j : Nat) (acc : List (List GF16))
      (st : M.σ) (s : State) (Frame : SepProp),
      FitsEvents M lim st (encoderFromPbPtsLoopEvents rem) →
      rem ≠ [] → j + rem.length = 16 → acc.length = j →
      (∀ bs ∈ rem, bs.length < 2 ^ 62) →
      s.pc = (blkPl_374).base + 260#64 → s.status = .Running → s.sp = fsp →
      s.readReg64 .x21 = 2#64 → s.readReg64 .x23 = 24#64 →
      s.readReg64 .x24 = BitVec.ofNat 64 j → s.readReg64 .x25 = ptsPtr →
      s.trace = s0.trace → AllocCallPreserved s0 s →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ sm (tail : List Point),
        decodePbPointsTotal rem = .ok tail →
        sm.pc = (blkPl_374).base + 1648#64 → sm.status = .Running → sm.sp = fsp →
        sm.readReg64 .x1 = s.readReg64 .x1 → sm.readReg64 .x29 = s.readReg64 .x29 →
        sm.trace = s0.trace → AllocCallPreserved s0 sm →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A.repAlloc (fsp + 480#64) (acc ++ tail.map Point.value) ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 456#64) 3 ∗
            A.pool lim (M.stepEvents (encoderFromPbPtsLoopEvents rem) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame)
          Q Qp) →
      (∀ sm (errPts : List (List GF16)),
        decodePbPointsTotal rem = .error .serializationInvalid → errPts.length = 16 →
        sm.pc = (blkPl_374).base + 1612#64 → sm.status = .Running → sm.sp = fsp →
        sm.readReg64 .x1 = s.readReg64 .x1 → sm.readReg64 .x29 = s.readReg64 .x29 →
        sm.trace = s0.trace → AllocCallPreserved s0 sm →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A.repAlloc (fsp + 480#64) errPts ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 456#64) 3 ∗
            A.pool lim (M.stepEvents (encoderFromPbPtsLoopEvents rem) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame)
          Q Qp) →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
        (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) rem.length ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j)) rem ∗
          cells (fsp + 456#64) 3 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        Q Qp
  | [], _, _, _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => (hne rfl).elim
  | bs :: rest, j, acc, st, s, Frame, hFit, _, hj_rem, hacc_len, hmax, hpc, hrun, hsp,
    hx21, hx23, hx24, hx25, htrace, hacp, hvregs, hcont_ok, hcont_err => by
    have hbs_max : bs.length < 2 ^ 62 := hmax bs List.mem_cons_self
    have hrest_max : ∀ bs' ∈ rest, bs'.length < 2 ^ 62 :=
      fun bs' hm => hmax bs' (List.mem_cons_of_mem _ hm)
    have hj_lt : j < 16 := by simp only [List.length_cons] at hj_rem; omega
    dsimp only [List.length_cons, emptySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat]
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_left (vecU8_open A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) bs))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap
    apply SepWPp.exists_elim; intro bsPtr
    by_cases hodd_bool : (bs.length % 2 != 0) = true
    · have hodd : bs.length % 2 ≠ 0 := bne_iff_ne.mp hodd_bool
      have hdec_err : decodePbPointsTotal (bs :: rest) = .error .serializationInvalid := by
        simp [decodePbPointsTotal, hodd_bool]
      have hevs_odd := encoderFromPbPtsLoopEvents_cons_odd (rest := rest) hodd_bool
      have hstep := pts_elem_odd_step_placed (ext := ext) j bs s fsp ptsPtr hfsp_align
        (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ bs) ∗
          vecU8Rest A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 456#64) 3 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        hodd hbs_max hpc hrun hsp hx23 hx24 hx25
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (seq_vm_wpp hstep ?_)
      intro sm hpcm hrunm hvmm ⟨hspm, hx1m, hx29m, htrm, hacpm, hvregsm⟩
      rw [← A.pool_of_vmPreserved hvmm]
      have herr_len : (acc ++ List.replicate (rest.length + 1) ([] : List GF16)).length = 16 := by
        simp only [List.length_cons] at hj_rem
        rw [List.length_append, List.length_replicate, hacc_len]
        omega
      refine SepWPp.weaken_pre ?_
        (hcont_err sm (acc ++ List.replicate (rest.length + 1) []) hdec_err herr_len
          hpcm hrunm hspm hx1m hx29m (htrm.trans htrace)
          (allocCallPreserved_trans hacp hacpm) (hvregsm.trans hvregs))
      rw [hevs_odd, AllocCostModel.stepEvents_nil]
      have heq_pre :
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ bs) ∗
          vecU8Rest A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 456#64) 3 ∗ A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame =
          (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
           emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (rest.length + 1)) ∗
          (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
           ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           (bsPtr ↦ₛ bs) ∗
           vecU8Rest A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 456#64) 3 ∗ A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame := by
        dsimp only [emptySlotsAt]
        sep_ac_rfl
      rw [heq_pre]
      have hslots := emptySlotsAt_entails_vecGF16ListOf A.repAlloc (rest.length + 1)
        (fsp + 480#64 + BitVec.ofNat 64 (24 * j))
      have happ := vecGF16ListOf_append A.repAlloc acc (List.replicate (rest.length + 1) []) (fsp + 480#64)
      rw [hacc_len] at happ
      have hclose := vecU8_close A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
      dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]
      refine Entails.trans
        (sepConj_mono (Entails.trans (sepConj_mono_right hslots) (Entails.of_eq happ.symm))
          (sepConj_mono_left hclose))
        (Entails.of_eq (by sep_ac_rfl))
    · have heven : bs.length % 2 = 0 := by
        simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd_bool
        exact hodd_bool
      have hevs_even := encoderFromPbPtsLoopEvents_cons_even (rest := rest) heven
      rw [hevs_even, fitsEvents_append] at hFit
      rcases hFit with ⟨hFit_slot, hFit_rest⟩
      let st1 := M.stepEvents (encoderFromPbPtsSlotEvents bs) st
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (pts_elem_even_step_placed hshim halloc j bs st hFit_slot s0 s fsp ptsPtr bsPtr hfsp_align
          (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
            emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
            vecU8Rest A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            Frame)
          heven hbs_max hpc hrun hsp hx21 hx23 hx24 hx25 htrace hacp hvregs ?_)
      intro s1 hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1 htr1 hacp1 hvregs1
      have hfin := pts_elem_finish_step_placed (A := A.repAlloc) (ext := ext) j hj_lt bs s1 fsp
        (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ptsPtr hfsp_align
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗
          vecU8Rest A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          A.pool lim st1 s1 ∗ stackAt fsp allocHookStack ∗ Frame)
        hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx24_1 hx25_1
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (seq_vm_wpp hfin ?_)
      intro s2 hpc2 hrun2 hvm2 ⟨hsp2, hx1_2, hx21_2, hx23_2, hx24_2, hx25_2, hx29_2, htr2, hacp2, hvregs2⟩
      rw [← A.pool_of_vmPreserved hvm2]
      have hacp_s2 : AllocCallPreserved s0 s2 := allocCallPreserved_trans hacp1 hacp2
      have hclose := vecU8_close A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
      have happ := vecGF16ListOf_append A.repAlloc acc [bytesToGF16ListTotal bs] (fsp + 480#64)
      rw [hacc_len] at happ
      have hsingle : vecGF16ListOf A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) [bytesToGF16ListTotal bs] =
          vecGF16Of A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs) := by
        dsimp only [vecGF16ListOf, arrayAt]; simp only [sepConj_emp]
      rw [hsingle] at happ
      cases rest with
      | nil =>
        have hj15 : j = 15 := by simp only [List.length_cons, List.length_nil] at hj_rem; omega
        have hlt_false : ¬(j + 1 < 16) := by omega
        simp only [hlt_false, ↓reduceIte] at hpc2
        have hdec_ok : decodePbPointsTotal [bs] = .ok [{ value := bytesToGF16ListTotal bs }] := by
          simp [decodePbPointsTotal, hodd_bool]
        refine SepWPp.weaken_pre ?_
          (hcont_ok s2 [{ value := bytesToGF16ListTotal bs }] hdec_ok hpc2 hrun2 hsp2
            (hx1_2.trans hx26_1) (hx29_2.trans hx29_1) (htr2.trans htr1)
            hacp_s2 (hvregs2.trans hvregs1))
        have hevs1 : encoderFromPbPtsLoopEvents [bs] = encoderFromPbPtsSlotEvents bs := by
          simpa [encoderFromPbPtsLoopEvents] using hevs_even
        rw [hevs1]
        dsimp only [List.map, List.length_nil, emptySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat, st1]
        simp only [sepConj_emp]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
             vecGF16Of A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
             ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             (bsPtr ↦ₛ bs) ∗
             vecU8Rest A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
            cells (fsp + 456#64) 3 ∗ A.pool lim (M.stepEvents (encoderFromPbPtsSlotEvents bs) st) s2 ∗
            stackAt fsp allocHookStack ∗ Frame by sep_ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
          (Entails.of_eq (by sep_ac_rfl))
      | cons bs' rest' =>
        have hlt_true : j + 1 < 16 := by simp only [List.length_cons] at hj_rem; omega
        simp only [hlt_true, ↓reduceIte] at hpc2
        have hj_addr1 : fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64 =
            fsp + 480#64 + BitVec.ofNat 64 (24 * (j + 1)) := by
          rw [bv_add_lit_add_lit]; rfl
        have hj_addr2 : ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64 =
            ptsPtr + BitVec.ofNat 64 (24 * (j + 1)) := by
          rw [bv_add_lit_add_lit]; rfl
        refine SepWPp.weaken_pre ?_
          (pts_outer_loop_placed hshim halloc s0 fsp ptsPtr hfsp_align (bs' :: rest') (j + 1)
            (acc ++ [bytesToGF16ListTotal bs]) st1 s2
            (vecU8 A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) bs ∗ Frame)
            hFit_rest
            (List.cons_ne_nil _ _)
            (by simp only [List.length_cons] at hj_rem ⊢; omega)
            (by rw [List.length_append, hacc_len]; rfl)
            hrest_max hpc2 hrun2 hsp2 hx21_2 hx23_2 hx24_2 hx25_2 (htr2.trans htr1)
            hacp_s2 (hvregs2.trans hvregs1)
            (fun sm tail hdec_tail hpcm hrunm hspm hx1m hx29m htrm hacpm hvregsm => ?_)
            (fun sm errPts hdec_err herr_len hpcm hrunm hspm hx1m hx29m htrm hacpm hvregsm => ?_))
        · rw [← hj_addr1, ← hj_addr2]
          refine Entails.trans
            (Entails.of_eq (show _ =
              (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
               vecGF16Of A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
              (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
               ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
               (bsPtr ↦ₛ bs) ∗
               vecU8Rest A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
              emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) (bs' :: rest').length ∗
              arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) (bs' :: rest') ∗
              cells (fsp + 456#64) 3 ∗ A.pool lim st1 s2 ∗ stackAt fsp allocHookStack ∗ Frame by sep_ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
            (Entails.of_eq (by sep_ac_rfl))
        · have hdec_cons : decodePbPointsTotal (bs :: bs' :: rest') =
              .ok ({ value := bytesToGF16ListTotal bs } :: tail) := by
            change (if bs.length % 2 != 0 then Except.error PolynomialError.serializationInvalid
              else match decodePbPointsTotal (bs' :: rest') with
              | Except.error e => Except.error e
              | Except.ok tail => Except.ok ({ value := bytesToGF16ListTotal bs } :: tail)) = _
            simp only [hodd_bool, Bool.false_eq_true, ↓reduceIte, hdec_tail]
          have happ_assoc : (acc ++ [bytesToGF16ListTotal bs]) ++ tail.map Point.value =
              acc ++ ({ value := bytesToGF16ListTotal bs } :: tail).map Point.value := by
            simp [List.append_assoc]
          have hst_eq :
              M.stepEvents (encoderFromPbPtsLoopEvents (bs' :: rest')) st1 =
                M.stepEvents (encoderFromPbPtsLoopEvents (bs :: bs' :: rest')) st := by
            dsimp only [st1]
            rw [← M.stepEvents_append, ← hevs_even]
          rw [happ_assoc, ← hj_addr2, hst_eq]
          refine SepWPp.weaken_pre
            (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by sep_ac_rfl))
            (hcont_ok sm ({ value := bytesToGF16ListTotal bs } :: tail) hdec_cons
              hpcm hrunm hspm (hx1m.trans (hx1_2.trans hx26_1))
              (hx29m.trans (hx29_2.trans hx29_1)) htrm hacpm hvregsm)
        · have hdec_cons : decodePbPointsTotal (bs :: bs' :: rest') = .error .serializationInvalid := by
            change (if bs.length % 2 != 0 then Except.error PolynomialError.serializationInvalid
              else match decodePbPointsTotal (bs' :: rest') with
              | Except.error e => Except.error e
              | Except.ok tail => Except.ok ({ value := bytesToGF16ListTotal bs } :: tail)) = _
            simp only [hodd_bool, Bool.false_eq_true, ↓reduceIte, hdec_err]
          have hst_eq :
              M.stepEvents (encoderFromPbPtsLoopEvents (bs' :: rest')) st1 =
                M.stepEvents (encoderFromPbPtsLoopEvents (bs :: bs' :: rest')) st := by
            dsimp only [st1]
            rw [← M.stepEvents_append, ← hevs_even]
          rw [← hj_addr2, hst_eq]
          refine SepWPp.weaken_pre
            (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by sep_ac_rfl))
            (hcont_err sm errPts hdec_cons herr_len
              hpcm hrunm hspm (hx1m.trans (hx1_2.trans hx26_1))
              (hx29m.trans (hx29_2.trans hx29_1)) htrm hacpm hvregsm)

end LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoopPlacedBudget
