/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Loop
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common

/-!
# `<PolyEncoder>::into_pb`: Budget-Threaded Placed Inner Loops

Placed inner `GF16` serialization loops (`polys_inner_loop_placed` and `points_inner_loop_placed`)
for Block `375`, preserving `VmPreserved` and `AllocCallPreserved`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.LoopBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_375 blkPl_375)
open CryptoVerification.LibsignalSpqrV1 (GF16 u16ToBeBytes)
open CryptoVerification.RustHeap (arrayAt arrayAt_cons)
open CryptoVerification.SpqrV1.Poly (gf16At)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (
  bne_one_of_pos length_u16ToBeBytes memRegion_two_cons ofNat_succ_sub_one
  off_add_two pointsTo16_rev16_eq_u16ToBeBytes rem_bytes_not_ule_one
  serializeGF16List serializeGF16List_cons
)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)

private theorem sepWP_map_post {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post1 post2 : State → SepProp → Prop}
    (h : SepWP prog target s P post1)
    (hmap : ∀ sm Pm, post1 sm Pm → post2 sm Pm) :
    SepWP prog target s P post2 :=
  SepWP.seq h fun _ _ hpc hrun hp => SepWP.done hpc hrun (hmap _ _ hp)

private theorem trans_vm_post {prog : Program} {target : BitVec 64} {s0 s1 : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hvm01 : VmPreserved s0 s1)
    (h : SepWP prog target s1 P (fun sm Pm => VmPreserved s1 sm ∧ post sm Pm)) :
    SepWP prog target s1 P (fun sm Pm => VmPreserved s0 sm ∧ post sm Pm) :=
  SepWP.seq h fun _ _ hpc hrun ⟨hvm1m, hp⟩ => SepWP.done hpc hrun ⟨hvm01.trans hvm1m, hp⟩

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s : State} {tp : BitVec 64}
    {P P_mid : SepProp} {Q : State → Prop}
    (hent : P ⊢ P_mid)
    (hwp : SepWP prog target s P_mid (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.weaken_pre hent hwp

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

section Placed

variable [LibsignalPlacement]

theorem polys_inner_loop_placed {ext : String → Option (State → State)}
    (s0 : State) (fsp dstPtr : BitVec 64)
    (total : Nat) (hmax : 2 * total < 2 ^ 63)
    (rem : List GF16) (hne : rem ≠ [])
    (done : Nat) (htot : done + rem.length = total)
    (s : State) (srcCur lenVal : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 240#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx0 : s.readReg64 .x0 = dstPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * done))
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 .x28 = srcCur)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      ((blkPl_375).base + 336#64)
      s
      (arrayAt gf16At 2 srcCur rem ∗
        memRegion (dstPtr + BitVec.ofNat 64 (2 * done)) (2 * rem.length) ∗
        ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
        ((fsp + 120#64) ↦₆₄ lenVal) ∗
        Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ arrayAt gf16At 2 srcCur rem ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List rem) ∗
          ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧
        sm.trace = s0.trace ∧
        AllocCallPreserved s0 sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  induction rem generalizing s done srcCur lenVal Frame with
  | nil => exact (hne rfl).elim
  | cons g rem' ih =>
    have htot' : done + (rem'.length + 1) = total := by
      simpa [List.length_cons] using htot
    have hrem_bound : 2 * (rem'.length + 1) < 2 ^ 63 := by omega
    have hnot_ule : BitVec.ule (BitVec.ofNat 64 (2 * total) - BitVec.ofNat 64 (2 * done)) 1#64 = false :=
      rem_bytes_not_ule_one htot' hmax
    nth_rw 1 [arrayAt_cons]
    nth_rw 1 [List.length_cons]
    rw [memRegion_two_cons dstPtr done rem'.length hrem_bound]
    dsimp only [gf16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro v16
    refine seq_vm_clean (mid := (blkPl_375).base + 272#64)
      (P_mid :=
        arrayAt gf16At 2 srcCur (g :: rem') ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
          memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * rem'.length) ∗
          ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 120#64) ↦₆₄ lenVal) ∗
          Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x0 = dstPtr ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
        sm.readReg64 .x27 = BitVec.ofNat 64 (rem'.length + 1) ∧
        sm.readReg64 .x28 = srcCur + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧
        sm.trace = s0.trace ∧
        AllocCallPreserved s0 sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · rcases hacp with ⟨hfs, _, hsig, htp, hbrk0, horacle, hsymtab⟩
      by_vm_steps (
        wp_steps
        rw [off_add_two done]
        refine align_pre_vm (Entails.of_eq ?_) ?_
        · rw [pointsTo16_rev16_eq_u16ToBeBytes, arrayAt_cons]
          dsimp only [gf16At]
          sep_ac_rfl
        · dsimp only [AllocCallPreserved]
          wp_done
      )
    · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, hx29_1, hx0_1, hx1_1, hx27_1, hx28_1,
        hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, htrace1, hacp1, hvregs1⟩
      cases rem' with
      | nil =>
        have hdone_tot : 2 * (done + 1) = 2 * total := by simp at htot'; omega
        rw [hdone_tot] at hx1_1
        simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, memRegion_zero, sepConj_emp] at hx27_1 ⊢
        apply trans_vm_post hvm1
        rcases hacp1 with ⟨hfs1, _, hsig1, htp1, hbrk0_1, horacle1, hsymtab1⟩
        by_vm_steps (
          wp_steps
          have hser1 : serializeGF16List [g] = u16ToBeBytes g.value := by
            simp [serializeGF16List]
          rw [hser1]
          dsimp only [AllocCallPreserved]
          wp_done
        )
      | cons g2 rem'' =>
        have hne' : g2 :: rem'' ≠ [] := List.cons_ne_nil g2 rem''
        have hpos' : 0 < (g2 :: rem'').length := by simp
        have hlt' : (g2 :: rem'').length + 1 < 2 ^ 64 := by simp at htot'; omega
        have hsubs_ne : (BitVec.ofNat 64 ((g2 :: rem'').length + 1) != 1#64) = true :=
          bne_one_of_pos hpos' hlt'
        refine seq_vm_clean (mid := (blkPl_375).base + 240#64)
          (P_mid :=
            arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') ∗
              memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * (g2 :: rem'').length) ∗
              ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
              ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * (done + 1))) ∗
              ((srcCur ↦₁₆ g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                Frame))
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 128#64 ∧
            sm.readReg64 .x0 = dstPtr ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
            sm.readReg64 .x27 = BitVec.ofNat 64 (g2 :: rem'').length ∧
            sm.readReg64 .x28 = srcCur + 2#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x25 = s0.readReg64 .x25 ∧
            sm.readReg64 .x26 = s0.readReg64 .x26 ∧
            sm.trace = s0.trace ∧
            AllocCallPreserved s0 sm ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · rcases hacp1 with ⟨hfs1, _, hsig1, htp1, hbrk0_1, horacle1, hsymtab1⟩
          by_vm_steps (
            nth_rw 1 [arrayAt_cons]
            dsimp only [gf16At]
            wp_steps
            rw [ofNat_succ_sub_one (g2 :: rem'').length]
            refine align_pre_vm (Entails.of_eq (by sep_ac_rfl)) ?_
            dsimp only [AllocCallPreserved]
            wp_done
          )
        · intro s2 hpc2 hrun2 hvm2 ⟨hsp2, hx29_2, hx0_2, hx1_2, hx27_2, hx28_2,
            hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, htrace2, hacp2, hvregs2⟩
          have hih := ih hne' (done + 1) (by omega) s2 (srcCur + 2#64)
            (BitVec.ofNat 64 (2 * (done + 1)))
            ((srcCur ↦₁₆ g.value) ∗
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
              Frame)
            hpc2 hrun2 hsp2 hx29_2 hx0_2 hx1_2 hx27_2 hx28_2
            hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 htrace2 hacp2 hvregs2
          have hcomb :
              arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') ∗
                ((dstPtr + BitVec.ofNat 64 (2 * (done + 1))) ↦ₛ serializeGF16List (g2 :: rem'')) ∗
                ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
                ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
                ((srcCur ↦₁₆ g.value) ∗
                  ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                  Frame) ⊢
              arrayAt gf16At 2 srcCur (g :: g2 :: rem'') ∗
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List (g :: g2 :: rem'')) ∗
                ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
                ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
                Frame := by
            have harr : arrayAt gf16At 2 srcCur (g :: g2 :: rem'') =
                (srcCur ↦₁₆ g.value) ∗ arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') :=
              arrayAt_cons gf16At 2 srcCur g (g2 :: rem'')
            have hser : ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List (g :: g2 :: rem'')) =
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                  ((dstPtr + BitVec.ofNat 64 (2 * (done + 1))) ↦ₛ serializeGF16List (g2 :: rem'')) := by
              rw [serializeGF16List_cons]
              exact pointsToBytes_append_off dstPtr (2 * done) (2 * (done + 1))
                (u16ToBeBytes g.value) (serializeGF16List (g2 :: rem''))
                (by simp [length_u16ToBeBytes]; omega)
            rw [harr, hser]
            exact Entails.of_eq (by sep_ac_rfl)
          exact sepWP_map_post hih fun sm Pm ⟨hvm_2_sm, hent, hrest⟩ =>
            ⟨hvm1.trans (hvm2.trans hvm_2_sm), Entails.trans hent hcomb, hrest⟩

theorem points_inner_loop_placed {ext : String → Option (State → State)}
    (s0 : State) (fsp dstPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (total : Nat) (hmax : 2 * total < 2 ^ 63)
    (rem : List GF16) (hne : rem ≠ [])
    (done : Nat) (htot : done + rem.length = total)
    (s : State) (srcCur lenVal : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 504#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx0 : s.readReg64 .x0 = dstPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * done))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 rem.length)
    (hx21 : s.readReg64 .x21 = srcCur)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      ((blkPl_375).base + 588#64)
      s
      (arrayAt gf16At 2 srcCur rem ∗
        memRegion (dstPtr + BitVec.ofNat 64 (2 * done)) (2 * rem.length) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
        ((fsp + 72#64) ↦₆₄ lenVal) ∗
        Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ arrayAt gf16At 2 srcCur rem ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List rem) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        AllocCallPreserved s0 sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  induction rem generalizing s done srcCur lenVal Frame with
  | nil => exact (hne rfl).elim
  | cons g rem' ih =>
    have htot' : done + (rem'.length + 1) = total := by
      simpa [List.length_cons] using htot
    have hrem_bound : 2 * (rem'.length + 1) < 2 ^ 63 := by omega
    have hnot_ule : BitVec.ule (BitVec.ofNat 64 (2 * total) - BitVec.ofNat 64 (2 * done)) 1#64 = false :=
      rem_bytes_not_ule_one htot' hmax
    nth_rw 1 [arrayAt_cons]
    nth_rw 1 [List.length_cons]
    rw [memRegion_two_cons dstPtr done rem'.length hrem_bound]
    dsimp only [gf16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro v16
    refine seq_vm_clean (mid := (blkPl_375).base + 536#64)
      (P_mid :=
        arrayAt gf16At 2 srcCur (g :: rem') ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
          memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * rem'.length) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 72#64) ↦₆₄ lenVal) ∗
          Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x0 = dstPtr ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
        sm.readReg64 .x26 = BitVec.ofNat 64 (rem'.length + 1) ∧
        sm.readReg64 .x21 = srcCur + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        AllocCallPreserved s0 sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · rcases hacp with ⟨hfs, _, hsig, htp, hbrk0, horacle, hsymtab⟩
      by_vm_steps (
        wp_steps
        rw [off_add_two done]
        refine align_pre_vm (Entails.of_eq ?_) ?_
        · rw [pointsTo16_rev16_eq_u16ToBeBytes, arrayAt_cons]
          dsimp only [gf16At]
          sep_ac_rfl
        · dsimp only [AllocCallPreserved]
          wp_done
      )
    · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, hx29_1, hx0_1, hx1_1, hx26_1, hx21_1,
        hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx28_1, htrace1, hacp1, hvregs1⟩
      cases rem' with
      | nil =>
        have hdone_tot : 2 * (done + 1) = 2 * total := by simp at htot'; omega
        rw [hdone_tot] at hx1_1
        simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, memRegion_zero, sepConj_emp] at hx26_1 ⊢
        apply trans_vm_post hvm1
        rcases hacp1 with ⟨hfs1, _, hsig1, htp1, hbrk0_1, horacle1, hsymtab1⟩
        by_vm_steps (
          wp_steps
          have hser1 : serializeGF16List [g] = u16ToBeBytes g.value := by
            simp [serializeGF16List]
          rw [hser1]
          dsimp only [AllocCallPreserved]
          wp_done
        )
      | cons g2 rem'' =>
        have hne' : g2 :: rem'' ≠ [] := List.cons_ne_nil g2 rem''
        have hpos' : 0 < (g2 :: rem'').length := by simp
        have hlt' : (g2 :: rem'').length + 1 < 2 ^ 64 := by simp at htot'; omega
        have hsubs_ne : (BitVec.ofNat 64 ((g2 :: rem'').length + 1) != 1#64) = true :=
          bne_one_of_pos hpos' hlt'
        refine seq_vm_clean (mid := (blkPl_375).base + 504#64)
          (P_mid :=
            arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') ∗
              memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * (g2 :: rem'').length) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
              ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (2 * (done + 1))) ∗
              ((srcCur ↦₁₆ g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                Frame))
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 128#64 ∧
            sm.readReg64 .x0 = dstPtr ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
            sm.readReg64 .x26 = BitVec.ofNat 64 (g2 :: rem'').length ∧
            sm.readReg64 .x21 = srcCur + 2#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x25 = s0.readReg64 .x25 ∧
            sm.readReg64 .x28 = s0.readReg64 .x28 ∧
            sm.trace = s0.trace ∧
            AllocCallPreserved s0 sm ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · rcases hacp1 with ⟨hfs1, _, hsig1, htp1, hbrk0_1, horacle1, hsymtab1⟩
          by_vm_steps (
            nth_rw 1 [arrayAt_cons]
            dsimp only [gf16At]
            wp_steps
            rw [ofNat_succ_sub_one (g2 :: rem'').length]
            refine align_pre_vm (Entails.of_eq (by sep_ac_rfl)) ?_
            dsimp only [AllocCallPreserved]
            wp_done
          )
        · intro s2 hpc2 hrun2 hvm2 ⟨hsp2, hx29_2, hx0_2, hx1_2, hx26_2, hx21_2,
            hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx28_2, htrace2, hacp2, hvregs2⟩
          have hih := ih hne' (done + 1) (by omega) s2 (srcCur + 2#64)
            (BitVec.ofNat 64 (2 * (done + 1)))
            ((srcCur ↦₁₆ g.value) ∗
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
              Frame)
            hpc2 hrun2 hsp2 hx29_2 hx0_2 hx1_2 hx26_2 hx21_2
            hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx28_2 htrace2 hacp2 hvregs2
          have hcomb :
              arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') ∗
                ((dstPtr + BitVec.ofNat 64 (2 * (done + 1))) ↦ₛ serializeGF16List (g2 :: rem'')) ∗
                ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
                ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
                ((srcCur ↦₁₆ g.value) ∗
                  ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                  Frame) ⊢
              arrayAt gf16At 2 srcCur (g :: g2 :: rem'') ∗
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List (g :: g2 :: rem'')) ∗
                ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
                ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
                Frame := by
            have harr : arrayAt gf16At 2 srcCur (g :: g2 :: rem'') =
                (srcCur ↦₁₆ g.value) ∗ arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') :=
              arrayAt_cons gf16At 2 srcCur g (g2 :: rem'')
            have hser : ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List (g :: g2 :: rem'')) =
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                  ((dstPtr + BitVec.ofNat 64 (2 * (done + 1))) ↦ₛ serializeGF16List (g2 :: rem'')) := by
              rw [serializeGF16List_cons]
              exact pointsToBytes_append_off dstPtr (2 * done) (2 * (done + 1))
                (u16ToBeBytes g.value) (serializeGF16List (g2 :: rem''))
                (by simp [length_u16ToBeBytes]; omega)
            rw [harr, hser]
            exact Entails.of_eq (by sep_ac_rfl)
          exact sepWP_map_post hih fun sm Pm ⟨hvm_2_sm, hent, hrest⟩ =>
            ⟨hvm1.trans (hvm2.trans hvm_2_sm), Entails.trans hent hcomb, hrest⟩

end Placed

end LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.LoopBudget
