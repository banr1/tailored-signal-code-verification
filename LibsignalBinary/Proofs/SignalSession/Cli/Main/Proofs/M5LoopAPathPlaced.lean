/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopATailPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable M5 Inner Loop A Path Builder (`M+0x8fc .. M+0x980`, Block `617`)

Verifies `m5_loop_a_build_path_placed` on Block `617` under `[LibsignalPlacement]`, allocating and
assembling `"<dir>/<name>"` (`pathOf dir name`) for non-empty `Dir.path`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.LoopDrop

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint DoReserveNorm
open CryptoVerification.SignalSession.Cli.Path.Helpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem off_m32_eq (base : BitVec 64) :
    (base + 40#64) + (-32#64) = base + 8#64 := by bv_omega

private theorem fsp_fp_add_neg24_a (fsp : BitVec 64) :
    (fsp + 0x480#64) + (-24#64) = fsp + 0x468#64 := by bv_omega

theorem m5_reg_a_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (hstep : SepWP prog mid s emp
      (fun sm Pm => sm.pc = mid → sm.status = .Running → CodeOk sm.mem →
        SepWPp prog ret sm (Pm ∗ P) Q Qp oom)
      (fun _ => ⌜False⌝)) :
    SepWPp prog ret s P Q Qp oom :=
  m5_run_placed hinv (by rw [emp_sepConj]; exact Entails.refl _) hstep

set_option maxHeartbeats 1600000 in
/-- Execute `M+0x8fc .. M+0x97c` (plus `M+0x9b8 .. M+0x9d8` on reserve grow and `M+0xbb4` on OOM),
producing `ownedBytes A capFinal ptrFinal (BitVec.ofNat 64 (pathOf dir name).length) (pathOf dir name)`
at `M+0x980` while preserving `(dPathPtr ↦ᵣ dir)`, `(p1 ↦ₛ name)`, `[fsp + 0x40] = dPathPtr`,
`[fsp + 0x58] = v58`, and all outer loop callee-saved registers (`x19`, `x20`, `x24`, `x26`, `x27`, `x28`). -/
theorem m5_loop_a_build_path_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack stk : Nat}
    {base dPathPtr c1 p1 v48 v58 v458 v460 v468 : BitVec 64}
    {dir name : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hs0tr : s0.trace = [])
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_res : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hd_ne : dir ≠ [])
    (hpath_lt : (pathOf dir name).length < 2 ^ 32)
    (hs : InMainPlaced CodeOk s0 s 0x8fc)
    (hx27 : s.readReg64 (.gpr 27#5) = base + 40#64)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length)
    (hP : P ⊢ vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x40#64) ↦₆₄ dPathPtr) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x48#64) ↦₆₄ v48) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x58#64) ↦₆₄ v58) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x458#64) ↦₆₄ v458) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x460#64) ↦₆₄ v460) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x468#64) ↦₆₄ v468) ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      A.pool ∗ F)
    (hnext : ∀ (sm : State) (capFinal ptrFinal v458' v460' v468' : BitVec 64),
      0 < capFinal.toNat →
      (pathOf dir name).length ≤ capFinal.toNat →
      capFinal.toNat < 2 ^ 63 →
      ptrFinal ≠ 0#64 →
      InMainPlaced CodeOk s0 sm 0x980 →
      sm.fs = s.fs →
      sm.trace = s.trace →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length →
      sm.readReg64 (.gpr 22#5) = ptrFinal →
      sm.readReg64 (.gpr 23#5) = capFinal →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (dir.length + 1) →
      sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sm.readReg64 (.gpr 27#5) = base + 40#64 →
      sm.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (ownedBytes A capFinal ptrFinal (BitVec.ofNat 64 (pathOf dir name).length)
            (pathOf dir name) ∗
          vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
          (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x40#64) ↦₆₄ dPathPtr) ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x48#64) ↦₆₄ p1) ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x58#64) ↦₆₄ v58) ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x458#64) ↦₆₄ v458') ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x460#64) ↦₆₄ v460') ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x468#64) ↦₆₄ v468') ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hp_eq := pathOf_ne_nil hd_ne name
  have hp_len : (pathOf dir name).length = dir.length + 1 + name.length := by rw [hp_eq]; simp; omega
  have hd_pos : 0 < dir.length := List.length_pos_of_ne_nil hd_ne
  have hd_lt : dir.length < 2 ^ 32 := by m5_omega
  have hname_lt : name.length < 2 ^ 32 := by m5_omega
  have hd_toNat : (BitVec.ofNat 64 dir.length).toNat = dir.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
  have hlay0 : LayoutOk dir.length 1 := ⟨hd_pos, ⟨0, rfl⟩, by m5_omega⟩
  have off_m32 : (base + 40#64) + (-32#64) = base + 8#64 := off_m32_eq base
  have off_fp40 : (s0.sp - 0x60#64) - 40#64 = fsp + 0x458#64 := by
    rw [fp_eq_fsp_add s0]; exact fsp_fp_sub_40 fsp
  have off_fp40_add : (s0.sp - 0x60#64) + (-40#64) = fsp + 0x458#64 := by
    rw [← BitVec.sub_eq_add_neg]; exact off_fp40
  have off_fp24 : (s0.sp - 0x60#64) + (-24#64) = fsp + 0x468#64 := by
    rw [fp_eq_fsp_add s0]; exact fsp_fp_add_neg24_a fsp
  have off_hdr1 :
      vecHeader base c1 p1 (BitVec.ofNat 64 name.length) =
        (base ↦₆₄ c1) ∗ ((base + 8#64) ↦₆₄ p1) ∗ (((base + 8#64) + 8#64) ↦₆₄ BitVec.ofNat 64 name.length) := by
    unfold vecHeader
    have hb : base + 16#64 = (base + 8#64) + 8#64 := by simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [hb]
  refine SepWPp.weaken_pre hP ?_
  have hpc := hs.pc; have hrun := hs.run
  refine m5_run_placed hs.inv (mid := lsρ lsRustNoAllocShimSymCli)
    (P0 := ((base + 8#64) ↦₆₄ p1) ∗ (((base + 8#64) + 8#64) ↦₆₄ BitVec.ofNat 64 name.length) ∗
      ((s.sp + 0x48#64) ↦₆₄ v48))
    (F := (base ↦₆₄ c1) ∗ (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468) ∗
      stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ F)
    (by rw [off_hdr1, hs.sp]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)) ?_
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, hpc, hx27, off_m32, hs.sp, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd]; try m5_bv_omega)
    (by simp only [arm64_norm, hrun])
  intro hpcm1 hrunm1 hinv_m1
  refine m5_call_shim_placed hA hstk_ext hstk64 hpcm1 hrunm1 hinv_m1
    (by simp only [arm64_norm, hs.sp]) (by simp only [arm64_norm, hs.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs.vregs]) hs.spAligned
    (retOff := 0x908) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd])
    (F := vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468) ∗
      A.pool ∗ F)
    (by rw [off_hdr1, hs.sp]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)) ?_
  intro s1 hs1 hfs1 htr1 hcsm1
  have hpc1 := hs1.pc; have hrun1 := hs1.run
  have r21_1 : s1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length := by
    simp only [hcsm1.2.2.1, arm64_norm]
  have r27_1 : s1.readReg64 (.gpr 27#5) = base + 40#64 :=
    hcsm1.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx27])
  have r28_1 : s1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length :=
    hcsm1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx28])
  apply m5_reg_a_placed hs1.inv (mid := lsρ lsRustAllocSymCli)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, hpc1, r28_1, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd]; try m5_bv_omega)
    (by simp only [arm64_norm, hrun1])
  intro hpcm2 hrunm2 hinv_m2; rw [emp_sepConj]
  refine m5_call_alloc_placed hA hs0tr hstk_ext hstk64 hlay0 hpcm2 hrunm2 hinv_m2
    (by simp only [arm64_norm, hs1.sp]) (by simp only [arm64_norm, hs1.fp])
    (by simp only [calleeSavedVRegs, arm64_norm, hs1.vregs]) hs1.spAligned
    (retOff := 0x914) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [arm64_norm, r28_1, hd_toNat]) (by simp only [arm64_norm]; try rfl)
    (F := vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468) ∗
      F)
    (Entails.of_eq (by ac_rfl)) ?_ ?_
  · intro s2 hs2 hx0_2 haf2
    have hpc2 := hs2.pc; have hrun2 := hs2.run
    apply m5_reg_a_placed hs2.inv (mid := mPcPlaced 0xbb4)
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, hpc2, hx0_2, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd]; try m5_bv_omega)
      (by simp only [arm64_norm, hrun2])
    intro hpcm3 hrunm3 hinv_m3; rw [emp_sepConj]
    have hs_bb4 := hs2.mk_step (by simpa only [mPcPlaced_eq_blkPl] using hpcm3) hrunm3
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      hinv_m3 (by simp only [calleeSavedVRegs, arm64_norm])
    exact m5_oom_bb4_placed (v58 := v58)
      (F := A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
        ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468) ∗
        F)
      hc hpanic hs0tr hs_bb4
      (by rw [hs_bb4.sp]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl))
      (allocFailedIn_of_prefix haf2 (by simp only [arm64_norm]; exact List.prefix_refl _))
  · intro s2 hs2 hptr0_ne hfs2 htr2 hcsm2
    let ptr0 := s2.readReg64 .x0
    have hptr0_beq : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hptr0_ne
    have hpc2 := hs2.pc; have hrun2 := hs2.run
    have r21_2 : s2.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length :=
      hcsm2.2.2.1.trans (by simp only [arm64_norm, r21_1])
    have r27_2 : s2.readReg64 (.gpr 27#5) = base + 40#64 :=
      hcsm2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r27_1])
    have r28_2 : s2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length :=
      hcsm2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r28_1])
    refine m5_run_placed hs2.inv (mid := lsρ memcpyName)
      (P0 := (s2.sp + 0x40#64) ↦₆₄ dPathPtr)
      (F := A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
        A.live ptr0 dir.length 1 ∗ memRegion ptr0 dir.length ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
        ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468) ∗
        F)
      (by rw [hs2.sp]; dsimp only [fsp, ptr0]; exact Entails.of_eq (by ac_rfl)) ?_
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, hpc2, hptr0_beq, hs2.sp, r28_2, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd]; try m5_bv_omega)
      (by simp only [arm64_norm, hrun2])
    intro hpcm3 hrunm3 hinv_m3
    refine m5_call_memcpy_ro_placed (MainMemcpyROFsPlaced.of_alloc hA) hstk_ext hstk64 hpcm3 hrunm3 hinv_m3
      (by simp only [arm64_norm, hs2.sp]) (by simp only [arm64_norm, hs2.fp])
      (by simp only [calleeSavedVRegs, arm64_norm, hs2.vregs]) hs2.spAligned
      (retOff := 0x928) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd])
      (dst := ptr0) (src := dPathPtr) (bs := dir)
      (by simp only [arm64_norm]; try rfl) (by simp only [arm64_norm])
      (by simp only [arm64_norm, r28_2, hd_toNat]) (by m5_omega)
      (F := A.pool ∗ A.live ptr0 dir.length 1 ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (p1 ↦ₛ name) ∗ ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
        ((fsp + 0x58#64) ↦₆₄ v58) ∗
        ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468) ∗
        F)
      (by rw [hs2.sp]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)) ?_
    intro s3 hs3 hfs3 htr3 hcsm3
    have hpc3 := hs3.pc; have hrun3 := hs3.run
    have r21_3 : s3.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length :=
      hcsm3.2.2.1.trans (by simp only [arm64_norm, r21_2])
    have r22_3 : s3.readReg64 (.gpr 22#5) = ptr0 :=
      hcsm3.2.2.2.1.trans (by simp only [arm64_norm]; try rfl)
    have r27_3 : s3.readReg64 (.gpr 27#5) = base + 40#64 :=
      hcsm3.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r27_2])
    have r28_3 : s3.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length :=
      hcsm3.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r28_2])
    have hcap0_ne : BitVec.ofNat 64 dir.length ≠ 0#64 := ofNat_ne_zero hd_pos (by m5_omega)
    have hrest0 :
        A.live ptr0 dir.length 1 ∗ (ptr0 ↦ₛ dir) =
          vecU8RestAt A (BitVec.ofNat 64 dir.length) ptr0 dir := by
      simp only [vecU8RestAt, BitVec.ofNat_eq_ofNat, hcap0_ne, ↓reduceIte, hd_toNat,
        Nat.sub_self, memRegion_zero, sepConj_emp]
    refine m5_run_placed hs3.inv (mid := lsmpl.base 561)
      (P0 := ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468))
      (F := vecU8RestAt A (BitVec.ofNat 64 dir.length) ptr0 dir ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗ F)
      (by rw [← hrest0]; exact Entails.of_eq (by ac_rfl)) ?_
    have hfp3 := hs3.fp
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, hpc3, hfp3, r28_3, r22_3, off_fp40, off_fp40_add, off_fp24, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd]; try m5_bv_omega)
      (by simp only [arm64_norm, hrun3])
    intro hpcm4 hrunm4 hinv_m4
    have hbound1 : reserveCap (BitVec.ofNat 64 dir.length).toNat dir.length 1 + 1 ≤ 2 ^ 63 := by
      simp only [reserveCap, hd_toNat]; m5_omega
    have hvec0 :
        ((fsp + 0x458#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
          ((fsp + 0x460#64) ↦₆₄ ptr0) ∗
          ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
          vecU8RestAt A (BitVec.ofNat 64 dir.length) ptr0 dir =
        vecU8At A (fsp + 0x458#64) (BitVec.ofNat 64 dir.length) ptr0 dir := by
      have h0 := vecU8At_of_header_rest A (fsp + 0x458#64) (BitVec.ofNat 64 dir.length) ptr0 dir
        (by rw [hd_toNat]) (by rw [hd_toNat]; m5_omega) hptr0_ne
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h0
    refine m5_call_reserve1_placed hc hs0tr hpanic hstk_res hstk64 hbound1 hpcm4 hrunm4 hinv_m4
      (by simp only [arm64_norm, hs3.sp]) (by simp only [arm64_norm, hfp3])
      (by simp only [calleeSavedVRegs, arm64_norm, hs3.vregs]) hs3.spAligned
      (retOff := 0x948) (by simp only [arm64_norm, mPcPlaced_eq_blkPl, BitVec.add_assoc, BitVec.reduceAdd])
      (v := fsp + 0x458#64) (curCap := BitVec.ofNat 64 dir.length) (curPtr := ptr0)
      (curBs := dir) (additional := 1)
      (by simp only [arm64_norm, hfp3, off_fp40])
      (by simp only [arm64_norm, r28_3, hd_toNat])
      (by simp only [arm64_norm]; try rfl)
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (F := vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗ F)
      (by rw [← hvec0]; exact Entails.of_eq (by ac_rfl)) ?_
    intro s4 ptr1 hs4 hfs4 htr4 hcsm4
    set cap1 : BitVec 64 := BitVec.ofNat 64 (reserveCap (BitVec.ofNat 64 dir.length).toNat dir.length 1)
    have hcap1_lt34 : cap1.toNat < 2 ^ 34 := by
      simp only [cap1, reserveCap, hd_toNat, BitVec.toNat_ofNat]; m5_omega
    have hcap1_ge : dir.length + 1 ≤ cap1.toNat := by
      have hlt64 : reserveCap dir.length dir.length 1 < 2 ^ 64 := by simp only [reserveCap]; m5_omega
      simp only [cap1, hd_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, reserveCap]; m5_omega
    exact m5_loop_a_slash_and_name_placed (base := base) (dPathPtr := dPathPtr) (c1 := c1) (p1 := p1)
      (cap1 := cap1) (ptr1 := ptr1) (F := ((fsp + 0x58#64) ↦₆₄ v58) ∗ F)
      hA hc hs0tr hpanic hstk_ext hstk_res hstk64
      hd_ne hpath_lt
      hcap1_ge hcap1_lt34 hs4
      (by simp only [hfs4, arm64_norm, hfs3, hfs2, hfs1])
      (by simp only [htr4, arm64_norm, htr3, htr2, htr1])
      (by simp only [hcsm4.1, arm64_norm, hcsm3.1, hcsm2.1, hcsm1.1])
      (by simp only [hcsm4.2.1, arm64_norm, hcsm3.2.1, hcsm2.2.1, hcsm1.2.1])
      (hcsm4.2.2.1.trans (by simp only [arm64_norm, r21_3]))
      (by simp only [hcsm4.2.2.2.2.2.1, arm64_norm, hcsm3.2.2.2.2.2.1, hcsm2.2.2.2.2.2.1, hcsm1.2.2.2.2.2.1])
      (by simp only [hcsm4.2.2.2.2.2.2.2.1, arm64_norm, hcsm3.2.2.2.2.2.2.2.1, hcsm2.2.2.2.2.2.2.2.1, hcsm1.2.2.2.2.2.2.2.1])
      (hcsm4.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r27_3]))
      (hcsm4.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, r28_3]))
      (by dsimp only [fsp]; exact Entails.of_eq (by ac_rfl))
      fun sm capFinal ptrFinal v458' v460' v468'
        hc1 hc2 hc3 hc4 hsm hfs htr h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 =>
        SepWPp.weaken_pre (by dsimp only [fsp]; exact Entails.of_eq (by ac_rfl))
          (hnext sm capFinal ptrFinal v458' v460' v468'
            hc1 hc2 hc3 hc4 hsm hfs htr h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
