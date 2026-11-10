/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable M5 Inner Loop A Slash Push & Name Append (`M+0x948 .. M+0x980`, Block `617`)

Verifies `m5_loop_a_slash_and_name_placed` (`M+0x948 .. M+0x980`, plus `M+0x9b8 .. M+0x9d8` on
reserve growth) appending `'/'` and `name` to the path buffer on Block `617`.
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

private theorem fsp_fp_add_neg32 (fsp : BitVec 64) :
    (fsp + 0x480#64) + (-32#64) = fsp + 0x460#64 := by bv_omega

private theorem fsp_fp_add_neg24 (fsp : BitVec 64) :
    (fsp + 0x480#64) + (-24#64) = fsp + 0x468#64 := by bv_omega

set_option maxHeartbeats 1600000 in
/-- Completes `M+0x948 .. M+0x97c -> M+0x980` (plus `M+0x9b8 .. M+0x9d8` when `name` grows the
buffer) from post-`reserve11(1)` state `s4`. -/
theorem m5_loop_a_slash_and_name_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack stk : Nat}
    {base dPathPtr c1 p1 cap1 ptr1 : BitVec 64}
    {dir name : List (BitVec 8)}
    {s0 s s4 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hs0tr : s0.trace = [])
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hstk_ext : mainFrameSize + extHookStack ≤ stk)
    (hstk_res : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hd_ne : dir ≠ [])
    (hpath_lt : (pathOf dir name).length < 2 ^ 32)
    (hcap1_ge : dir.length + 1 ≤ cap1.toNat)
    (hcap1_lt34 : cap1.toNat < 2 ^ 34)
    (hs4 : InMainPlaced CodeOk s0 s4 0x948)
    (hfs4_s : s4.fs = s.fs)
    (htr4_s : s4.trace = s.trace)
    (r19_4 : s4.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (r20_4 : s4.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (r21_4 : s4.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length)
    (r24_4 : s4.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5))
    (r26_4 : s4.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5))
    (r27_4 : s4.readReg64 (.gpr 27#5) = base + 40#64)
    (r28_4 : s4.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length)
    (hP : P ⊢ vecU8At A ((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x458#64) cap1 ptr1 dir ∗
      A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
      (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x40#64) ↦₆₄ dPathPtr) ∗
      (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x48#64) ↦₆₄ p1) ∗ F)
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
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x458#64) ↦₆₄ v458') ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x460#64) ↦₆₄ v460') ∗
          (((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x468#64) ↦₆₄ v468') ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s4 P Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hp_eq := pathOf_ne_nil hd_ne name
  have hp_len : (pathOf dir name).length = dir.length + 1 + name.length := by rw [hp_eq]; simp; omega
  have hd_lt : dir.length < 2 ^ 32 := by m5_omega
  have hname_lt : name.length < 2 ^ 32 := by m5_omega
  have off_fp40 : (s0.sp - 0x60#64) - 40#64 = fsp + 0x458#64 := by
    rw [fp_eq_fsp_add s0]; exact fsp_fp_sub_40 fsp
  have off_fp40_add : (s0.sp - 0x60#64) + (-40#64) = fsp + 0x458#64 := by
    rw [← BitVec.sub_eq_add_neg]; exact off_fp40
  have off_fp32 : (s0.sp - 0x60#64) + (-32#64) = fsp + 0x460#64 := by
    rw [fp_eq_fsp_add s0]; exact fsp_fp_add_neg32 fsp
  have off_fp24 : (s0.sp - 0x60#64) + (-24#64) = fsp + 0x468#64 := by
    rw [fp_eq_fsp_add s0]; exact fsp_fp_add_neg24 fsp
  refine SepWPp.weaken_pre hP ?_
  rw [vecU8At_eq_header_rest]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hle_v1, hlt_v1, hptr1⟩ => ?_
  have hexp1 :
      ((fsp + 0x458#64) ↦₆₄ cap1) ∗ (((fsp + 0x458#64) + 8#64) ↦₆₄ ptr1) ∗
        (((fsp + 0x458#64) + 16#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A cap1 ptr1 dir =
      ((fsp + 0x458#64) ↦₆₄ cap1) ∗
        ((fsp + 0x460#64) ↦₆₄ ptr1) ∗ ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
        memRegion (ptr1 + BitVec.ofNat 64 dir.length) 1 ∗
        memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
          (cap1.toNat - dir.length - 1) := by
    rw [vecU8At_of_header_rest A (fsp + 0x458#64) cap1 ptr1 dir hle_v1 hlt_v1 hptr1,
      vecU8At_expose_slice A (fsp + 0x458#64) cap1 ptr1 dir 1 hcap1_ge (by m5_omega) hptr1 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hreord_b1 :
      ((fsp + 0x458#64) ↦₆₄ cap1) ∗ (((fsp + 0x458#64) + 8#64) ↦₆₄ ptr1) ∗
        (((fsp + 0x458#64) + 16#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A cap1 ptr1 dir ∗ A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F =
      (((fsp + 0x458#64) ↦₆₄ cap1) ∗ (((fsp + 0x458#64) + 8#64) ↦₆₄ ptr1) ∗
        (((fsp + 0x458#64) + 16#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A cap1 ptr1 dir) ∗
      (A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F) := by ac_rfl
  rw [hreord_b1, hexp1, memRegion_1_eq_pointsTo8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b0 => ?_
  have step_970 : ∀ (sk : State) (cap2 ptr2 v460k v468k : BitVec 64),
      0 < name.length →
      (dir.length + 1) + name.length ≤ cap2.toNat →
      cap2.toNat < 2 ^ 63 →
      ptr2 ≠ 0#64 →
      InMainPlaced CodeOk s0 sk 0x970 →
      sk.fs = s.fs →
      sk.trace = s.trace →
      sk.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sk.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sk.readReg64 (.gpr 21#5) = BitVec.ofNat 64 name.length →
      sk.readReg64 (.gpr 22#5) = ptr2 →
      sk.readReg64 (.gpr 23#5) = cap2 →
      sk.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sk.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (dir.length + 1) →
      sk.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sk.readReg64 (.gpr 27#5) = base + 40#64 →
      sk.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sk
        (((fsp + 0x458#64) ↦₆₄ cap2) ∗ ((fsp + 0x460#64) ↦₆₄ v460k) ∗ ((fsp + 0x468#64) ↦₆₄ v468k) ∗
          vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8]) ∗
          vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
          (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
          ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ F)
        Q Qp (mainOom s0) := by
    intro sk cap2 ptr2 v460k v468k _ hle2 hlt2 hptr2 hsk hfsk htrk
      k19 k20 k21 k22 k23 k24 k25 k26 k27 k28
    have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
    have hlen1 : (dir ++ [0x2f#8]).length = dir.length + 1 := by simp
    have hcap2_ne : cap2 ≠ 0 := by intro h0; subst h0; change _ ≤ 0 at hle2; m5_omega
    have hsplit_rest2 :
        vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8]) =
          A.live ptr2 cap2.toNat 1 ∗ (ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗
            memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1)) name.length ∗
            memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
              (cap2.toNat - (dir.length + 1) - name.length) := by
      simp only [vecU8RestAt, hcap2_ne, ↓reduceIte, hlen1]
      have hsub : cap2.toNat - (dir.length + 1) =
          name.length + (cap2.toNat - (dir.length + 1) - name.length) := by m5_omega
      conv =>
        lhs
        rw [hsub, ProofLib.memRegion_split (ptr2 + BitVec.ofNat 64 (dir.length + 1)) name.length
          (cap2.toNat - (dir.length + 1) - name.length) (by m5_omega)]
    have hpck := hsk.pc; have hrunk := hsk.run
    refine m5_run_placed hsk.inv (mid := lsρ memcpyName)
      (P0 := (sk.sp + 0x48#64) ↦₆₄ p1)
      (F := ((fsp + 0x458#64) ↦₆₄ cap2) ∗ ((fsp + 0x460#64) ↦₆₄ v460k) ∗
        ((fsp + 0x468#64) ↦₆₄ v468k) ∗
        A.live ptr2 cap2.toNat 1 ∗ (ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗
        memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1)) name.length ∗
        memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
          (cap2.toNat - (dir.length + 1) - name.length) ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗ ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ F)
      (by rw [hsplit_rest2, hsk.sp]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)) ?_
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm_c hrunm_c hinv_c
    refine m5_call_memcpy_placed hA hstk_ext hstk64 hpcm_c hrunm_c hinv_c
      (by simp only [arm64_norm, hsk.sp]) (by simp only [arm64_norm, hsk.fp])
      (by simp only [calleeSavedVRegs, arm64_norm, hsk.vregs]) hsk.spAligned
      (retOff := 0x980) (by simp only [arm64_norm, *]; try m5_bv_omega)
      (dst := ptr2 + BitVec.ofNat 64 (dir.length + 1)) (src := p1) (bs := name)
      (by simp only [arm64_norm, k22, k25]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, k21, hname_toNat])
      (F := ((fsp + 0x458#64) ↦₆₄ cap2) ∗ ((fsp + 0x460#64) ↦₆₄ v460k) ∗
        ((fsp + 0x468#64) ↦₆₄ v468k) ∗
        A.live ptr2 cap2.toNat 1 ∗ (ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗
        memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
          (cap2.toNat - (dir.length + 1) - name.length) ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
        A.pool ∗ F)
      (by rw [hsk.sp]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)) ?_
    intro sm hsm hfsm htrm hcsm
    have hrest_full :
        A.live ptr2 cap2.toNat 1 ∗
          ((ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗ ((ptr2 + BitVec.ofNat 64 (dir.length + 1)) ↦ₛ name)) ∗
          memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
            (cap2.toNat - (dir.length + 1) - name.length) ⊢
        ownedBytes A cap2 ptr2 (BitVec.ofNat 64 (pathOf dir name).length) (pathOf dir name) := by
      have happ := pointsToBytes_append ptr2 (dir ++ [0x2f#8]) name
      rw [hlen1] at happ
      have hbv_len :
          ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length =
            ptr2 + BitVec.ofNat 64 (pathOf dir name).length := by
        rw [hp_len, BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [← happ, ← hp_eq, hbv_len]
      have heq_rest :
          A.live ptr2 cap2.toNat 1 ∗ (ptr2 ↦ₛ pathOf dir name) ∗
            memRegion (ptr2 + BitVec.ofNat 64 (pathOf dir name).length)
              (cap2.toNat - (dir.length + 1) - name.length) =
          vecU8RestAt A cap2 ptr2 (pathOf dir name) := by
        simp only [vecU8RestAt, hcap2_ne, ↓reduceIte, hp_len, Nat.sub_sub]
      rw [heq_rest]
      exact ownedBytes_of_vecU8RestAt A cap2 ptr2 (pathOf dir name)
        (by rw [hp_len]; m5_omega) hlt2 hptr2
    refine SepWPp.weaken_pre ?_
      (hnext sm cap2 ptr2 cap2 v460k v468k
        (by m5_omega) (by rw [hp_len]; m5_omega) hlt2 hptr2 hsm
        (hfsm.trans (by simp only [arm64_norm, hfsk]))
        (htrm.trans (by simp only [arm64_norm, htrk]))
        (hcsm.1.trans (by simp only [arm64_norm, k19]))
        (hcsm.2.1.trans (by simp only [arm64_norm, k20]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, k21]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, k22]))
        (hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, k23]))
        (hcsm.2.2.2.2.2.1.trans (by simp only [arm64_norm, k24]))
        (hcsm.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, k25]))
        (hcsm.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, k26]))
        (hcsm.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, k27]))
        (hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, k28])))
    have hord :
        ((ptr2 + BitVec.ofNat 64 (dir.length + 1)) ↦ₛ name) ∗ (p1 ↦ₛ name) ∗
          stackAt fsp (stk - mainFrameSize) ∗
          (((fsp + 0x458#64) ↦₆₄ cap2) ∗ ((fsp + 0x460#64) ↦₆₄ v460k) ∗
            ((fsp + 0x468#64) ↦₆₄ v468k) ∗
            A.live ptr2 cap2.toNat 1 ∗ (ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗
            memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
              (cap2.toNat - (dir.length + 1) - name.length) ∗
            vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
            (dPathPtr ↦ᵣ dir) ∗ ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
            A.pool ∗ F) =
        (A.live ptr2 cap2.toNat 1 ∗
          ((ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗ ((ptr2 + BitVec.ofNat 64 (dir.length + 1)) ↦ₛ name)) ∗
          memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
            (cap2.toNat - (dir.length + 1) - name.length)) ∗
        (vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
          (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
          ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
          ((fsp + 0x458#64) ↦₆₄ cap2) ∗ ((fsp + 0x460#64) ↦₆₄ v460k) ∗
          ((fsp + 0x468#64) ↦₆₄ v468k) ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ F) := by ac_rfl
    rw [hord]
    exact sepConj_mono_left hrest_full
  have hpc4 := hs4.pc; have hrun4 := hs4.run; have hfp4 := hs4.fp
  have hadd1 : BitVec.ofNat 64 dir.length + 1#64 = BitVec.ofNat 64 (dir.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hpack_slash :
      ((fsp + 0x458#64) ↦₆₄ cap1) ∗ ((fsp + 0x460#64) ↦₆₄ ptr1) ∗
        ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)) ∗
        A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
        ((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ 0x2f#8) ∗
        memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
          (cap1.toNat - dir.length - 1) =
      vecU8At A (fsp + 0x458#64) cap1 ptr1 (dir ++ [0x2f#8]) := by
    have hp1 := vecU8At_pack_slice A (fsp + 0x458#64) cap1 ptr1 dir [0x2f#8]
      (by simpa using hcap1_ge) (by m5_omega) hptr1 (by decide)
    rw [pointsTo8_eq_singleton]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, List.length_singleton, hadd1] using hp1
  have hult_iff := elem_len_ult_spare_iff (cap := cap1) (bsLen := dir.length + 1)
    (elemLen := name.length) hcap1_ge (by m5_omega) (by m5_omega)
  by_cases hgrow : (cap1 - BitVec.ofNat 64 (dir.length + 1)).ult (BitVec.ofNat 64 name.length) = true
  · have hlt_cap : cap1.toNat < (dir.length + 1) + name.length := hult_iff.mp hgrow
    have hnpos : 0 < name.length := by m5_omega
    have hlen1_toNat : (BitVec.ofNat 64 (dir.length + 1)).toNat = dir.length + 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
    have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by m5_omega)]
    refine m5_run_placed hs4.inv (mid := lsmpl.base 561)
      (P0 := ((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ b0) ∗
        ((fsp + 0x458#64) ↦₆₄ cap1) ∗
        ((fsp + 0x460#64) ↦₆₄ ptr1) ∗ ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 dir.length))
      (F := A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
        memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
          (cap1.toNat - dir.length - 1) ∗
        A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F)
      (Entails.of_eq (by ac_rfl)) ?_
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, *, hadd1]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm5 hrunm5 hinv_m5
    have hlen1 : (dir ++ [0x2f#8]).length = dir.length + 1 := by simp
    have hbound2 : reserveCap cap1.toNat (dir ++ [0x2f#8]).length name.length + 1 ≤ 2 ^ 63 := by
      simp only [reserveCap, hlen1]; m5_omega
    refine m5_call_reserve1_placed hc hs0tr hpanic hstk_res hstk64 hbound2 hpcm5 hrunm5 hinv_m5
      (by simp only [arm64_norm, hs4.sp]) (by simp only [arm64_norm, hfp4])
      (by simp only [calleeSavedVRegs, arm64_norm, hs4.vregs]) hs4.spAligned
      (retOff := 0x9d0) (by simp only [arm64_norm, *]; try m5_bv_omega)
      (v := fsp + 0x458#64) (curCap := cap1) (curPtr := ptr1)
      (curBs := dir ++ [0x2f#8]) (additional := name.length)
      (by simp only [arm64_norm, hfp4, off_fp40])
      (by simp only [arm64_norm, hlen1, hadd1, hlen1_toNat])
      (by simp only [arm64_norm, r21_4, hname_toNat])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (F := vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F)
      (by
        have hord :
            (((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ 47#8) ∗
              ((fsp + 0x458#64) ↦₆₄ cap1) ∗
              (((fsp + 0x460#64) ↦₆₄ ptr1) ∗ ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)))) ∗
              A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
              memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
                (cap1.toNat - dir.length - 1) ∗
              A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
              vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
              (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
              ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F =
            (((fsp + 0x458#64) ↦₆₄ cap1) ∗ ((fsp + 0x460#64) ↦₆₄ ptr1) ∗
              ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)) ∗
              A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
              ((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ 0x2f#8) ∗
              memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
                (cap1.toNat - dir.length - 1)) ∗
            (A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
              vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
              (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
              ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F) := by ac_rfl
        rw [hord, hpack_slash]; exact Entails.of_eq (by ac_rfl)) ?_
    intro s5 ptr2 hs5 hfs5 htr5 hcsm5
    set cap2 : BitVec 64 := BitVec.ofNat 64 (reserveCap cap1.toNat (dir ++ [0x2f#8]).length name.length)
    have hcap2_lt : cap2.toNat < 2 ^ 63 := by
      simp only [cap2, reserveCap, hlen1, BitVec.toNat_ofNat]; m5_omega
    have hcap2_ge : (dir.length + 1) + name.length ≤ cap2.toNat := by
      have hlt64 : reserveCap cap1.toNat (dir.length + 1) name.length < 2 ^ 64 := by
        simp only [reserveCap]; m5_omega
      simp only [cap2, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, reserveCap]; m5_omega
    rw [vecU8At_eq_header_rest]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, _, hptr2⟩ => ?_
    have hpc5 := hs5.pc; have hrun5 := hs5.run; have hfp5 := hs5.fp
    refine m5_run_placed hs5.inv (mid := mPcPlaced 0x970)
      (P0 := ((fsp + 0x458#64) ↦₆₄ cap2) ∗
        ((fsp + 0x460#64) ↦₆₄ ptr2) ∗ ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)))
      (F := vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8]) ∗
        A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
        vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
        (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
        ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F)
      (Entails.of_eq (by ac_rfl)) ?_
    m5_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try m5_bv_omega) (by simp only [arm64_norm, *])
    intro hpcm6 hrunm6 hinv_m6
    refine SepWPp.weaken_pre
      (Entails.of_eq (by ac_rfl))
      (step_970 _ cap2 ptr2 ptr2 (BitVec.ofNat 64 (dir.length + 1)) hnpos hcap2_ge hcap2_lt hptr2
        (mkStepPlaced hs5 hpcm6 hrunm6 (by simp only [arm64_norm]) (by simp only [arm64_norm])
          hinv_m6 (by simp only [calleeSavedVRegs, arm64_norm]))
        (by simp only [arm64_norm, hfs5, hfs4_s])
        (by simp only [arm64_norm, htr5, htr4_s])
        (by simp only [arm64_norm, hcsm5.1, r19_4])
        (by simp only [arm64_norm, hcsm5.2.1, r20_4])
        (by simp only [arm64_norm, hcsm5.2.2.1, r21_4])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, hcsm5.2.2.2.2.2.1, r24_4])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm, hcsm5.2.2.2.2.2.2.2.1, r26_4])
        (by simp only [arm64_norm, hcsm5.2.2.2.2.2.2.2.2.1, r27_4])
        (by simp only [arm64_norm, hcsm5.2.2.2.2.2.2.2.2.2.1, r28_4]))
  · have hgrow_f :
        (cap1 - BitVec.ofNat 64 (dir.length + 1)).ult (BitVec.ofNat 64 name.length) = false :=
      Bool.eq_false_iff.mpr hgrow
    have hfit : (dir.length + 1) + name.length ≤ cap1.toNat := by
      have := mt hult_iff.mpr hgrow; m5_omega
    rcases (show name = [] ∨ 0 < name.length by cases name <;> simp) with hname0 | hnpos
    · have hn0 : BitVec.ofNat 64 name.length = 0#64 := by simp [hname0]
      have hgrow_f0 : (cap1 - BitVec.ofNat 64 (dir.length + 1)).ult 0#64 = false := hn0 ▸ hgrow_f
      refine m5_run_placed hs4.inv (mid := mPcPlaced 0x980)
        (P0 := ((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ b0) ∗
          ((fsp + 0x458#64) ↦₆₄ cap1) ∗
          ((fsp + 0x460#64) ↦₆₄ ptr1) ∗ ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 dir.length))
        (F := A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
          memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
            (cap1.toNat - dir.length - 1) ∗
          A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
          vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
          (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
          ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F)
        (Entails.of_eq (by ac_rfl)) ?_
      m5_steps
      apply SepWP.done (by simp only [arm64_norm, *, hadd1]; try m5_bv_omega)
        (by simp only [arm64_norm, *])
      intro hpcm5 hrunm5 hinv_m5
      refine SepWPp.weaken_pre ?_
        (hnext _ cap1 ptr1 cap1 ptr1 (BitVec.ofNat 64 (dir.length + 1))
          (by m5_omega) (by rw [hp_len]; m5_omega) (by m5_omega) hptr1
          (mkStepPlaced hs4 hpcm5 hrunm5 (by simp only [arm64_norm]) (by simp only [arm64_norm])
            hinv_m5 (by simp only [calleeSavedVRegs, arm64_norm]))
          (by simp only [arm64_norm, hfs4_s]) (by simp only [arm64_norm, htr4_s])
          (by simp only [arm64_norm, r19_4]) (by simp only [arm64_norm, r20_4])
          (by simp only [arm64_norm, r21_4]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, r24_4])
          (by simp only [arm64_norm, hadd1]) (by simp only [arm64_norm, r26_4])
          (by simp only [arm64_norm, r27_4]) (by simp only [arm64_norm, r28_4]))
      have hp0 : pathOf dir name = dir ++ [0x2f#8] := by rw [hp_eq, hname0, List.append_nil]
      have hord :
          (((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ 47#8) ∗
            ((fsp + 0x458#64) ↦₆₄ cap1) ∗
            (((fsp + 0x460#64) ↦₆₄ ptr1) ∗ ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)))) ∗
            A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
            memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
              (cap1.toNat - dir.length - 1) ∗
            A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
            vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
            (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
            ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F =
          (((fsp + 0x458#64) ↦₆₄ cap1) ∗ ((fsp + 0x460#64) ↦₆₄ ptr1) ∗
            ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)) ∗
            A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
            ((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ 0x2f#8) ∗
            memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
              (cap1.toNat - dir.length - 1)) ∗
          (vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
            (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
            ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ F) := by ac_rfl
      rw [hord, hpack_slash, ← hp0, vecU8At_eq_header_rest A (fsp + 0x458#64) cap1 ptr1 (pathOf dir name)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      apply Entails.pure_left; rintro ⟨hle_p, hlt_p, hp_ne⟩
      have hord2 :
          ((fsp + 0x458#64) ↦₆₄ cap1) ∗ ((fsp + 0x460#64) ↦₆₄ ptr1) ∗
            ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (pathOf dir name).length) ∗
            vecU8RestAt A cap1 ptr1 (pathOf dir name) ∗
            vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
            (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
            ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ F =
          vecU8RestAt A cap1 ptr1 (pathOf dir name) ∗
            (vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
              (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
              ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
              ((fsp + 0x458#64) ↦₆₄ cap1) ∗ ((fsp + 0x460#64) ↦₆₄ ptr1) ∗
              ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (pathOf dir name).length) ∗
              stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ F) := by ac_rfl
      rw [hord2]
      exact Entails.trans (sepConj_mono_left (ownedBytes_of_vecU8RestAt A cap1 ptr1 (pathOf dir name)
        hle_p hlt_p hp_ne))
        (Entails.of_eq (by simp only [hp0, List.length_append, List.length_singleton]; rfl))
    · have hn_beq0 : (BitVec.ofNat 64 name.length == 0#64) = false :=
        ofNat_beq_zero_false hnpos (by m5_omega)
      refine m5_run_placed hs4.inv (mid := mPcPlaced 0x970)
        (P0 := ((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ b0) ∗
          ((fsp + 0x458#64) ↦₆₄ cap1) ∗
          ((fsp + 0x460#64) ↦₆₄ ptr1) ∗ ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 dir.length))
        (F := A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
          memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
            (cap1.toNat - dir.length - 1) ∗
          A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
          vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
          (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
          ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F)
        (Entails.of_eq (by ac_rfl)) ?_
      m5_steps
      apply SepWP.done (by simp only [arm64_norm, *, hadd1]; try m5_bv_omega)
        (by simp only [arm64_norm, *])
      intro hpcm5 hrunm5 hinv_m5
      refine SepWPp.weaken_pre ?_
        (step_970 _ cap1 ptr1 ptr1 (BitVec.ofNat 64 (dir.length + 1))
          hnpos hfit (by m5_omega) hptr1
          (mkStepPlaced hs4 hpcm5 hrunm5 (by simp only [arm64_norm]) (by simp only [arm64_norm])
            hinv_m5 (by simp only [calleeSavedVRegs, arm64_norm]))
          (by simp only [arm64_norm, hfs4_s]) (by simp only [arm64_norm, htr4_s])
          (by simp only [arm64_norm, r19_4]) (by simp only [arm64_norm, r20_4])
          (by simp only [arm64_norm, r21_4]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, r24_4])
          (by simp only [arm64_norm, hadd1]) (by simp only [arm64_norm, r26_4])
          (by simp only [arm64_norm, r27_4]) (by simp only [arm64_norm, r28_4]))
      have hord :
          (((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ 47#8) ∗
            ((fsp + 0x458#64) ↦₆₄ cap1) ∗
            (((fsp + 0x460#64) ↦₆₄ ptr1) ∗ ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)))) ∗
            A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
            memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
              (cap1.toNat - dir.length - 1) ∗
            A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
            vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
            (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
            ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗ F =
          (((fsp + 0x458#64) ↦₆₄ cap1) ∗ ((fsp + 0x460#64) ↦₆₄ ptr1) ∗
            ((fsp + 0x468#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)) ∗
            A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ dir) ∗
            ((ptr1 + BitVec.ofNat 64 dir.length) ↦₈ 0x2f#8) ∗
            memRegion (ptr1 + BitVec.ofNat 64 dir.length + BitVec.ofNat 64 1)
              (cap1.toNat - dir.length - 1)) ∗
          (vecHeader base c1 p1 (BitVec.ofNat 64 name.length) ∗
            (dPathPtr ↦ᵣ dir) ∗ (p1 ↦ₛ name) ∗
            ((fsp + 0x40#64) ↦₆₄ dPathPtr) ∗ ((fsp + 0x48#64) ↦₆₄ p1) ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ F) := by ac_rfl
      rw [hord, hpack_slash, vecU8At_eq_header_rest A (fsp + 0x458#64) cap1 ptr1 (dir ++ [0x2f#8])]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, List.length_append, List.length_singleton,
        sepConj_assoc]
      apply Entails.pure_left; intro _
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
