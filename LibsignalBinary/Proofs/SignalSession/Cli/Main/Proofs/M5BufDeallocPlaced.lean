/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common

/-!
# Relocatable `Dir.changed` Buffer Deallocation (`M+0xabc .. M+0xad8`, Block `617`)

Verifies deallocation of the optional `48 * curCap`-byte `Dir.changed` buffer (`M+0xabc .. M+0xad8`)
and loop-back to `AtM5LoopPlaced (k + 1)` under `[LibsignalPlacement]`.
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
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint DoReserveNorm CryptoVerification.SignalSession.Cli.Path.Helpers

set_option maxHeartbeats 1600000 in
/-- Free optional `Dir.changed` buffer (`M+0xabc .. M+0xad8`) and branch into `AtM5LoopPlaced (k + 1)`. -/
theorem m5_buf_dealloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {s0 s : State} {stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hcap_lt : curCap.toNat * 48 < 2 ^ 63)
    (hs : InMainPlaced CodeOk s0 s 0xabc)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx22 : s.readReg64 (.gpr 22#5) = curPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (k + 1))
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 0x28#64)
    (hx27 : s.readReg64 (.gpr 27#5) = curCap)
    (hfiles : commitFiles io.wr F0 (writesBefore g (k + 1)) = some s.fs.files)
    (htr0 : tr0 <+: s.trace)
    (hstdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
      ProcessOutcome.traceStreamBytes .stdout tr0)
    (hP : P ⊢ (if curCap = 0#64 then emp
        else A.live curPtr (curCap.toNat * 48) 8 ∗ memRegion curPtr (curCap.toNat * 48)) ∗
      m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
    (hnext : ∀ sf : State,
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  have finish : ∀ (s1 : State),
      InMainPlaced CodeOk s0 s1 0xad4 →
      s1.readReg64 (.gpr 19#5) = buf →
      s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (k + 1) →
      s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s1.readReg64 (.gpr 25#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64 →
      s1.readReg64 (.gpr 26#5) = 0x28#64 →
      s1.fs = s.fs →
      s1.trace = s.trace →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s1
        (m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp (mainOom s0) := by
    intro s1 hs1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hfs1 htr1
    have hpc1 := hs1.pc
    have hrun1 := hs1.run
    by_cases hk1 : k + 1 < 8
    · have hne8 : (BitVec.ofNat 64 (k + 1) - 8#64 == 0#64) = false := by
        apply beq_false_of_ne; intro h
        have h' : BitVec.ofNat 64 (k + 1) = 8#64 := by m5_bv_omega
        have ht := congrArg BitVec.toNat h'
        simp [BitVec.toNat_ofNat] at ht; m5_omega
      apply m5_seq_placed hs1.inv (mid := mPcPlaced 0x8b8)
      m5_steps
      apply SepWP.done
        (by simp only [arm64_norm, *]; try m5_bv_omega)
        (by simp only [arm64_norm, *])
      intro hpcm hrunm hinv_m
      have hat : AtM5LoopPlaced CodeOk io F0 tr0 g s0 _ n buf (k + 1) :=
        { hk := by m5_omega
          base := by
            simp only [hk1, ↓reduceIte]
            exact mkStepPlaced hs1 hpcm hrunm (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv_m (by simp only [calleeSavedVRegs, arm64_norm])
          x19 := by simp only [arm64_norm, *]
          x23 := by simp only [arm64_norm, *]
          x25 := by simp only [arm64_norm, *]
          x24 := by simp only [arm64_norm, *]
          x26 := by simp only [arm64_norm, *]
          files := by simp only [arm64_norm, hfs1, hfiles]
          trace := by simp only [arm64_norm, htr1]; exact htr0
          stdout := by simp only [arm64_norm, htr1, hstdout] }
      exact hnext _ hat
    · have heq8 : k + 1 = 8 := by m5_omega
      have hbeq8 : (BitVec.ofNat 64 (k + 1) - 8#64 == 0#64) = true := by
        rw [heq8]; decide
      apply m5_seq_placed hs1.inv (mid := mPcPlaced 0xadc)
      m5_steps
      apply SepWP.done
        (by simp only [arm64_norm, *]; try m5_bv_omega)
        (by simp only [arm64_norm, *])
      intro hpcm hrunm hinv_m
      have hat : AtM5LoopPlaced CodeOk io F0 tr0 g s0 _ n buf (k + 1) :=
        { hk := by m5_omega
          base := by
            simp only [hk1, ↓reduceIte]
            exact mkStepPlaced hs1 hpcm hrunm (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv_m (by simp only [calleeSavedVRegs, arm64_norm])
          x19 := by simp only [arm64_norm, *]
          x23 := by simp only [arm64_norm, *]
          x25 := by simp only [arm64_norm, *]
          x24 := by simp only [arm64_norm, *]
          x26 := by simp only [arm64_norm, *]
          files := by simp only [arm64_norm, hfs1, hfiles]
          trace := by simp only [arm64_norm, htr1]; exact htr0
          stdout := by simp only [arm64_norm, htr1, hstdout] }
      exact hnext _ hat
  have hpc := hs.pc
  have hrun := hs.run
  refine SepWPp.weaken_pre hP ?_
  by_cases hcap0 : curCap = 0#64
  · subst hcap0
    simp only [↓reduceIte, emp_sepConj]
    apply m5_seq_placed hs.inv (mid := mPcPlaced 0xad4)
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, *]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm hrunm hinv_m
    exact finish _
      (mkStepPlaced hs hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
        hinv_m (by simp only [calleeSavedVRegs, arm64_norm]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
  · simp only [hcap0, ↓reduceIte]
    have hbeq : (curCap == 0#64) = false := beq_false_of_ne hcap0
    have hpos : 0 < curCap.toNat := by
      have : curCap.toNat ≠ 0 := fun h => hcap0 (BitVec.eq_of_toNat_eq h)
      m5_omega
    have hlay : LayoutOk (curCap.toNat * 48) 8 := ⟨by m5_omega, ⟨3, rfl⟩, by m5_omega⟩
    have h48 : (curCap + (curCap <<< 1#64)) <<< 4#64 = curCap * 48#64 := by bv_kernel
    have hx1_toNat : ((curCap + (curCap <<< 1#64)) <<< 4#64).toNat = curCap.toNat * 48 := by
      rw [h48]
      have hmul : (curCap * 48#64).toNat = (curCap.toNat * 48) % 2 ^ 64 := BitVec.toNat_mul _ _
      rw [hmul, Nat.mod_eq_of_lt (by m5_omega)]
    have hx1_shl :
        (BitVec.extractLsb' 0 60 (curCap + (curCap <<< 1#64)) ++ 0#4).toNat =
          curCap.toNat * 48 := by
      rw [ubfm_lsl1_bv]
      have hmul : (curCap * 48#64).toNat = (curCap.toNat * 48) % 2 ^ 64 := BitVec.toNat_mul _ _
      rw [hmul, Nat.mod_eq_of_lt (by m5_omega)]
    apply m5_seq_placed hs.inv (mid := lsρ lsRustDeallocSymCli)
    m5_steps
    apply SepWP.done
      (by simp only [arm64_norm, *]; try m5_bv_omega)
      (by simp only [arm64_norm, *])
    intro hpcm hrunm hinv_m
    refine m5_call_dealloc_placed hA hstk hstk64 hlay hpcm hrunm hinv_m
      (by simp only [arm64_norm, hs.sp]) (by simp only [arm64_norm, hs.fp])
      (by simp only [calleeSavedVRegs, arm64_norm, hs.vregs]) hs.spAligned
      (retOff := 0xad4)
      (by simp only [arm64_norm, *]; try m5_bv_omega)
      (ptr := curPtr)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; first | exact hx1_toNat | exact hx1_shl)
      (by simp only [arm64_norm]; try rfl)
      (F := ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5LoopCellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g (k + 1)) ∗
        anyHeap)
      (by dsimp only [m5LoopMemPlaced]; exact Entails.of_eq (by ac_rfl)) ?_
    intro sm hsm hfs_m htr_m hcsm
    refine SepWPp.weaken_pre
      (by dsimp only [m5LoopMemPlaced]; exact Entails.of_eq (by ac_rfl))
      (finish sm hsm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (hfs_m.trans (by simp only [arm64_norm]))
        (htr_m.trans (by simp only [arm64_norm])))

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
