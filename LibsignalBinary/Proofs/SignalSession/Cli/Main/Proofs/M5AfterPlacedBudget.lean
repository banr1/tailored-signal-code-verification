/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5BufDeallocPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common

/-!
# Budget-Threaded Post-Entries Convergence & M5 Completion Hop (Block `617`)

Budget-threaded verification of `m5_after_entries_placed` (`M+0xa6c → AtM5LoopPlaced (k + 1)`,
advancing `A.pool` by `FreeOnlyEvs`) and `m5_done_placed` (`M+0xadc → M+0xf70`) under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (arrayAt vecBuf)
open CryptoVerification.SignalSession.Cli (StoresGhost dirEntryAt)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM5LoopPlaced AtM6Placed InMainPlaced IoModel LsCodeInv argsBuf commitFiles locals
   locals_m5LoopCellsPlaced_eight m5LoopMemPlaced m6CellsPlaced mPcPlaced mainFrameSize mainSaved
   ownedBytes writesBefore writesBefore_eight)
open CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
  (m5ScratchPlaced m5WorkRestPlaced m5Work_exit_to_next_placed m5_run_placed m5_seq_placed
   mkStepPlaced)
open scoped CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5BufDeallocPlacedBudget
  (m5BufDeallocEnv_freeOnly m5_buf_dealloc_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
  (m5_entry_drop_loop_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
  (argsBuf_atState_eq_repAlloc m5LoopCellsPlaced_atState_eq_repAlloc
   ownedBytes_atState_eq_repAlloc)

attribute [local arm64_norm]
  RustCliAllocBudget.pool_setPC
  RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState
  RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32
  RustCliAllocBudget.pool_writeReg

namespace LoopDrop

set_option maxHeartbeats 1600000 in
/-- Budget-threaded shared convergence tail (`M+0xa6c .. M+0xa80 -> M+0xa90 -> M+0xabc -> AtM5LoopPlaced (k + 1)`)
entered once Loop A or Loop B has committed all `curEntries ≠ []` of `Dir k`, advancing `A.pool` by
`FreeOnlyEvs`. -/
theorem m5_after_entries_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {s0 s : State} {stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr v40 v48 v58 v458 v460 v468 : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {curEntries : List (List (BitVec 8) × List (BitVec 8))}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk : k < 8)
    (hne : curEntries ≠ [])
    (hs : InMainPlaced CodeOk s0 s 0xa6c)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 curEntries.length)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hfiles : commitFiles io.wr F0 (writesBefore g (k + 1)) = some s.fs.files)
    (htr0 : tr0 <+: s.trace)
    (hstdout : ProcessOutcome.traceStreamBytes .stdout s.trace =
      ProcessOutcome.traceStreamBytes .stdout tr0)
    (hP : P ⊢ vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) curCap curPtr curEntries ∗
      m5ScratchPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
        curCap curPtr (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
        v40 v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize)
        outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
      A.pool lim st s ∗ anyHeap)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 sf n buf (k + 1) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sf
        (m5LoopMemPlaced (A.atState lim (M.stepEvents evs st) sf)
          s0 stk n outCap outPtr inCap inPtr buf out inp ps g (k + 1))
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  refine SepWPp.weaken_pre hP ?_
  unfold vecBuf
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hle, hcap_lt, _⟩ => ?_
  have hpos : 0 < curEntries.length := List.length_pos_of_ne_nil hne
  have hcap_ne0 : curCap ≠ 0 := by
    intro h0; subst h0; change curEntries.length ≤ 0 at hle; m5_omega
  have hcap_ne : curCap ≠ 0#64 := hcap_ne0
  simp only [hcap_ne0, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
  have hpc := hs.pc; have hrun := hs.run
  refine m5_run_placed hs.inv (mid := mPcPlaced 0xa90)
    (P0 := ((s.sp + 0x20#64) ↦₆₄ curCap) ∗
      ((s.sp + 0x28#64) ↦₆₄ curPtr) ∗
      ((s.sp + 0x30#64) ↦₆₄ (fsp + 0x1c8#64)) ∗
      ((s.sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 (k + 1)))
    (F := (((fsp + 0x40#64) ↦₆₄ v40) ∗ ((fsp + 0x48#64) ↦₆₄ v48) ∗
        ((fsp + 0x58#64) ↦₆₄ v58) ∗
        ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗
        ((fsp + 0x468#64) ↦₆₄ v468)) ∗
      (A.live curPtr (curCap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 curPtr curEntries ∗
        memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
          ((curCap.toNat - curEntries.length) * 48)) ∗
      m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗
      stackAt fsp (stk - mainFrameSize) ∗
      A.pool lim st s ∗ anyHeap)
    (by
      dsimp only [fsp, m5ScratchPlaced]
      rw [hs.sp]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *]; try m5_bv_omega)
    (by simp only [arm64_norm, *])
  intro hpcm hrunm hinv_m
  have hs_a90 : InMainPlaced CodeOk s0 _ 0xa90 :=
    mkStepPlaced hs hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
      hinv_m (by simp only [calleeSavedVRegs, arm64_norm])
  refine m5_entry_drop_loop_placed (st := st) (base := curPtr) curEntries hA hstk hstk64 hne
    (by m5_omega) hs_a90
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hx20])
    (F := A.live curPtr (curCap.toNat * 48) 8 ∗
      memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
        ((curCap.toNat - curEntries.length) * 48) ∗
      m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
        v40 v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
      ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗ anyHeap)
    (by
      dsimp only [fsp, m5ScratchPlaced]
      rw [hs.sp]
      simp only [arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  intro sm evs1 hf1 hsm hfsm htrm m19 m22 m23 m24 m25 m26 m27
  have hmerge_buf :
      memRegion curPtr (curEntries.length * 48) ∗
        memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
          ((curCap.toNat - curEntries.length) * 48) =
      memRegion curPtr (curCap.toNat * 48) := by
    have hmul : curCap.toNat * 48 =
        curEntries.length * 48 + (curCap.toNat - curEntries.length) * 48 := by
      have := Nat.add_sub_of_le hle
      calc curCap.toNat * 48
        _ = (curEntries.length + (curCap.toNat - curEntries.length)) * 48 := by rw [this]
        _ = curEntries.length * 48 + (curCap.toNat - curEntries.length) * 48 := Nat.add_mul _ _ _
    rw [hmul, ProofLib.memRegion_split curPtr (curEntries.length * 48)
      ((curCap.toNat - curEntries.length) * 48) (by m5_omega)]
  have hexit := m5Work_exit_to_next_placed A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length)
    inCap inPtr g hk curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
    v40 v48 v58 v458 v460 v468
  refine m5_buf_dealloc_placed (st := M.stepEvents evs1 st)
    (io := io) (F0 := F0) (tr0 := tr0) (g := g) (stk := stk) (n := n)
    (outCap := outCap) (outPtr := outPtr) (inCap := inCap) (inPtr := inPtr)
    (buf := buf) (curCap := curCap) (curPtr := curPtr)
    (out := out) (inp := inp) (ps := ps)
    hA hstk hstk64 hk hcap_lt hsm
    (m19.trans (by simp only [arm64_norm, hx19]))
    (m22.trans (by simp only [arm64_norm]))
    (m23.trans (by simp only [arm64_norm]))
    (m24.trans (by simp only [arm64_norm, hx24]))
    (m25.trans (by dsimp only [fsp]; simp only [arm64_norm]; try rfl))
    (m26.trans (by simp only [arm64_norm]))
    (m27.trans (by simp only [arm64_norm]))
    (by simp only [hfsm, arm64_norm, hfiles])
    (by simp only [htrm, arm64_norm]; exact htr0)
    (by simp only [htrm, arm64_norm, hstdout])
    ?_ ?_
  · simp only [hcap_ne, ↓reduceIte, m5LoopMemPlaced, RustCliAllocBudget.atState_pool,
      ownedBytes_atState_eq_repAlloc, argsBuf_atState_eq_repAlloc,
      m5LoopCellsPlaced_atState_eq_repAlloc]
    have hreord :
        memRegion curPtr (curEntries.length * 48) ∗ A.pool lim (M.stepEvents evs1 st) sm ∗
          stackAt fsp (stk - mainFrameSize) ∗
          (A.live curPtr (curCap.toNat * 48) 8 ∗
            memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
              ((curCap.toNat - curEntries.length) * 48) ∗
            m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
              v40 v48 v58 v458 v460 v468 ∗
            m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k ∗
            ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
            mainSaved s0 ∗ anyHeap) =
        (m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
            v40 v48 v58 v458 v460 v468 ∗
          m5WorkRestPlaced A.repAlloc fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr g k) ∗
        ((A.live curPtr (curCap.toNat * 48) 8 ∗
            (memRegion curPtr (curEntries.length * 48) ∗
              memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
                ((curCap.toNat - curEntries.length) * 48))) ∗
          (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
            mainSaved s0 ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool lim (M.stepEvents evs1 st) sm ∗ anyHeap)) := by
      sep_ac_rfl
    rw [hreord, hmerge_buf]
    refine Entails.trans (sepConj_mono_left hexit) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf evs2 hevs2 hat
    rw [← M.stepEvents_append evs1 evs2 st]
    exact hnext sf (evs1 ++ evs2) (hf1.append (m5BufDeallocEnv_freeOnly curCap hevs2)) hat

set_option maxHeartbeats 1600000 in
/-- Budget-threaded completion hop: after all 8 `Dir`s succeed (`AtM5LoopPlaced … 8` at `M+0xadc`),
step `M+0xadc -> M+0xc5c -> M+0xf70` into `AtM6Placed … true`. -/
theorem m5_done_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {s0 s : State} {stk n : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hs : AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf 8)
    (hnext : ∀ s' : State,
      commitFiles io.wr F0 g.writes = some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      AtM6Placed CodeOk s0 s' true n buf →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
              outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st s' ∗ anyHeap)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (m5LoopMemPlaced (A.atState lim st s) s0 stk n outCap outPtr inCap inPtr buf out inp ps g 8)
      Q Qp oom := by
  have hbase : InMainPlaced CodeOk s0 s 0xadc := by simpa using hs.base
  have hx23 := hs.x23
  have hx19 := hs.x19
  have hx24 := hs.x24
  have hpc := hbase.pc
  have hrun := hbase.run
  apply m5_seq_placed hbase.inv (mid := mPcPlaced 0xc5c)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm1 hrunm1 hinv_m1
  apply m5_seq_placed hinv_m1 (mid := mPcPlaced 0xf70)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm hrunm hinv_m
  have hfiles : commitFiles io.wr F0 g.writes = some s.fs.files := by
    have := hs.files; rwa [writesBefore_eight] at this
  have hat6 : AtM6Placed CodeOk s0 _ true n buf :=
    { base := mkStepPlaced hbase hpcm hrunm (by simp only [arm64_norm]) (by simp only [arm64_norm])
        hinv_m (by simp only [calleeSavedVRegs, arm64_norm])
      w22 := by simp only [arm64_norm]
      x19 := by simp only [arm64_norm, hx19]
      x24 := by simp only [arm64_norm, hx24] }
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, hfiles])
      (by simp only [arm64_norm]; exact hs.trace)
      (by simp only [arm64_norm, hs.stdout]) hat6)
  dsimp only [m5LoopMemPlaced]
  rw [locals_m5LoopCellsPlaced_eight]
  simp only [ownedBytes_atState_eq_repAlloc, argsBuf_atState_eq_repAlloc,
    RustCliAllocBudget.atState_pool, arm64_norm]
  exact Entails.refl _

end LoopDrop

export LoopDrop (m5_after_entries_placed m5_done_placed)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5AfterPlacedBudget
