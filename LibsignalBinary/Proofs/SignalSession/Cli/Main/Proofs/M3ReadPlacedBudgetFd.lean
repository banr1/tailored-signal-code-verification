/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Descriptor-Threaded `read_file("coins")` Continuations for `main` Hop M3 (Block `617`)

Threads `FdsGe3Closed` across `read_file("coins")` (`M+0x5b0 .. M+0x5d8`) and its error branches on
Block `617`, discharging the return-address guard `LsRetAddr624 ((blkPl_617).base + 0x5c8#64)`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudgetFd

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs lsReadFileSym stdinCapBytes)
open CryptoVerification.SignalSession.Cli (CoinsReadable cliInputs cliStaticsPlaced ioVecAt utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkLib_eq_617 blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM4Placed CallV CallW InMainPlaced IoModel LsCodeInv ReadFileLitGhost argsBuf callHeap cell
   coinsLitSym coinsOf inputOf locals localsBound localsCtx localsEnd localsFrom
   locals_carve_region locals_focus m4CellsPlaced mPcPlaced_eq mProgPlaced mProgPlaced_eq
   mainFrameSize mainLitsBlk617 mainSaved main_call_rocl ownedBytes sepWPp_of_mainOom
   sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (beq_add_one_zero_false_of_lt entails_pure_elim_left entails_pure_intro_left inInv inInvOpt
   mainLitsBlk617Rest mainLitsBlk617_eq memRegion_16_cells optOwnedBytes optOwnedBytes_false
   ownedBytes_entails_optOwned ownedBytes_pure stackAt_sub_split vecU8_to_ownedBytes)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (hookSat_keepLr_withFds_of_withFds_keepLrAndFds lsReadFile_rocl_of_hookSat
   withKeepLrAndFds withLsRetAddr624AndFds withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrPlacedBudget
  (step_err_0x624_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudget (ReadCoinsEnvOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget (ExitKPoolPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileLitSpecPlaced)

attribute [local irreducible] Arm64.Program.fetch Arm64.Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem utf8_coins_length : (utf8 "coins").length = 5 := by
  rw [utf8_eq_kutf8]; decide

private theorem pool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ms : M.σ) (s : State) {s' : State}
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0) (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    A.pool lim ms s' = A.pool lim ms s :=
  A.pool_of_vmPreserved ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

set_option maxHeartbeats 1200000 in
/-- Core `FdsGe3Closed`-threaded continuation across `read_file("coins")` (`M+0x5b0 .. M+0x5d8`)
    and both error tests on Block `617`, parameterized by any return-address guard `lrOk` at
    `lr = (blkPl_617).base + 0x5c8#64`. -/
theorem step_from_0x5b0_readOf_pool_placed_guard_fd [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {lrOk : BitVec 64 → Prop}
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr x27 : BitVec 64} {inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hread : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl
        (withPreGuard (fun s => lrOk (s.readReg64 .lr))
          (withFdsGe3Closed (readFileLitSpecPlaced io A lim hookStack ReadEnv)))))
    (hlr_ok : lrOk ((blkPl_617).base + 1480#64))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (ReadCoinsEnvOf ReadEnv i))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x5b0)
    (hfds : FdsGe3Closed st.fs)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hx27 : st.readReg64 (.gpr 27#5) = x27)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hfiles : st.fs.files = (initFsState (cliInputs i)).files)
    (hst_tr : st.trace = s.trace)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      ReadCoinsEnvOf ReadEnv i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗
          cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hsub_le : hookStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  have hcarve_open :=
    (locals_carve_region fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
      0x1b8 24 []).trans
    (locals_focus fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
      0x1b8 24 (memRegion (fsp + 0x1b8#64) 24) [])
  rw [List.append_nil] at hcarve_open
  rw [hcarve_open, mainLitsBlk617_eq]
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsReadFileSym) hinv
  wp_steps
  apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
  intro hinv1
  refine main_call_rocl (CodeOk := CodeOk)
    (spec := withPreGuard (fun s => lrOk (s.readReg64 .lr))
      (withFdsGe3Closed (readFileLitSpecPlaced io A lim hookStack ReadEnv)))
    (({ pathA := lsρ coinsLitSym, path := utf8 "coins", ret := fsp + 0x1b8#64 } : ReadFileLitGhost), ms)
    hread
    hinv1 (by (try simp only [arm64_norm, *]); try rfl) (by (try simp only [arm64_norm, *]); try rfl)
    (by simp only [arm64_norm]; exact hal)
    (ret_pc := (blkPl_617).base + 1480#64) (by (try simp only [arm64_norm, *]); try rfl)
    (F := inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗ callHeap A.repAlloc w c ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
      ArgvFrame ∗
      mainSaved s0 ∗
      localsCtx fsp 0
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
        0x1b8 24 [] ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      cliStaticsPlaced ∗ mainLitsBlk617Rest)
    ?_ (hnext := ?_)
  · dsimp only [withPreGuard, withFdsGe3Closed, readFileLitSpecPlaced]
    conv => arg 2; rw [pool_congr_vm A lim ms st (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm])]
    simp only [arm64_norm, hsp, hfiles]
    rw [stackAt_sub_split fsp hsub_le hsub64]
    simp only [sepConj_assoc]
    apply entails_pure_intro_left
      ⟨hlr_ok, hfds, utf8_coins_length.symm, by rw [utf8_coins_length]; decide, hcoinsOk, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [withPreGuard, withFdsGe3Closed, readFileLitSpecPlaced]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hfds_sf => ?_
    have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by rw [hcs_f.1]; simp only [arm64_norm, hx19]
    have hx20_f : sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag := by
      rw [hcs_f.2.1]; simp only [arm64_norm, hx20]
    have hx21_f : sf.readReg64 (.gpr 21#5) = w.w5 := by
      rw [hcs_f.2.2.1]; simp only [arm64_norm]
    have hx22_f : sf.readReg64 (.gpr 22#5) = w.w2 := by
      rw [hcs_f.2.2.2.1]; simp only [arm64_norm, hx22]
    have hx23_f : sf.readReg64 (.gpr 23#5) = inCap := by
      rw [hcs_f.2.2.2.2.1]; simp only [arm64_norm, hx23]
    have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length := by
      rw [hcs_f.2.2.2.2.2.1]; simp only [arm64_norm, hx24]
    have hx25_f : sf.readReg64 (.gpr 25#5) = w.w0 := by
      rw [hcs_f.2.2.2.2.2.2.1]; simp only [arm64_norm, hx25]
    have hx26_f : sf.readReg64 (.gpr 26#5) = w.w6 := by
      rw [hcs_f.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hx26]
    have hx27_f : sf.readReg64 (.gpr 27#5) = x27 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hx27]
    have hsp_sf : sf.sp = fsp := by rw [hsp_f]; simp only [arm64_norm, hsp]
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf, fsp, mainFrameSize]
      exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hst.spAligned
    have hfp_sf : sf.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hst.fp]
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.2]; simp only [calleeSavedVRegs, arm64_norm, hst.vregs]
    have hsp_pre : (_ : State).sp = fsp := hsp_f.symm.trans hsp_sf
    rw [hsp_pre]
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hevs => ?_
    have hevs' : ReadCoinsEnvOf ReadEnv i evs := by
      simpa only [ReadCoinsEnvOf, arm64_norm, hfiles] using hevs
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    refine SepWPp.exists_elim fun rCoins => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hfiles_f, hrd_rf, htr_sf⟩ => ?_
    have hfiles_sf : sf.fs.files = (initFsState (cliInputs i)).files :=
      hfiles_f.trans (by simp only [arm64_norm, hfiles])
    have hrd_rf' : rCoins = io.rd (initFsState (cliInputs i)).files (utf8 "coins") := by
      simpa only [arm64_norm, hfiles] using hrd_rf
    cases rCoins with
    | ok cBs =>
      have hc_eq : cBs = coinsOf i := by
        rcases hcoins _ hrd_rf'.symm with hok_c | ⟨herr_c, -⟩
        · exact Except.ok.inj hok_c
        · cases herr_c
      subst hc_eq
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (vecU8_to_ownedBytes A.repAlloc (fsp + 0x1b8#64) (coinsOf i))) ?_
      rw [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun coinsCap => ?_
      rw [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun coinsPtr => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
            (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ stackAt fsp hookStack ∗
            A.pool lim (M.stepEvents evs ms) sf ∗
            (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
              ArgvFrame ∗
              mainSaved s0 ∗
              localsCtx fsp 0
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                0x1b8 24 [] ∗
              memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                (stk - mainFrameSize - hookStack) ∗
              cliStaticsPlaced ∗ mainLitsBlk617Rest)) by sep_ac_rfl)) ?_
      rw [ownedBytes_pure A.repAlloc coinsCap coinsPtr
            (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i),
          sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, _, hcoins_lt, _⟩ => ?_
      have hcoins_nzero := beq_add_one_zero_false_of_lt hcoins_lt
      cases inOk with
      | true =>
        dsimp only [inInvOpt, inInv]
        refine SepWPp.weaken_pre (Entails.of_eq (show _ =
          ⌜(inputOf i c).length ≤ stdinCapBytes⌝ ∗
            (⌜x27 = BitVec.ofNat 64 (inputOf i c).length⌝ ∗
              (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
                ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
                ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
                ownedBytes A.repAlloc coinsCap coinsPtr
                  (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
                (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ stackAt fsp hookStack ∗
                A.pool lim (M.stepEvents evs ms) sf ∗
                (callHeap A.repAlloc w c ∗
                  argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
                  ArgvFrame ∗
                  mainSaved s0 ∗
                  localsCtx fsp 0
                    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                    0x1b8 24 [] ∗
                  memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                    (stk - mainFrameSize - hookStack) ∗
                  cliStaticsPlaced ∗ mainLitsBlk617Rest))) by sep_ac_rfl)) ?_
        refine SepWPp.pure_elim fun hin_cap_le => ?_
        refine SepWPp.pure_elim fun hx27_len => ?_
        rw [ownedBytes_pure A.repAlloc inCap inPtr
              (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c),
            sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨_, _, hin_lt, _⟩ => ?_
        have hin_nzero := beq_add_one_zero_false_of_lt hin_lt
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1500#64) hinv_f
        wp_steps
        apply SepWP.done
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, *]); try rfl)
        intro hinv_5dc
        have hin_5dc : InMainPlaced CodeOk s0 _ 0x5dc := {
          inv := hinv_5dc
          pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
          run := by simp only [arm64_norm, *]
          sp := by (try simp only [arm64_norm]); exact hsp_sf
          fp := by (try simp only [arm64_norm]); exact hfp_sf
          vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
          spAligned := hst.spAligned
        }
        have hatM4 : AtM4Placed CodeOk i s0 _ w c i.argv.length buf coinsCap coinsPtr inCap := {
          base := hin_5dc
          x0 := by simp only [arm64_norm]
          x1 := by simp only [arm64_norm]
          x19 := by simp only [arm64_norm, hx19_f]
          x20 := by simp only [arm64_norm, hx20_f]
          x23 := by simp only [arm64_norm, hx23_f]
          x24 := by simp only [arm64_norm, hx24_f]
          x27 := by simp only [arm64_norm, hx27_f, hx27_len]
          w0 := by simp only [arm64_norm, hx25_f]
          w2 := by simp only [arm64_norm, hx22_f]
          w5 := by simp only [arm64_norm, hx21_f]
          w6 := by simp only [arm64_norm, hx26_f]
          fs := by simp only [arm64_norm, hfiles_sf]
          trace := by
            simp only [arm64_norm]
            exact htr_sf.trans ((by simp only [arm64_norm] : _ = st.trace).trans (hst_tr.trans hs_tr))
        }
        refine SepWPp.weaken_pre ?_
          (hnext _ coinsCap coinsPtr inCap inPtr evs hevs' hin_cap_le hatM4
            (by simpa only [arm64_norm] using hfds_sf))
        conv => arg 2; rw [pool_congr_vm A lim (M.stepEvents evs ms) sf
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
        have hm4_merge :
            ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
              localsCtx fsp 0
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                0x1b8 24 [] ⊢
              locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) := by
          have h24 :
              ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ⊢
                memRegion (fsp + 0x1b8#64) 16 := by
            rw [memRegion_split (fsp + 0x1b8#64) 8 8 (by decide),
              show (fsp + 0x1b8#64) + 8#64 = fsp + 0x1c0#64 by rw [BitVec.add_assoc]; rfl]
            exact sepConj_mono
              (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
          have hctx_eq :
              memRegion (fsp + 0x1b8#64) 16 ∗
                ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
                localsCtx fsp 0
                  [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                  0x1b8 24 [] =
                locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) := by
            simp only [locals, localsFrom, localsCtx, Nat.reduceAdd, Nat.reduceSub]
            rw [ProofLib.memRegion_split' (b := fsp + 0x60#64) (b' := fsp + 0x1b8#64)
              (N := 0x168) (n := 0x158) (k := 16) (by decide) (by rw [BitVec.add_assoc]; rfl)
              (by decide)]
            sep_ac_rfl
          rw [← hctx_eq, ← sepConj_assoc]
          exact sepConj_mono_left h24
        rw [stackAt_sub_split fsp hsub_le hsub64, mainLitsBlk617_eq]
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            localsCtx fsp 0
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
              0x1b8 24 []) ∗
          (ownedBytes A.repAlloc coinsCap coinsPtr
              (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
            ownedBytes A.repAlloc inCap inPtr
              (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            ArgvFrame ∗
            mainSaved s0 ∗
            (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
            A.pool lim (M.stepEvents evs ms) sf ∗ cliStaticsPlaced ∗
            ((lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617Rest)) by sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hm4_merge) ?_
        exact Entails.of_eq (by sep_ac_rfl)
      | false =>
        dsimp only [inInvOpt]
        refine SepWPp.weaken_pre (Entails.of_eq (show _ =
          ⌜inCap = 0xffffffffffffffff#64 ∧ 1 < c.tag ∧ stdinCapBytes < i.stdin.length⌝ ∗
            (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
              ownedBytes A.repAlloc coinsCap coinsPtr
                (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
              (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ stackAt fsp hookStack ∗
              A.pool lim (M.stepEvents evs ms) sf ∗
              (callHeap A.repAlloc w c ∗
                argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
                ArgvFrame ∗
                mainSaved s0 ∗
                localsCtx fsp 0
                  [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                  0x1b8 24 [] ∗
                memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                  (stk - mainFrameSize - hookStack) ∗
                cliStaticsPlaced ∗ mainLitsBlk617Rest)) by sep_ac_rfl)) ?_
        refine SepWPp.pure_elim fun ⟨hin_neg1, htag_gt1, hstdin_gt⟩ => ?_
        subst hin_neg1
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1572#64) hinv_f
        wp_steps
        apply SepWP.done
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, *]); try rfl)
        intro hinv_624
        have hin_624 : InMainPlaced CodeOk s0 _ 0x624 := {
          inv := hinv_624
          pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
          run := by simp only [arm64_norm, *]
          sp := by (try simp only [arm64_norm]); exact hsp_sf
          fp := by (try simp only [arm64_norm]); exact hfp_sf
          vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
          spAligned := hst.spAligned
        }
        have htr_sf_eq : sf.trace = s.trace :=
          htr_sf.trans (by simp only [arm64_norm, hst_tr])
        refine SepWPp.weaken_pre ?_
          (sepWPp_of_mainOom (step_err_0x624_pool_placed
            (ms := M.stepEvents evs ms)
            (P := ¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length))
            (i := i) (s := s) (n := i.argv.length) (buf := buf)
            (coinsOk := true) (inOk := false)
            (coinsCap := coinsCap) (coinsPtr := coinsPtr)
            (inCap := 0xffffffffffffffff#64) (inPtr := inPtr)
            (c := c) (w := w) (ps := ps) hc hstk hstk64 hin_624
            (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl)
            (by (try simp only [arm64_norm, hx19_f]); try rfl)
            (by (try simp only [arm64_norm, hx20_f]); try rfl)
            (by (try simp only [arm64_norm, hx21_f]); try rfl)
            (by (try simp only [arm64_norm, hx22_f]); try rfl)
            (by (try simp only [arm64_norm, hx23_f]); try rfl)
            (by (try simp only [arm64_norm, hx24_f]); try rfl)
            (by (try simp only [arm64_norm, hx25_f]); try rfl)
            (by exact ⟨by simpa only [arm64_norm] using hfiles_sf, Or.inr ⟨htag_gt1, hstdin_gt⟩,
              by simpa only [arm64_norm] using htr_sf_eq⟩)
            hexit))
        conv => arg 2; rw [pool_congr_vm A lim (M.stepEvents evs ms) sf
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
        have hloc_back :
            ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
              localsCtx fsp 0
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                0x1b8 24 [] ⊢
              locals fsp
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] := by
          have h24 :
              ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
                ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ⊢
                memRegion (fsp + 0x1b8#64) 24 := by
            rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
              memRegion_split (fsp + 0x1b8#64) 8 (8 + 8) (by decide),
              memRegion_split ((fsp + 0x1b8#64) + 8#64) 8 8 (by decide)]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            exact sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
          rw [hcarve_open]
          rw [← sepConj_assoc, ← sepConj_assoc]
          exact sepConj_mono_left (by simpa only [sepConj_assoc] using h24)
        have hcoins_opt :
            ownedBytes A.repAlloc coinsCap coinsPtr
              (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ⊢
              optOwnedBytes A.repAlloc true coinsCap coinsPtr :=
          ownedBytes_entails_optOwned _ _ _ _ _
        have hin_opt : emp ⊢ optOwnedBytes A.repAlloc false 0xffffffffffffffff#64 inPtr := by
          rw [optOwnedBytes_false, ← sepConj_emp ⌜_⌝]
          exact entails_pure_intro_left rfl (Entails.refl emp)
        rw [stackAt_sub_split fsp hsub_le hsub64]
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            localsCtx fsp 0
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
              0x1b8 24 []) ∗
          ownedBytes A.repAlloc coinsCap coinsPtr
            (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          emp ∗
          (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗
            (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
            A.pool lim (M.stepEvents evs ms) sf ∗
            ((lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗
              ArgvFrame ∗
              cliStaticsPlaced ∗ mainLitsBlk617Rest)) by simp only [emp_sepConj]; sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hloc_back
          (sepConj_mono hcoins_opt (sepConj_mono hin_opt
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (ProofLib.entails_anyHeap _))))))))) ?_
        exact Entails.of_eq (by sep_ac_rfl)
    | error u =>
      cases u
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (sepConj_mono_right (memRegion_16_cells (fsp + 0x1b8#64)))) ?_
      simp only [sepExists_sepConj_right, sepExists_sepConj_left]
      refine SepWPp.exists_elim fun errCoinsPtr => ?_
      refine SepWPp.exists_elim fun errCoinsLen => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1572#64) hinv_f
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv_624
      have hin_624 : InMainPlaced CodeOk s0 _ 0x624 := {
        inv := hinv_624
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hsp_sf
        fp := by (try simp only [arm64_norm]); exact hfp_sf
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
        spAligned := hst.spAligned
      }
      have htr_sf_eq : sf.trace = s.trace :=
        htr_sf.trans (by simp only [arm64_norm, hst_tr])
      have hnr_coins : ¬ CoinsReadable i := by
        rcases hcoins _ hrd_rf'.symm with hok_c | ⟨-, hnr⟩
        · cases hok_c
        · exact hnr
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_mainOom (step_err_0x624_pool_placed
          (ms := M.stepEvents evs ms)
          (P := ¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length))
          (i := i) (s := s) (n := i.argv.length) (buf := buf)
          (coinsOk := false) (inOk := inOk)
          (coinsCap := 0xffffffffffffffff#64) (coinsPtr := errCoinsPtr)
          (inCap := inCap) (inPtr := inPtr)
          (c := c) (w := w) (ps := ps) hc hstk hstk64 hin_624
          (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx19_f]); try rfl)
          (by (try simp only [arm64_norm, hx20_f]); try rfl)
          (by (try simp only [arm64_norm, hx21_f]); try rfl)
          (by (try simp only [arm64_norm, hx22_f]); try rfl)
          (by (try simp only [arm64_norm, hx23_f]); try rfl)
          (by (try simp only [arm64_norm, hx24_f]); try rfl)
          (by (try simp only [arm64_norm, hx25_f]); try rfl)
          (by exact ⟨by simpa only [arm64_norm] using hfiles_sf, Or.inl hnr_coins,
            by simpa only [arm64_norm] using htr_sf_eq⟩)
          hexit))
      conv => arg 2; rw [pool_congr_vm A lim (M.stepEvents evs ms) sf
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
      have hloc_back :
          ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 0x1c0#64) ↦₆₄ errCoinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ errCoinsLen) ∗
            localsCtx fsp 0
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
              0x1b8 24 [] ⊢
            locals fsp
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] := by
        have h24 :
            ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 0x1c0#64) ↦₆₄ errCoinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ errCoinsLen) ⊢
              memRegion (fsp + 0x1b8#64) 24 := by
          rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
            memRegion_split (fsp + 0x1b8#64) 8 (8 + 8) (by decide),
            memRegion_split ((fsp + 0x1b8#64) + 8#64) 8 8 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
        rw [hcarve_open]
        rw [← sepConj_assoc, ← sepConj_assoc]
        exact sepConj_mono_left (by simpa only [sepConj_assoc] using h24)
      have hin_opt :
          inInvOpt inOk A.repAlloc i c inCap inPtr x27 ⊢
            optOwnedBytes A.repAlloc inOk inCap inPtr := by
        cases inOk with
        | false =>
          dsimp only [inInvOpt]
          rw [optOwnedBytes_false, ← sepConj_emp ⌜_ ∧ _⌝]
          exact entails_pure_elim_left fun h => by
            rw [← sepConj_emp ⌜_⌝]
            exact entails_pure_intro_left h.1 (Entails.refl emp)
        | true =>
          dsimp only [inInvOpt, inInv]
          exact entails_pure_elim_left fun _ =>
            entails_pure_elim_left fun _ => ownedBytes_entails_optOwned _ _ _ _ _
      have hcoins_opt : emp ⊢ optOwnedBytes A.repAlloc false 0xffffffffffffffff#64 errCoinsPtr := by
        rw [optOwnedBytes_false, ← sepConj_emp ⌜_⌝]
        exact entails_pure_intro_left rfl (Entails.refl emp)
      rw [stackAt_sub_split fsp hsub_le hsub64]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 0x1c0#64) ↦₆₄ errCoinsPtr) ∗
          ((fsp + 0x1c8#64) ↦₆₄ errCoinsLen) ∗
          localsCtx fsp 0
            [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
            0x1b8 24 []) ∗
        emp ∗
        inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
          A.pool lim (M.stepEvents evs ms) sf ∗
          ((lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗
            ArgvFrame ∗
            cliStaticsPlaced ∗ mainLitsBlk617Rest)) by simp only [emp_sepConj]; sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hloc_back
        (sepConj_mono hcoins_opt (sepConj_mono hin_opt
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (ProofLib.entails_anyHeap _))))))))) ?_
      exact Entails.of_eq (by sep_ac_rfl)

/-- `subroutine_ok` `LsRetAddr624` twin of `M3ReadPlacedBudget.step_from_0x5b0_readOf_pool_placed`,
    discharging `LsRetAddr624 ((blkPl_617).base + 0x5c8#64)` locally by `decide`. -/
theorem step_from_0x5b0_readOf_pool_placed_subroutine_fd [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr x27 : BitVec 64} {inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hread : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl
        (withLsRetAddr624AndFds (readFileLitSpecPlaced io A lim hookStack ReadEnv))))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (ReadCoinsEnvOf ReadEnv i))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x5b0)
    (hfds : FdsGe3Closed st.fs)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hx27 : st.readReg64 (.gpr 27#5) = x27)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hfiles : st.fs.files = (initFsState (cliInputs i)).files)
    (hst_tr : st.trace = s.trace)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      ReadCoinsEnvOf ReadEnv i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗
          cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  step_from_0x5b0_readOf_pool_placed_guard_fd hc hread
    (lsRetAddr624_blockPlacement_base_add 617 1480#64 (by decide) (by decide))
    hstk hstk64 hcoinsOk hcoins hfit hs_tr hst hfds
    hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27 hw5_orr hfiles hst_tr hexit hnext

/-- `HookSat` `LsRetAddr624` twin of `M3ReadPlacedBudget.step_from_0x5b0_readOf_pool_placed`,
    taking `HookSat H lsReadFileSym (withLsRetAddr624AndFds (readFileLitSpecPlaced ...))` and
    discharging `LsRetAddr624 ((blkPl_617).base + 0x5c8#64)` locally by `decide`. -/
theorem step_from_0x5b0_readOf_pool_placed_fd [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr x27 : BitVec 64} {inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hSat : HookSat H lsReadFileSym
      (withLsRetAddr624AndFds (readFileLitSpecPlaced io A lim hookStack ReadEnv)))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (ReadCoinsEnvOf ReadEnv i))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x5b0)
    (hfds : FdsGe3Closed st.fs)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hx27 : st.readReg64 (.gpr 27#5) = x27)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hfiles : st.fs.files = (initFsState (cliInputs i)).files)
    (hst_tr : st.trace = s.trace)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      ReadCoinsEnvOf ReadEnv i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗
          cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  step_from_0x5b0_readOf_pool_placed_subroutine_fd hc
    (lsReadFile_rocl_of_hookSat (callerProg := lsProg_617 H) (i := 617) hSat)
    hstk hstk64 hcoinsOk hcoins hfit hs_tr hst hfds
    hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27 hw5_orr hfiles hst_tr hexit hnext

/-- `HookSat` `keepSet` twin of `M3ReadPlacedBudget.step_from_0x5b0_readOf_pool_placed` for
    `withFdsGe3Closed (withKeepLrAndFds keepSet (readFileLitSpecPlaced ...))`
    (definitionally `withFdsGe3Closed (h2k_readFileLitSpecK ...)` at `keepSet := hole2_keepSub`). -/
theorem step_from_0x5b0_readOf_pool_placed_keep_fd [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {keepSet : BitVec 64 → Bool}
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr x27 : BitVec 64} {inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hSat : HookSat H lsReadFileSym
      (withFdsGe3Closed
        (withKeepLrAndFds keepSet (readFileLitSpecPlaced io A lim hookStack ReadEnv))))
    (hlr : keepSet ((blkPl_617).base + 1480#64) = false)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hfit : FitsEnv M lim ms (ReadCoinsEnvOf ReadEnv i))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x5b0)
    (hfds : FdsGe3Closed st.fs)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hx27 : st.readReg64 (.gpr 27#5) = x27)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hfiles : st.fs.files = (initFsState (cliInputs i)).files)
    (hst_tr : st.trace = s.trace)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      ReadCoinsEnvOf ReadEnv i evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗
          cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) st
      (inInvOpt inOk A.repAlloc i c inCap inPtr x27 ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms st ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  step_from_0x5b0_readOf_pool_placed_guard_fd (lrOk := fun lr => keepSet lr = false) hc
    (lsReadFile_rocl_of_hookSat (callerProg := lsProg_617 H) (i := 617)
      (hookSat_keepLr_withFds_of_withFds_keepLrAndFds hSat))
    hlr hstk hstk64 hcoinsOk hcoins hfit hs_tr hst hfds
    hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27 hw5_orr hfiles hst_tr hexit hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudgetFd
