/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitBundlePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.Pure
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `init` Dispatch Branch (`M+0x240`, Block `617`)

Verifies `main`'s 3-argument `"init"` dispatch branch at `M+0x240` with read-only `argvAtROP` and
`RustCliAllocBudget M`, routing invalid commands or addresses to `exit 2` and valid peers into
bundle allocation (`M+0x274`) under `InitBranchEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (CliInputsOk utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtCallPlaced CallV CallW InMainPlaced LsCodeInv addrParse argsBuf
   callCellsPlaced callHeap locals mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize mainSaved
   parseArgs sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.Proofs
  (argsBufTail argsBuf_three_cons argsBuf_three_eq cliInputsOk_elem cmn1_false
   fsp_align_of_spAligned le32_init_iff locals_merge_memRegion m2LocalsRest main_call_keepsFs_placed
   parseArgs_three_bad_cmd perm_parseFail_pre protocolAddressAt_to_words pure_intro_entails
   stackAt_split_ge utf8_init_eq utf8_keygen_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget fitsEvents_append
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (MainCalleesROBlk617 addressSpecRO address_ro_keepsFs_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cStrAtRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (AddressEnv addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (ExitKPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitBundlePlacedBudget
  (bytes4_eq_pointsTo32RO cStrAtRO_split step_init_bundle_274_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlacedBudget
  (step_parseFail_af8_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem pool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {s' : State}
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0) (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    A.pool lim st s' = A.pool lim st s :=
  A.pool_of_vmPreserved ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

/-- Deterministic `AllocEvent` list emitted by `step_init_branch_240_placed` prior to the tail
`vptr` deallocation (`address` + `try_allocate_in` on `bs3` when `bs1 = utf8 "init"` and
`addrParse uuidParse bs2 = some peer`, else `[]`). -/
def initBranchEvents (uuidParse : UuidParser) (bs1 bs2 bs3 : List (BitVec 8)) :
    List AllocEvent :=
  if bs1 = utf8 "init" then
    match addrParse uuidParse bs2 with
    | none => []
    | some peer => rustAllocEvents peer.name.length 1 ++ rustAllocEvents bs3.length 1
  else []

/-- Exact deterministic `AllocEvent` envelope of `step_init_branch_240_placed` prior to the tail
`vptr` deallocation. -/
def InitBranchEnv (uuidParse : UuidParser) (bs1 bs2 bs3 : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  evs = initBranchEvents uuidParse bs1 bs2 bs3

set_option maxHeartbeats 800000 in
theorem step_init_branch_240_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 w3 w4 w1 : BitVec 64}
    {b0 b1 b2 b3 : BitVec 8} {bs2 bs3 : List (BitVec 8)}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ([(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] :
      List (BitVec 64 × List (BitVec 8))).map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (initBranchEvents uuidParse [b0, b1, b2, b3] bs2 bs3))
    (hs : InMainPlaced CodeOk s0 s 0x240)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
            [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
          argvAtROP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") ::
              [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (initBranchEvents uuidParse [b0, b1, b2, b3] bs2 bs3) st)) s' ∗
          Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      ((vptr ↦₆₄ p1) ∗ ((vptr + 8#64) ↦₆₄ BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ∗
        ((vptr + 16#64) ↦₆₄ p2) ∗ ((vptr + 24#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        ((vptr + 32#64) ↦₆₄ p3) ∗ ((vptr + 40#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        argsBufTail A.repAlloc vcap vptr [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") ::
            [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ Statics)
      Q Qp oom := by
  dsimp only
  have ⟨hbs3_ne, hbs3_le, _⟩ := cliInputsOk_elem hok hps
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hbs3_pos : 0 < bs3.length := List.length_pos_of_ne_nil hbs3_ne
  let wcmd : BitVec 32 := b3 ++ (b2 ++ (b1 ++ b0))
  have hwcmd : (b3 ++ b2 ++ b1 ++ b0 : BitVec 32) = wcmd := by dsimp only [wcmd]; bv_bits
  by_cases hinit : wcmd = 0x74696e69#32
  · have hcmd : [b0, b1, b2, b3] = utf8 "init" := (le32_init_iff b0 b1 b2 b3).mp hinit
    have haddr := address_ro_keepsFs_placed_ok hc
    have hres_le : resStack ≤ stk - mainFrameSize := by omega
    have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
    have hfit_addr_ev : FitsEvents M lim st (addressEvents uuidParse bs2) := by
      have hf := hfit
      simp only [initBranchEvents, hcmd, ↓reduceIte, addressEvents] at hf ⊢
      cases h : addrParse uuidParse bs2 with
      | none => trivial
      | some peer =>
        rw [h] at hf
        exact ((fitsEvents_append M lim _ _ st).mp hf).1
    dsimp only [argvAtROP]
    rw [cStrAtRO_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32RO p1 b0 b1 b2 b3, hwcmd, hinit,
      cStrAtRO_split p2 bs2, stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hres_le hsub64]
    obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    have hfsp_align0 := fsp_align_of_spAligned hsp0
    generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp hfsp_align0 ⊢
    have hfit_addr : FitsEnv M lim st (AddressEnv uuidParse ⟨fsp + 0x1b8#64, p2, bs2⟩) :=
      fun _ hevs => hevs ▸ hfit_addr_ev
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsmpl.base 580) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine main_call_keepsFs_placed (CodeOk := CodeOk) (x := (⟨fsp + 0x1b8#64, p2, bs2⟩, st))
      (k_ret := 0x268)
      (F := (vptr ↦₆₄ p1) ∗
        ((vptr + 8#64) ↦₆₄ BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ∗
        ((vptr + 16#64) ↦₆₄ p2) ∗ ((vptr + 24#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        ((vptr + 32#64) ↦₆₄ p3) ∗ ((vptr + 40#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        argsBufTail A.repAlloc vcap vptr [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
        ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗ (p1 ↦₃₂ᵣ 0x74696e69#32) ∗
        ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ↦₈ᵣ 0#8) ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗
        ((p2 + BitVec.ofNat 64 bs2.length) ↦₈ᵣ 0#8) ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ p3) ∗ cStrAtRO p3 bs3 ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        m2LocalsRest fsp ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - resStack) ∗ Statics)
      haddr hinv1
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
      (by simp only [arm64_norm, *])
      (hP := ?_)
      (hnext := ?_)
    · dsimp only [addressSpecRO]
      conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm])]
      refine Entails.trans (Entails.of_eq (by simp only [arm64_norm, hsp]; sep_ac_rfl))
        (sepConj_mono_left (pure_intro_entails
          ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], hfit_addr⟩ (Entails.refl _)))
    intro sm hin hcs hfs_m
    dsimp only [addressSpecRO]
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr_m, _, hevs⟩ => ?_
    dsimp only [AddressEnv] at hevs
    subst hevs
    let st1 := M.stepEvents (addressEvents uuidParse bs2) st
    have hx19_m : sm.readReg64 (.gpr 19#5) = buf := hcs.1.trans (by simp only [arm64_norm, *])
    have hx20_m : sm.readReg64 (.gpr 20#5) = vptr := hcs.2.1.trans (by simp only [arm64_norm, *])
    have hx23_m : sm.readReg64 (.gpr 23#5) = vcap := hcs.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx24_m : sm.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
      hcs.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx26_m : sm.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length :=
      hcs.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx27_m : sm.readReg64 (.gpr 27#5) = p3 :=
      hcs.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have htr_m' : sm.trace = s0.trace :=
      htr_m.trans ((by simp only [arm64_norm, *] : _ = s.trace).trans htr)
    have hfs_m' : sm.fs = s0.fs :=
      hfs_m.trans ((by simp only [arm64_norm, *] : _ = s.fs).trans hfs)
    obtain ⟨hpc_m, hrun_m, hsp_m, hfp_m, hinv_m, hvregs_m, _⟩ := hin
    rw [hfsp] at hsp_m
    rw [mPcPlaced_eq] at hpc_m
    simp only [arm64_norm, hsp]
    cases hparse2 : addrParse uuidParse bs2 with
    | none =>
      dsimp only
      have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
        have hneq : utf8 "init" ≠ utf8 "keygen" := by rw [utf8_init_eq, utf8_keygen_eq]; decide
        rw [← hps]
        simp only [List.map_cons, List.map_nil, parseArgs, hcmd, hneq, ↓reduceIte,
          hparse2, Option.map_none]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv_m
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      have hin2 : InMainPlaced CodeOk s0 _ 0xb54 := {
        pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
        run := by simp only [arm64_norm, *]
        sp := by simp only [arm64_norm, *]
        fp := by simp only [arm64_norm, *]
        inv := hinv2
        vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
        spAligned := hsp0 }
      have h32 : ((fsp + 440#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (fsp + 448#64) 24 ⊢ memRegion (fsp + 0x1b8#64) 32 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          (Entails.trans
            (sepConj_mono_left (pointsTo64_entails_memRegion (fsp + 0x1b8#64) 0xffffffffffffffff#64))
            (Entails.of_eq (ProofLib.memRegion_split (fsp + 0x1b8#64) 8 24 (by decide)).symm))
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_parseFail_af8_pool_placed (hookStack := hookStack) (resStack := resStack)
          (st := st1) (buf := buf) (vcap := vcap) (vptr := vptr)
          (ps := [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)])
          (Rest := (p2 ↦ᵣ bs2) ∗
            ((s0.readReg64 (.gpr 1#5)) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
            ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ᵣ p1) ∗ (p1 ↦₃₂ᵣ 0x74696e69#32) ∗
            ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ↦₈ᵣ 0#8) ∗
            ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ᵣ p2) ∗
            ((p2 + BitVec.ofNat 64 bs2.length) ↦₈ᵣ 0#8) ∗
            ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ᵣ p3) ∗ cStrAtRO p3 bs3 ∗
            ((s0.readReg64 (.gpr 1#5) + 32#64) ↦₆₄ᵣ 0#64) ∗ Statics)
          hc.allocFs hstk hstk64 hok hne hparse_none hin2
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
          hvcap (by simp only [arm64_norm, htr_m']) (by simp only [arm64_norm, hfs_m']) hexit)
      conv => arg 2; rw [pool_congr_vm A lim st1 sm (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm])]
      rw [hfsp, stackAt_split_ge fsp hres_le hsub64]
      have hloc := Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h32))))
        (locals_merge_memRegion fsp w3 w4 w1)
      rw [argsBuf_three_cons A.repAlloc (p1, [b0, b1, b2, b3]) (p2, bs2) (p3, bs3) hvcap]
      have hp_n : ∀ (P2S PL S0 M1B8 AB3 AB1 X0 C0 X1 C1 N1 X2 N2 X3 C3 X4 MS W3 W4 W1 M2 STX ST :
          SepProp),
          P2S ∗ PL ∗ S0 ∗ M1B8 ∗ (AB3 ∗ AB1 ∗ X0 ∗ C0 ∗ X1 ∗ C1 ∗ N1 ∗ X2 ∗ N2 ∗ X3 ∗ C3 ∗ X4 ∗
            MS ∗ W3 ∗ W4 ∗ W1 ∗ M2 ∗ STX ∗ ST) ⊢
            (W3 ∗ W4 ∗ W1 ∗ M1B8 ∗ M2) ∗
              (AB3 ∗ AB1 ∗ MS ∗ (STX ∗ S0) ∗ PL ∗
                (P2S ∗ X0 ∗ C0 ∗ X1 ∗ C1 ∗ N1 ∗ X2 ∗ N2 ∗ X3 ∗ C3 ∗ X4 ∗ ST)) :=
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Entails.of_eq (by sep_ac_rfl)
      exact Entails.trans (hp_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (Entails.trans (sepConj_mono_left hloc) (perm_parseFail_pre _ _ _ _ _ _ _))
    | some peer =>
      have hparse_ok : parseArgs uuidParse (i.argv.map bytesOfString) = some (.init peer bs3) := by
        have hneq : utf8 "init" ≠ utf8 "keygen" := by rw [utf8_init_eq, utf8_keygen_eq]; decide
        rw [← hps]
        simp only [List.map_cons, List.map_nil, parseArgs, hcmd, hneq, ↓reduceIte, hparse2,
          Option.map_some]
      have hfit_bs3 : FitsEvents M lim st1 (rustAllocEvents bs3.length 1) := by
        have hf := hfit
        simp only [initBranchEvents, hcmd, ↓reduceIte, hparse2] at hf
        have hst1_eq : st1 = M.stepEvents (rustAllocEvents peer.name.length 1) st := by
          dsimp only [st1, addressEvents]; rw [hparse2]
        rw [hst1_eq]
        exact ((fitsEvents_append M lim _ _ st).mp hf).2
      rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right,
        sepExists_sepConj_right]
      refine SepWPp.exists_elim fun g => ?_
      have hpure_g : ∀ (A0 B0 C0 P0 R1 R2 : SepProp),
          A0 ∗ B0 ∗ C0 ∗ (P0 ∗ R1) ∗ R2 = P0 ∗ (R1 ∗ A0 ∗ B0 ∗ C0 ∗ R2) :=
        fun _ _ _ _ _ _ => by sep_ac_rfl
      rw [hpure_g]
      refine SepWPp.pure_elim fun ⟨hgname, _, hgdev⟩ => ?_
      refine SepWPp.weaken_pre
        (sepConj_mono_left (protocolAddressAt_to_words A.repAlloc (fsp + 0x1b8#64) hgname hgdev)) ?_
      rw [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun devw => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hcap_ne => ?_
      have hcmn : (g.name.cap + 1#64 == 0#64) = false := cmn1_false hcap_ne
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x274#64) hinv_m
      wp_steps_sync_pool ((blkPl_617).base + 0x274#64)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      have hin2 : InMainPlaced CodeOk s0 _ 0x274 := {
        pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
        run := by simp only [arm64_norm, *]
        sp := by simp only [arm64_norm, *]
        fp := by simp only [arm64_norm, *]
        inv := hinv2
        vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
        spAligned := hsp0 }
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_init_bundle_274_placed (st := st1) (buf := buf) (vcap := vcap) (vptr := vptr)
          (p0 := p0) (p1 := p1) (p2 := p2) (p3 := p3) (w3 := w3) (w4 := w4) (w1 := w1)
          (devw := devw) (peer := peer) (g := g)
          (bs1 := [b0, b1, b2, b3]) (bs2 := bs2) (bs3 := bs3) (Statics := Statics)
          hc hstk hstk64 hbs3_pos hbs3_le hfit_bs3 hparse_ok hin2
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) hvcap
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (fun s' w c hp ha => by
            have hst_end : M.stepEvents (rustAllocEvents bs3.length 1) st1 =
                M.stepEvents (initBranchEvents uuidParse [b0, b1, b2, b3] bs2 bs3) st := by
              dsimp only [st1, addressEvents, initBranchEvents]
              simp only [hcmd, ↓reduceIte, hparse2]
              rw [← M.stepEvents_append]
            rw [hst_end]
            exact hnext s' w c hp ha))
      dsimp only [argvAtROP]
      rw [cStrAtRO_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32RO p1 b0 b1 b2 b3, hwcmd, hinit,
        cStrAtRO_split p2 bs2, hfsp, stackAt_split_ge fsp hres_le hsub64,
        argsBuf_three_eq A.repAlloc (p1, [b0, b1, b2, b3]) (p2, bs2) (p3, bs3) hvcap]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq (by sep_ac_rfl)
  · have hninit : [b0, b1, b2, b3] ≠ utf8 "init" := fun hc4 => hinit ((le32_init_iff ..).mpr hc4)
    have hnkey : [b0, b1, b2, b3] ≠ utf8 "keygen" := fun hc6 => by
      have hl := congrArg List.length hc6; rw [utf8_keygen_eq] at hl; simp at hl
    have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
      rw [← hps]; exact parseArgs_three_bad_cmd uuidParse [b0, b1, b2, b3] bs2 bs3 hnkey hninit
    have hinit_neq : (wcmd == 0x74696e69#32) = false := beq_false_of_ne hinit
    dsimp only [argvAtROP]
    rw [cStrAtRO_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32RO p1 b0 b1 b2 b3, hwcmd]
    obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp ⊢
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
    wp_steps
    wp_step
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0xb54 := {
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, *]
      sp := by simp only [arm64_norm, *]
      fp := by simp only [arm64_norm, *]
      inv := hinv1
      vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
      spAligned := hsp0 }
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_parseFail_af8_pool_placed (hookStack := hookStack) (resStack := resStack)
        (st := st) (buf := buf) (vcap := vcap) (vptr := vptr)
        (ps := [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)])
        (Rest := ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
          ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗
          (p1 ↦₃₂ᵣ wcmd) ∗
          ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ↦₈ᵣ 0#8) ∗
          ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗ cStrAtRO p2 bs2 ∗
          ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ p3) ∗ cStrAtRO p3 bs3 ∗
          ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗ Statics)
        hc.allocFs hstk hstk64 hok hne hparse_none hin1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hexit)
    conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm])]
    rw [hfsp, argsBuf_three_cons A.repAlloc (p1, [b0, b1, b2, b3]) (p2, bs2) (p3, bs3) hvcap]
    let LOC : SepProp :=
      ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp
    let REST : SepProp :=
      ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
      ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗
      (p1 ↦₃₂ᵣ wcmd) ∗ ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ↦₈ᵣ 0#8) ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗ cStrAtRO p2 bs2 ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ p3) ∗ cStrAtRO p3 bs3 ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗ Statics
    refine Entails.trans
      (Q := LOC ∗ (argsBuf A.repAlloc vcap vptr [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ REST))
      (Entails.of_eq (by dsimp only [LOC, REST]; sep_ac_rfl))
      (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 w4 w1))
        (perm_parseFail_pre _ _ _ _ _ _ _))

theorem step_init_branch_240_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 w3 w4 w1 : BitVec 64}
    {b0 b1 b2 b3 : BitVec 8} {bs2 bs3 : List (BitVec 8)}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ([(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] :
      List (BitVec 64 × List (BitVec 8))).map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (initBranchEvents uuidParse [b0, b1, b2, b3] bs2 bs3))
    (hs : InMainPlaced CodeOk s0 s 0x240)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
            [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
          argvAtROP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") ::
              [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (initBranchEvents uuidParse [b0, b1, b2, b3] bs2 bs3) st)) s' ∗
          Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      ((vptr ↦₆₄ p1) ∗ ((vptr + 8#64) ↦₆₄ BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ∗
        ((vptr + 16#64) ↦₆₄ p2) ∗ ((vptr + 24#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        ((vptr + 32#64) ↦₆₄ p3) ∗ ((vptr + 40#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        argsBufTail A.repAlloc vcap vptr [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") ::
            [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ Statics)
      Q Qp oom :=
  step_init_branch_240_pool_placed hc hstk hstk64 hok hne hps hfit hs hx19 hx20 hx23 hx24
    hvcap htr hfs (exitKPoolPlaced_of_exitKPlaced hexit) hnext

theorem step_init_branch_240_placed_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 w3 w4 w1 : BitVec 64}
    {b0 b1 b2 b3 : BitVec 8} {bs2 bs3 : List (BitVec 8)}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ([(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] :
      List (BitVec 64 × List (BitVec 8))).map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (initBranchEvents uuidParse [b0, b1, b2, b3] bs2 bs3))
    (hs : InMainPlaced CodeOk s0 s 0x240)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (st' : M.σ) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
            [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
          argvAtROP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") ::
              [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      ((vptr ↦₆₄ p1) ∗ ((vptr + 8#64) ↦₆₄ BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ∗
        ((vptr + 16#64) ↦₆₄ p2) ∗ ((vptr + 24#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        ((vptr + 32#64) ↦₆₄ p3) ∗ ((vptr + 40#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        argsBufTail A.repAlloc vcap vptr [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)] ∗
        argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") ::
            [(p1, [b0, b1, b2, b3]), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ Statics)
      Q Qp oom :=
  step_init_branch_240_placed hc hstk hstk64 hok hne hps hfit hs hx19 hx20 hx23 hx24
    hvcap htr hfs hexit fun s' w' c' hp ha => hnext s' _ w' c' hp ha

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitPlacedBudget
