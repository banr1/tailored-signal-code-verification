/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitBundlePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.RecvArmPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendArmPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendRecvPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.Pure
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `send` / `recv` Dispatch (`M+0x2f4`, Block `617`)

Verifies `main`'s 2-argument subcommand dispatch at `M+0x2f4` with read-only `argvAtROP` and
`RustCliAllocBudget M`, routing `"send"` (`M+0x360`), `"recv"` (`M+0x32c`), or invalid 2-argument
commands (`exit 2` at `M+0xb54`) under `SendRecvEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendRecvPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (CliInputsOk utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtCallPlaced AtM2DispatchPlaced CallV CallW InMainPlaced LsCodeInv argsBuf
   callCellsPlaced callHeap locals mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize mainSaved
   parseArgs sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.Proofs
  (argsBuf_two_eq cliInputsOk_elem le32_recv_iff le32_send_iff
   locals_merge_memRegion locals_split_m2 m2LocalsRest parseArgs_two_bad_cmd perm_parseFail_pre
   utf8_recv_eq utf8_send_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (MainCalleesROBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cStrAtRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (ExitKPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitBundlePlacedBudget
  (bytes4_eq_pointsTo32RO cStrAtRO_split)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.RecvArmPlacedBudget
  (step_recv_arm_32c_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendArmPlacedBudget
  (step_send_arm_35c_pool_placed)
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

private theorem ps_two_of_map {i : Inputs} {ps : List (BitVec 64 × List (BitVec 8))}
    (hn : i.argv.length = 2) (hps : ps.map (·.2) = i.argv.map bytesOfString) :
    ∃ a1 a2 p1 bs1 p2 bs2,
      i.argv = [a1, a2] ∧ ps = [(p1, bs1), (p2, bs2)] ∧
      bs1 = bytesOfString a1 ∧ bs2 = bytesOfString a2 := by
  generalize hargv : i.argv = argv at hn hps ⊢
  rcases argv with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩ <;>
    rcases ps with _ | ⟨⟨p1, bs1⟩, _ | ⟨⟨p2, bs2⟩, _ | _⟩⟩ <;>
    simp_all

private theorem list_len_four {α : Type} {l : List α} (h : l.length = 4) :
    ∃ b0 b1 b2 b3, l = [b0, b1, b2, b3] := by
  match l with
  | [b0, b1, b2, b3] => exact ⟨b0, b1, b2, b3, rfl⟩
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => simp at h

/-- Deterministic `AllocEvent` list emitted by `step_send_recv_2f4_placed` prior to the tail
`vptr` deallocation (`addressEvents uuidParse bs2` when `args = [bs1, bs2]` with
`bs1 = utf8 "send"` or `bs1 = utf8 "recv"`, else `[]`). -/
def sendRecvEvents (uuidParse : UuidParser) (args : List (List (BitVec 8))) :
    List AllocEvent :=
  match args with
  | [bs1, bs2] =>
    if bs1 = utf8 "send" ∨ bs1 = utf8 "recv" then addressEvents uuidParse bs2 else []
  | _ => []

/-- Exact deterministic `AllocEvent` envelope of `step_send_recv_2f4_placed` prior to the tail
`vptr` deallocation. -/
def SendRecvEnv (uuidParse : UuidParser) (args : List (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  evs = sendRecvEvents uuidParse args

set_option maxHeartbeats 800000 in
theorem step_send_recv_2f4_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ []) (hn : i.argv.length = 2)
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (sendRecvEvents uuidParse (i.argv.map bytesOfString)))
    (hs : AtM2DispatchPlaced CodeOk s0 s i.argv.length buf vcap vptr)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (sendRecvEvents uuidParse (i.argv.map bytesOfString)) st)) s' ∗
          Statics)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc vcap vptr ps ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom := by
  obtain ⟨a1, a2, p1, bs1, p2, bs2, _, rfl, _, _⟩ := ps_two_of_map hn hps
  have ⟨_, hbs1_le, _⟩ := cliInputsOk_elem hok hps (List.mem_cons_self ..)
  obtain ⟨hbase, _, hx19, hx20, _, hx23, hx24, hvcap, htr, hfs⟩ := hs
  simp only [hn, ↓reduceIte] at hbase
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hbase
  rw [mPcPlaced_eq] at hpc
  rw [argsBuf_two_eq A.repAlloc (p1, bs1) (p2, bs2) hvcap,
    locals_split_m2 (s0.sp - BitVec.ofNat 64 mainFrameSize)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w1 => ?_
  by_cases hlen4 : bs1.length = 4
  · obtain ⟨b0, b1, b2, b3, rfl⟩ := list_len_four hlen4
    let wcmd : BitVec 32 := b3 ++ (b2 ++ (b1 ++ b0))
    have hwcmd : (b3 ++ b2 ++ b1 ++ b0 : BitVec 32) = wcmd := by dsimp only [wcmd]; bv_bits
    by_cases hsend : wcmd = 0x646e6573#32
    · dsimp only [argvAtROP]
      rw [cStrAtRO_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32RO p1 b0 b1 b2 b3, hwcmd, hsend]
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x360#64) hinv
      wp_steps
      wp_step
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv1
      have hcmd : [b0, b1, b2, b3] = utf8 "send" := (le32_send_iff b0 b1 b2 b3).mp hsend
      have hev_eq : sendRecvEvents uuidParse (i.argv.map bytesOfString) =
          addressEvents uuidParse bs2 := by
        rw [← hps]
        simp only [List.map_cons, List.map_nil, sendRecvEvents, hcmd, true_or, ↓reduceIte]
      have hfit_addr : FitsEvents M lim st (addressEvents uuidParse bs2) := hev_eq ▸ hfit
      have hin1 : InMainPlaced CodeOk s0 _ 0x360 := {
        pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
        run := by simp only [arm64_norm, *]
        sp := by simp only [arm64_norm, *]
        fp := by simp only [arm64_norm, *]
        inv := hinv1
        vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
        spAligned := hsp0 }
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_send_arm_35c_pool_placed (st := st) (buf := buf) (vcap := vcap) (vptr := vptr)
          (p0 := p0) (p1 := p1) (p2 := p2) (w3 := w3) (w4 := w4) (w1 := w1)
          (bs1 := [b0, b1, b2, b3]) (bs2 := bs2) (Statics := Statics)
          hc hstk hstk64 hok hne hps hcmd hfit_addr hin1
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          hexit (fun s' w c hp ha => by rw [← hev_eq]; exact hnext s' w c hp ha))
      dsimp only [argvAtROP]
      conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm])]
      rw [cStrAtRO_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32RO p1 b0 b1 b2 b3, hwcmd, hsend]
      exact Entails.of_eq (by sep_ac_rfl)
    · have hsend_neq : (wcmd == 0x646e6573#32) = false := beq_false_of_ne hsend
      have hnot_send : [b0, b1, b2, b3] ≠ utf8 "send" := fun hc4 => hsend ((le32_send_iff ..).mpr hc4)
      by_cases hrecv : wcmd = 0x76636572#32
      · dsimp only [argvAtROP]
        rw [cStrAtRO_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32RO p1 b0 b1 b2 b3, hwcmd, hrecv]
        rw [mProgPlaced_eq]
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x32c#64) hinv
        wp_steps
        wp_step
        wp_steps
        wp_step
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hinv1
        have hcmd : [b0, b1, b2, b3] = utf8 "recv" := (le32_recv_iff b0 b1 b2 b3).mp hrecv
        have hev_eq : sendRecvEvents uuidParse (i.argv.map bytesOfString) =
            addressEvents uuidParse bs2 := by
          rw [← hps]
          simp only [List.map_cons, List.map_nil, sendRecvEvents, hcmd, or_true, ↓reduceIte]
        have hfit_addr : FitsEvents M lim st (addressEvents uuidParse bs2) := hev_eq ▸ hfit
        have hin1 : InMainPlaced CodeOk s0 _ 0x32c := {
          pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
          run := by simp only [arm64_norm, *]
          sp := by simp only [arm64_norm, *]
          fp := by simp only [arm64_norm, *]
          inv := hinv1
          vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
          spAligned := hsp0 }
        rw [← mProgPlaced_eq]
        refine SepWPp.weaken_pre ?_
          (step_recv_arm_32c_pool_placed (st := st) (buf := buf) (vcap := vcap) (vptr := vptr)
            (p0 := p0) (p1 := p1) (p2 := p2) (w3 := w3) (w4 := w4) (w1 := w1)
            (bs1 := [b0, b1, b2, b3]) (bs2 := bs2) (Statics := Statics)
            hc hstk hstk64 hok hne hps hcmd hfit_addr hin1
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hexit (fun s' w c hp ha => by rw [← hev_eq]; exact hnext s' w c hp ha))
        dsimp only [argvAtROP]
        conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm])]
        rw [cStrAtRO_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32RO p1 b0 b1 b2 b3, hwcmd, hrecv]
        exact Entails.of_eq (by sep_ac_rfl)
      · have hnot_recv : [b0, b1, b2, b3] ≠ utf8 "recv" := fun hc4 => hrecv ((le32_recv_iff ..).mpr hc4)
        have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
          rw [← hps]; exact parseArgs_two_bad_cmd uuidParse [b0, b1, b2, b3] bs2 hnot_send hnot_recv
        have hrecv_neq : (wcmd == 0x76636572#32) = false := beq_false_of_ne hrecv
        dsimp only [argvAtROP]
        rw [cStrAtRO_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32RO p1 b0 b1 b2 b3, hwcmd]
        generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp ⊢
        rw [mProgPlaced_eq]
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
        wp_steps
        wp_step
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
            (ps := [(p1, [b0, b1, b2, b3]), (p2, bs2)])
            (Rest := ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
              ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗ (p1 ↦₃₂ᵣ wcmd) ∗
              ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ↦₈ᵣ 0#8) ∗
              ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗ cStrAtRO p2 bs2 ∗
              ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗ Statics)
            hc.allocFs hstk hstk64 hok hne hparse_none hin1
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hexit)
        conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm])]
        rw [hfsp, ← argsBuf_two_eq A.repAlloc (p1, [b0, b1, b2, b3]) (p2, bs2) hvcap]
        let LOC : SepProp :=
          ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
            memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp
        let REST : SepProp :=
          ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
            ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗ (p1 ↦₃₂ᵣ wcmd) ∗
            ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3] : List (BitVec 8)).length) ↦₈ᵣ 0#8) ∗
            ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗ cStrAtRO p2 bs2 ∗
            ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗ Statics
        refine Entails.trans
          (Q := LOC ∗ (argsBuf A.repAlloc vcap vptr [(p1, [b0, b1, b2, b3]), (p2, bs2)] ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
              [(p1, [b0, b1, b2, b3]), (p2, bs2)] ∗
            mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ REST))
          (Entails.of_eq (by dsimp only [LOC, REST]; sep_ac_rfl))
          (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 w4 w1))
            (perm_parseFail_pre _ _ _ _ _ _ _))
  · have hnot_send : bs1 ≠ utf8 "send" := fun hc4 => hlen4 (by rw [hc4, utf8_send_eq]; rfl)
    have hnot_recv : bs1 ≠ utf8 "recv" := fun hc4 => hlen4 (by rw [hc4, utf8_recv_eq]; rfl)
    have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
      rw [← hps]; exact parseArgs_two_bad_cmd uuidParse bs1 bs2 hnot_send hnot_recv
    have hbs1_lt : bs1.length < 2 ^ 64 := by dsimp only at hbs1_le; omega
    have hlen_beq : (BitVec.ofNat 64 bs1.length == 4#64) = false := by
      apply beq_false_of_ne; intro heq
      have htn := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs1_lt] at htn
      exact hlen4 htn
    generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp ⊢
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
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
        (ps := [(p1, bs1), (p2, bs2)])
        (Rest := argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2)]) ∗ Statics)
        hc.allocFs hstk hstk64 hok hne hparse_none hin1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hexit)
    conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm])]
    rw [hfsp, ← argsBuf_two_eq A.repAlloc (p1, bs1) (p2, bs2) hvcap]
    let LOC : SepProp :=
      ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp
    let REST : SepProp :=
      argvAtROP (s0.readReg64 .x1)
        ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2)]) ∗ Statics
    refine Entails.trans
      (Q := LOC ∗ (argsBuf A.repAlloc vcap vptr [(p1, bs1), (p2, bs2)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2)] ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ REST))
      (Entails.of_eq (by dsimp only [LOC, REST]; sep_ac_rfl))
      (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 w4 w1))
        (perm_parseFail_pre _ _ _ _ _ _ _))

theorem step_send_recv_2f4_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ []) (hn : i.argv.length = 2)
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (sendRecvEvents uuidParse (i.argv.map bytesOfString)))
    (hs : AtM2DispatchPlaced CodeOk s0 s i.argv.length buf vcap vptr)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (sendRecvEvents uuidParse (i.argv.map bytesOfString)) st)) s' ∗
          Statics)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc vcap vptr ps ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  step_send_recv_2f4_pool_placed hc hstk hstk64 hok hne hn hps hfit hs
    (exitKPoolPlaced_of_exitKPlaced hexit) hnext

theorem step_send_recv_2f4_pool_placed_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ []) (hn : i.argv.length = 2)
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (sendRecvEvents uuidParse (i.argv.map bytesOfString)))
    (hs : AtM2DispatchPlaced CodeOk s0 s i.argv.length buf vcap vptr)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (st' : M.σ) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ Statics)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc vcap vptr ps ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  step_send_recv_2f4_pool_placed hc hstk hstk64 hok hne hn hps hfit hs hexit
    fun s' w' c' hp ha => hnext s' _ w' c' hp ha

theorem step_send_recv_2f4_placed_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ []) (hn : i.argv.length = 2)
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (sendRecvEvents uuidParse (i.argv.map bytesOfString)))
    (hs : AtM2DispatchPlaced CodeOk s0 s i.argv.length buf vcap vptr)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (st' : M.σ) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ Statics)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc vcap vptr ps ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  step_send_recv_2f4_pool_placed_any_st hc hstk hstk64 hok hne hn hps hfit hs
    (exitKPoolPlaced_of_exitKPlaced hexit) hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendRecvPlacedBudget
