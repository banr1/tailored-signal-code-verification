/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendRecvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.Pure
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `main` M2 Dispatch (`M+0x2f4 / M+0x1b0 → M+0x568 / M+0xb80`)

Verifies the subcommand dispatch half of `main_m2` on Block `617` with read-only `argvAtROP` and
`RustCliAllocBudget M` across `send`, `recv`, `init`, `keygen`, and invalid-CLI parse failures
(`exit 2`) under `M2DispatchEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlacedBudget

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
  (argsBuf_three_eq argvFits_bounds cliInputsOk_elem list_len_four list_len_six
   locals_merge_memRegion locals_nil locals_split_m2 m2LocalsRest parseArgs_len_ne
   parseArgs_three_bad_cmd perm_parseFail_pre ps_three_of_map utf8_init_eq utf8_keygen_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (MainCalleesROBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (ExitKPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitPlacedBudget
  (initBranchEvents step_init_branch_240_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenPlacedBudget
  (keygenBranchEvents step_keygen_cmd_1cc_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendRecvPlacedBudget
  (sendRecvEvents step_send_recv_2f4_pool_placed)
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

/-- Exact deterministic `AllocEvent` list emitted during `main`'s `M2` dispatch phase prior to the
tail `vptr` deallocation (`rustDeallocEvents (vcap.toNat * 16) 8`). -/
def m2DispatchEvents (uuidParse : UuidParser) (args : List (List (BitVec 8))) :
    List AllocEvent :=
  match args with
  | [bs1, bs2] => sendRecvEvents uuidParse [bs1, bs2]
  | [bs1, bs2, bs3] =>
    if bs1.length = 4 then initBranchEvents uuidParse bs1 bs2 bs3
    else if bs1.length = 6 then keygenBranchEvents uuidParse bs1 bs2
    else []
  | _ => []

/-- Exact deterministic `AllocEvent` envelope for `main`'s `M2` dispatch phase prior to the tail
`vptr` deallocation. -/
def M2DispatchEnv (uuidParse : UuidParser) (args : List (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  evs = m2DispatchEvents uuidParse args

set_option maxHeartbeats 800000 in
theorem main_m2_dispatch_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (m2DispatchEvents uuidParse (i.argv.map bytesOfString)))
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
              (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString)) st)) s' ∗
          Statics)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc vcap vptr ps ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom := by
  by_cases hn2 : i.argv.length = 2
  · have hev2 : m2DispatchEvents uuidParse (i.argv.map bytesOfString) =
        sendRecvEvents uuidParse (i.argv.map bytesOfString) := by
      rcases ha : i.argv with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩ <;> simp_all [m2DispatchEvents]
    exact step_send_recv_2f4_pool_placed hc hstk hstk64 hok hne hn2 hps (hev2 ▸ hfit) hs hexit
      (fun s' w c hp ha => by rw [← hev2]; exact hnext s' w c hp ha)
  · obtain ⟨hbase, _, hx19, hx20, hx21, hx23, hx24, hvcap, htr, hfs⟩ := hs
    simp only [hn2, ↓reduceIte] at hbase
    have hlen_le : i.argv.length ≤ 1820 := (argvFits_bounds hok.2).1
    by_cases hn3 : i.argv.length = 3
    · obtain ⟨p1, bs1, p2, bs2, p3, bs3, rfl⟩ := ps_three_of_map hn3 hps
      have ⟨_, hbs1_le, _⟩ := cliInputsOk_elem hok hps (List.mem_cons_self ..)
      rw [locals_split_m2 (s0.sp - BitVec.ofNat 64 mainFrameSize)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun w3 =>
        SepWPp.exists_elim fun w4 =>
        SepWPp.exists_elim fun w1 => ?_
      rw [argsBuf_three_eq A.repAlloc (p1, bs1) (p2, bs2) (p3, bs3) hvcap]
      obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hbase
      rw [mPcPlaced_eq] at hpc
      rw [mProgPlaced_eq]
      by_cases hl4 : bs1.length = 4
      · obtain ⟨b0, b1, b2, b3, rfl⟩ := list_len_four hl4
        have hev_init : m2DispatchEvents uuidParse (i.argv.map bytesOfString) =
            initBranchEvents uuidParse [b0, b1, b2, b3] bs2 bs3 := by
          rw [← hps]; rfl
        have hfit_init : FitsEvents M lim st
            (initBranchEvents uuidParse [b0, b1, b2, b3] bs2 bs3) := hev_init ▸ hfit
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x240#64) hinv
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *, hn3]) (by simp only [arm64_norm, *])
        intro hinv1
        rw [← mProgPlaced_eq]
        refine SepWPp.weaken_pre ?_
          (step_init_branch_240_pool_placed (st := st) (buf := buf) (vcap := vcap) (vptr := vptr)
            (p0 := p0) (p1 := p1) (p2 := p2) (p3 := p3) (w3 := w3) (w4 := w4) (w1 := w1)
            (Statics := Statics)
            hc hstk hstk64 hok hne hps hfit_init
            ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *, hn3],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], hinv1,
             by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
            (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
            (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
            hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs])
            hexit (fun s' w c hp ha => by rw [← hev_init]; exact hnext s' w c hp ha))
        dsimp only
        conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm])]
        exact Entails.of_eq (by sep_ac_rfl)
      · have hbs1_lt : bs1.length < 2 ^ 64 := by dsimp only at hbs1_le; omega
        have hne4 : (BitVec.ofNat 64 bs1.length == 4#64) = false := by
          apply beq_false_of_ne; intro h; have htn := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs1_lt] at htn; exact hl4 htn
        have hne4' : (BitVec.ofNat 64 bs1.length != 4#64) = true := by simp only [bne, hne4]; rfl
        by_cases hl6 : bs1.length = 6
        · obtain ⟨b0, b1, b2, b3, b4, b5, rfl⟩ := list_len_six hl6
          have hev_kg : m2DispatchEvents uuidParse (i.argv.map bytesOfString) =
              keygenBranchEvents uuidParse [b0, b1, b2, b3, b4, b5] bs2 := by
            rw [← hps]; rfl
          have hfit_kg : FitsEvents M lim st
              (keygenBranchEvents uuidParse [b0, b1, b2, b3, b4, b5] bs2) := hev_kg ▸ hfit
          apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x1cc#64) hinv
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *, hn3]) (by simp only [arm64_norm, *])
          intro hinv1
          rw [← mProgPlaced_eq]
          refine SepWPp.weaken_pre ?_
            (step_keygen_cmd_1cc_pool_placed (st := st) (buf := buf) (vcap := vcap) (vptr := vptr)
              (p0 := p0) (p1 := p1) (p2 := p2) (p3 := p3) (w3 := w3) (w4 := w4) (w1 := w1)
              (Statics := Statics)
              hc hstk hstk64 hok hne hn3 hps hfit_kg
              ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *, hn3],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], hinv1,
               by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
              (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
              (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
              hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs])
              hexit (fun s' w c hp ha => by rw [← hev_kg]; exact hnext s' w c hp ha))
          dsimp only
          conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (fun _ => by simp only [arm64_norm])]
          rw [← argsBuf_three_eq A.repAlloc (p1, [b0, b1, b2, b3, b4, b5]) (p2, bs2) (p3, bs3) hvcap]
          exact Entails.of_eq (by sep_ac_rfl)
        · have hne6 : (BitVec.ofNat 64 bs1.length == 6#64) = false := by
            apply beq_false_of_ne; intro h; have htn := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs1_lt] at htn; exact hl6 htn
          have hne6' : (BitVec.ofNat 64 bs1.length != 6#64) = true := by simp only [bne, hne6]; rfl
          have hnkey : bs1 ≠ utf8 "keygen" := fun hc6 =>
            hl6 ((congrArg List.length hc6).trans (by rw [utf8_keygen_eq]; rfl))
          have hninit : bs1 ≠ utf8 "init" := fun hc4 =>
            hl4 ((congrArg List.length hc4).trans (by rw [utf8_init_eq]; rfl))
          have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
            rw [← hps]; exact parseArgs_three_bad_cmd uuidParse bs1 bs2 bs3 hnkey hninit
          generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp ⊢
          apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *, hn3]) (by simp only [arm64_norm, *])
          intro hinv1
          have hin1 : InMainPlaced CodeOk s0 _ 0xb54 := {
            pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *, hn3]
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
              (ps := [(p1, bs1), (p2, bs2), (p3, bs3)])
              (Rest := argvAtROP (s0.readReg64 .x1)
                ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
                Statics)
              hc.allocFs hstk hstk64 hok hne hparse_none hin1
              (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
              (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
              hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs]) hexit)
          conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (fun _ => by simp only [arm64_norm])]
          rw [hfsp, ← argsBuf_three_eq A.repAlloc (p1, bs1) (p2, bs2) (p3, bs3) hvcap]
          let LOC : SepProp :=
            ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
              memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp
          let REST : SepProp :=
            argvAtROP (s0.readReg64 .x1)
              ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗ Statics
          refine Entails.trans
            (Q := LOC ∗ (argsBuf A.repAlloc vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
              argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
                [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
              mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ REST))
            (Entails.of_eq (by dsimp only [LOC, REST]; sep_ac_rfl))
            (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 w4 w1))
              (perm_parseFail_pre _ _ _ _ _ _ _))
    · have hlen_lt : i.argv.length < 2 ^ 64 := by omega
      have hne3_bv : (BitVec.ofNat 64 i.argv.length == 3#64) = false := by
        apply beq_false_of_ne; intro h; have htn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt] at htn; exact hn3 htn
      have hne3_bv' : (BitVec.ofNat 64 i.argv.length != 3#64) = true := by simp only [bne, hne3_bv]; rfl
      have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none :=
        parseArgs_len_ne uuidParse _ (by simp [hn2]) (by simp [hn3])
      rw [locals_nil]
      obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hbase
      rw [mPcPlaced_eq] at hpc
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
          (st := st) (buf := buf) (vcap := vcap) (vptr := vptr) (ps := ps)
          (Rest := argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗ Statics)
          hc.allocFs hstk hstk64 hok hne hparse_none hin1
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
          hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs]) hexit)
      conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm])]
      exact Entails.of_eq (by sep_ac_rfl)

theorem main_m2_dispatch_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (m2DispatchEvents uuidParse (i.argv.map bytesOfString)))
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
              (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString)) st)) s' ∗
          Statics)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc vcap vptr ps ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  main_m2_dispatch_pool_placed hc hstk hstk64 hok hne hps hfit hs
    (exitKPoolPlaced_of_exitKPlaced hexit) hnext

theorem main_m2_dispatch_pool_placed_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (m2DispatchEvents uuidParse (i.argv.map bytesOfString)))
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
      (argsBuf A.repAlloc vcap vptr ps ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  main_m2_dispatch_pool_placed hc hstk hstk64 hok hne hps hfit hs hexit
    fun s' w' c' hp ha => hnext s' _ w' c' hp ha

theorem main_m2_dispatch_placed_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (m2DispatchEvents uuidParse (i.argv.map bytesOfString)))
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
      (argsBuf A.repAlloc vcap vptr ps ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  main_m2_dispatch_pool_placed_any_st hc hstk hstk64 hok hne hps hfit hs
    (exitKPoolPlaced_of_exitKPlaced hexit) hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlacedBudget
