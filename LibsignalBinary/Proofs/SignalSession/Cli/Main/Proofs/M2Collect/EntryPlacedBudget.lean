/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Frame
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `main` M2 Collect Entry (`M+0xc0 .. M+0x11c / M+0x1ac`)

Verifies the initial `from_utf8`, allocator shim, and `__rust_alloc(64, 8)` setup of `main`'s
`Vec<&str>` collection on Block `617` with read-only `argvAtROP` and `RustCliAllocBudget M`,
threading `A.pool` and `M2CollectEnv` into the collection loop.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (vecHeader)
open CryptoVerification.SignalSession
  (lsFromUtf8Sym lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkLib_eq_617 blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv argsBuf argsBufRest argsBuf_focus argsBuf_init_cap4 fsp_spAligned locals
   locals_nil_split_m2 mainFrameSize mainSaved main_call_rocl memRegion_24_words ofNat_beq_ofNat
   sepWPp_seq_codeOk stackAt_split_ge' words_to_memRegion_24)
open CryptoVerification.SignalSession.Cli.MainHops.M2Entry (memRegion_64_head_words)
open CryptoVerification.SignalSession.Cli.MainHops.M2Steps
  (calleeSavedVRegs_preserve cs_fp cs_x19 cs_x21 cs_x22 cs_x23 cs_x24 cs_x25 fspOf
   sepWPp_exists_elim sepWPp_mono_pre sepWPp_pure_elim)
open CryptoVerification.SignalSession.Cli.MainHops.M2StepsPlaced (M2FramePlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents NullAllowed OomPreserved
   RustCliAllocBudget RustLayoutOk SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (fromUtf8AsciiSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlacedBudget
  (M2CollectLoopEnv M2EnvPlaced argvAtROPRest argvAtROP_focus m2LoopMem m2LoopRest
   step_collect_loop_placed)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem sepWPp_seq_codeOk_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_617).rebase (blkPl_617).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm =>
          ∀ m_real : Memory,
            ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            CodeOk (sm'.setMem m_real).mem →
            SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret (sm'.setMem m_real) Pm Q Qp oom)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s Pre Q Qp oom := by
  refine sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := mid) hinv ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_617).rebase (blkPl_617).base (hooksException H))
    blkLib_eq_617 (mid := mid)
  intro m_strip
  refine SepWP.mono (hseg m_strip) fun sm' Pm hpc_m' hrun_m' hcont m_real hnsp => ?_
  exact SepWP.done hpc_m' hrun_m' (hcont m_real hnsp)

private theorem entail_with_frame_p (F : SepProp) {A B P Q : SepProp}
    (hAB : A ⊢ B)
    (hP : P = A ∗ F := by
      simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]; try sep_ac_rfl)
    (hQ : B ∗ F = Q := by
      simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]; try sep_ac_rfl) :
    P ⊢ Q := by
  rw [hP, ← hQ]
  exact sepConj_mono_left hAB

private theorem sepWPp_mono_pre_sp_pool {prog : Program} {target_pc : BitVec 64} {s : State}
    {fsp : BitVec 64} {P : SepProp} {F : BitVec 64 → State → SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hsp : s.sp = fsp) (hP : P ⊢ F fsp s)
    (h : SepWPp prog target_pc s (F s.sp s) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  apply sepWPp_mono_pre (P' := F s.sp s)
  · rw [hsp]; exact hP
  · exact h

/-- Full allocation-event envelope of `M2Collect`: initial `__rust_alloc(64, 8)` for the
    4-element `Vec<&str>` buffer followed by `M2CollectLoopEnv n 1` across loop iterations. -/
def M2CollectEnv (n : Nat) : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 64 8) (M2CollectLoopEnv n 1)

theorem M2CollectEnv.alloc_only (n : Nat) : M2CollectEnv n (rustAllocEvents 64 8) :=
  SeqEnv.inl rfl

theorem M2CollectEnv.alloc_then_loop {n : Nat} {evs : List AllocEvent}
    (h : M2CollectLoopEnv n 1 evs) : M2CollectEnv n (rustAllocEvents 64 8 ++ evs) :=
  Or.inr ⟨rustAllocEvents 64 8, evs, rfl, rfl, h⟩

set_option maxHeartbeats 800000 in
/-- Post-`__rust_alloc(64, 8)` continuation at `M+0x0ec` on Block `617` (non-null allocation). -/
theorem step_collect_post_alloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st1 : M.σ}
    {s0 sf3 : State} {ret : BitVec 64} {stk hookStack resStack n : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A lim hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hn1_le : 1 ≤ n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hascii : ∀ k (hk : k < ps.length), ∀ b ∈ ps[k].2, b.toNat < 128)
    (hfit_loop : 1 < n → FitsEnv M lim st1 (M2CollectLoopEnv n 1))
    (hsp0 : s0.spAligned = true)
    (hpc3 : sf3.pc = (blkPl_617).base + 0x0ec#64) (hrun3 : sf3.status = .Running)
    (hsp3_eq : sf3.sp = fspOf s0) (hfp_3 : sf3.readReg64 .fp = s0.sp - 0x60#64)
    (hinv6 : CodeOk sf3.mem) (hvregs_3 : calleeSavedVRegs sf3 = calleeSavedVRegs s0)
    (hx19_3 : sf3.readReg64 (.gpr 19#5) = buf)
    (hx21_3 : sf3.readReg64 (.gpr 21#5) = (ps[0]'(by omega)).1)
    (hx22_3 : sf3.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n))
    (hx23_3 : sf3.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (ps[0]'(by omega)).2.length)
    (hx24_3 : sf3.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25_3 : sf3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n)
    (htr3 : sf3.trace = s0.trace) (hfs3 : sf3.fs = s0.fs)
    (hv0 : sf3.readReg64 .x0 ≠ 0#64)
    (hnext : ∀ (s' : State) (vcap vptr : BitVec 64) (evs : List AllocEvent),
      M2CollectLoopEnv n 1 evs →
      M2FramePlaced CodeOk s0 s' (if n = 2 then 0x2f4 else 0x1b0) →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = vptr →
      s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 23#5) = vcap →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      vcap ≠ 0#64 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (argsBuf A.repAlloc vcap vptr ps ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st1) s' ∗ Statics) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sf3
      (A.live (sf3.readReg64 .x0) 64 8 ∗ memRegion (sf3.readReg64 .x0) 64 ∗
        A.pool lim st1 sf3 ∗ stackAt (fspOf s0) extHookStack ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        memRegion (fspOf s0) 0x1b8 ∗
        memRegion (fspOf s0 + 0x1b8#64) 24 ∗
        memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
        memRegion (fspOf s0 + 0x310#64) 24 ∗
        memRegion (fspOf s0 + 0x328#64) 0x158 ∗
        mainSaved s0 ∗
        memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
        Statics) Q Qp oom := by
  have h0_ps : 0 < ps.length := by omega
  have hs3_aligned : sf3.spAligned = true := fsp_spAligned hsp0 hsp3_eq
  have hsp0_keep : Unit → s0.spAligned = true := fun () => hsp0
  clear hsp0
  have hstk_ext := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := extHookStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  let vptr0 : BitVec 64 := sf3.readReg64 .x0
  have hv0_beq : (vptr0 == 0#64) = false := beq_eq_false_iff_ne.mpr hv0
  apply sepWPp_mono_pre
    (P' := A.live vptr0 64 8 ∗ memRegion vptr0 64 ∗
      memRegion (sf3.sp + 0x310#64) 24 ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 0x1b8#64) 24 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗ memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool lim st1 sf3 ∗ Statics)
  · simp only [wp_norm, arm64_norm, hsp3_eq]
    rw [hstk_ext]
    apply Entails.of_eq
    simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]
    try sep_ac_rfl
  rw [memRegion_64_head_words vptr0, memRegion_24_words (sf3.sp + 0x310#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  refine sepWPp_exists_elim fun hw0 => sepWPp_exists_elim fun hw1 =>
    sepWPp_exists_elim fun hdr0 => sepWPp_exists_elim fun hdr1 =>
    sepWPp_exists_elim fun hdr2 => ?_
  simp only [wp_norm, arm64_norm, hsp3_eq]
  have hcmp1 : (BitVec.ofNat 64 n == 1#64) = decide (n = 1) :=
    ofNat_beq_ofNat (by omega) (by decide)
  have htake1 : [ps[0]] = ps.take 1 := by
    cases ps with
    | nil => simp at h0_ps
    | cons _ _ => rfl
  by_cases hn1 : n = 1
  · refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 0x1a8#64) hinv6 fun _m_strip => ?_
    wp_step; wp_steps
    apply SepWP.done
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hv0_beq, hx25_3, hcmp1, hn1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, *]; try bv_omega)
      (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    clear hpc3
    intro _m_real hnsp4 hinv7
    have hpool4 : A.pool lim st1 sf3 = A.pool lim st1 _ :=
      (A.pool_transport lim st1 _ _ (hnsp4.toVmPreserved (by simp only [wp_norm, arm64_norm]))).symm
    have hwith : ∀ {s_m : State} {Pm : SepProp},
        s_m.pc = (blkPl_617).base + 0x1a8#64 →
        (s_m.pc = (blkPl_617).base + 0x1a8#64 →
          SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s_m Pm Q Qp oom) →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s_m Pm Q Qp oom := fun h1 k => k h1
    refine hwith
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hv0_beq, hx25_3, hcmp1, hn1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; try bv_omega) ?_
    intro hpc4
    refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 0x1b0#64) hinv7 fun _m_strip2 => ?_
    wp_step; wp_steps
    apply SepWP.done
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hx24_3, hx25_3, hn1, Bool.false_eq_true, ↓reduceIte, *]; try bv_omega)
      (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    intro _m_real2 hnsp5 hinv8
    have hpool5 : A.pool lim st1 sf3 = A.pool lim st1 _ :=
      hpool4.trans (A.pool_transport lim st1 _ _ (hnsp5.toVmPreserved (by simp only [wp_norm, arm64_norm]))).symm
    apply sepWPp_mono_pre
      (P' := argsBuf A.repAlloc 4#64 vptr0 ps ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (fspOf s0) [] ∗
        stackAt (fspOf s0) (stk - mainFrameSize) ∗
        A.pool lim (M.stepEvents [] st1) _ ∗ Statics)
    · have hinit : (A.live vptr0 64 8 ∗ (vptr0 ↦₆₄ ps[0].1) ∗
          ((vptr0 + 8#64) ↦₆₄ BitVec.ofNat 64 ps[0].2.length) ∗ memRegion (vptr0 + 16#64) 48) ⊢
          argsBuf A.repAlloc 4#64 vptr0 ps := by
        have h := argsBuf_init_cap4 A.repAlloc vptr0 ps[0] hv0
        simpa only [RustCliAllocBudget.repAlloc_live, htake1, ← hn1, ← hps_len, List.take_length] using h
      have hhdr := words_to_memRegion_24 (fspOf s0 + 0x310#64) 4#64 vptr0 1#64
      rw [locals_nil_split_m2, AllocCostModel.stepEvents_nil, ← hpool5]
      simp only [wp_norm, arm64_norm, hsp3_eq, hx21_3, hx23_3, hn1,
        BitVec.add_assoc, BitVec.reduceAdd,
        show BitVec.ofNat 64 1 = 1#64 by rfl] at hinit hhdr ⊢
      exact Entails.trans
        (entail_with_frame_p
          (F := ((fspOf s0 + 784#64) ↦₆₄ 4#64 ∗ (fspOf s0 + 792#64) ↦₆₄ vptr0 ∗
              (fspOf s0 + 800#64) ↦₆₄ 1#64) ∗
            argsBuf A.repAlloc 1#64 buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            memRegion (fspOf s0) 440 ∗ memRegion (fspOf s0 + 440#64) 24 ∗
            memRegion (fspOf s0 + 464#64) 320 ∗ memRegion (fspOf s0 + 808#64) 344 ∗
            mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool lim st1 sf3 ∗ Statics) hinit)
        (entail_with_frame_p
          (F := argsBuf A.repAlloc 4#64 vptr0 ps ∗
            argsBuf A.repAlloc 1#64 buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            memRegion (fspOf s0) 440 ∗ memRegion (fspOf s0 + 440#64) 24 ∗
            memRegion (fspOf s0 + 464#64) 320 ∗ memRegion (fspOf s0 + 808#64) 344 ∗
            mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool lim st1 sf3 ∗ Statics) hhdr)
    refine hnext _ 4#64 vptr0 [] (M2CollectLoopEnv.nil n 1)
      ⟨?_, ?_, ?_, ?_, hinv8, ?_, hsp0_keep (), ?_⟩
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by decide)
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hn1, Bool.false_eq_true, ↓reduceIte]; try bv_omega
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hrun3]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3_eq]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_3]
    · simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_3
    · exact fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp3_eq])
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_3, hn1]
    · rfl
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hn1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_3, hn1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr3]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfs3]
  · have hn_gt1 : 1 < n := by omega
    refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 0x120#64) hinv6 fun _m_strip => ?_
    wp_step; wp_steps
    apply SepWP.done
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hv0_beq, hx25_3, hcmp1, hn1, decide_false, Bool.not_false, ↓reduceIte, *]; try bv_omega)
      (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    intro _m_real hnsp4 hinv7
    have hpool4 : A.pool lim st1 sf3 = A.pool lim st1 _ :=
      (A.pool_transport lim st1 _ _ (hnsp4.toVmPreserved (by simp only [wp_norm, arm64_norm]))).symm
    apply sepWPp_mono_pre_sp_pool (fsp := fspOf s0)
      (F := fun sp s_cur => vecHeader (sp + 0x310#64) 4#64 vptr0 (BitVec.ofNat 64 1) ∗
        argsBuf A.repAlloc 4#64 vptr0 (ps.take 1) ∗
        m2LoopMem A lim st1 s_cur s0 stk n buf p0 ps Statics)
    · simp only [wp_norm, arm64_norm, hsp3_eq]
    · have hinit : (A.live vptr0 64 8 ∗ (vptr0 ↦₆₄ ps[0].1) ∗
          ((vptr0 + 8#64) ↦₆₄ BitVec.ofNat 64 ps[0].2.length) ∗ memRegion (vptr0 + 16#64) 48) ⊢
          argsBuf A.repAlloc 4#64 vptr0 (ps.take 1) := by
        simpa only [RustCliAllocBudget.repAlloc_live, htake1] using
          argsBuf_init_cap4 A.repAlloc vptr0 ps[0] hv0
      dsimp only [m2LoopMem, m2LoopRest]
      unfold vecHeader
      rw [← hpool4]
      simp only [wp_norm, arm64_norm, hsp3_eq, hx21_3, hx23_3, fspOf, mainFrameSize,
        BitVec.add_assoc, BitVec.reduceAdd,
        show BitVec.ofNat 64 1 = 1#64 by rfl,
        show BitVec.ofNat 64 1248 = 1248#64 by rfl] at hinit ⊢
      exact entail_with_frame_p
        (F := ((s0.sp - 464#64) ↦₆₄ 4#64 ∗
            (s0.sp - 456#64) ↦₆₄ vptr0 ∗
            (s0.sp - 448#64) ↦₆₄ 1#64) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (s0.sp - 1248#64) 440 ∗
          memRegion (s0.sp - 808#64) 24 ∗
          memRegion (s0.sp - 784#64) 320 ∗
          memRegion (s0.sp - 440#64) 344 ∗
          mainSaved s0 ∗ stackAt (s0.sp - 1248#64) (stk - 1248) ∗
          A.pool lim st1 sf3 ∗ Statics) hinit
    refine step_collect_loop_placed env hstk hstk64 hn_le hps_len hascii
      (n - 1) 1 st1 _ 4#64 vptr0 rfl (Nat.le_refl 1) hn_gt1 (hfit_loop hn_gt1)
      ⟨⟨?_, ?_, ?_, ?_, hinv7, ?_, hsp0_keep (), ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
      hnext
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hv0_beq, hx25_3, hcmp1, hn1, decide_false, Bool.not_false, ↓reduceIte]; try bv_omega
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hrun3]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3_eq]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_3]
    · simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_3
    · exact fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp3_eq])
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_3]
    · rfl
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx22_3]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_3]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_3]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr3]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfs3]

set_option maxHeartbeats 800000 in
/-- Entry phase `M+0x0c0 .. M+0x11c` on Block `617` with general OOM callback on `__rust_alloc(64, 8)`
    and `FitsEnv` for the loop re-allocations (`1 < n`). -/
theorem step_collect_first_oom_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {ret : BitVec 64} {stk hookStack resStack n : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A lim hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hn1_le : 1 ≤ n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hascii : ∀ k (hk : k < ps.length), ∀ b ∈ ps[k].2, b.toNat < 128)
    (hoom_cb : ∀ s_pre sf R',
      s_pre.trace = s0.trace → s_pre.fs = s0.fs →
      sf.status = .OutOfMemory →
      ¬ FitsEvents M lim st (rustAllocEvents 64 8) →
      OomPreserved s_pre sf →
      (sf.mem ⊨ anyHeap ∗ R') → (sf.mem ⊨ oom sf ∗ R'))
    (hfit_loop : 1 < n → FitsEnv M lim (M.stepEvents (rustAllocEvents 64 8) st) (M2CollectLoopEnv n 1))
    (hf : M2FramePlaced CodeOk s0 s 0x0c0)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx22 : s.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n))
    (_hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hnext : ∀ (s' : State) (vcap vptr : BitVec 64) (evs : List AllocEvent),
      M2CollectEnv n evs →
      M2FramePlaced CodeOk s0 s' (if n = 2 then 0x2f4 else 0x1b0) →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = vptr →
      s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 23#5) = vcap →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      vcap ≠ 0#64 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (argsBuf A.repAlloc vcap vptr ps ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ Statics) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
      (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics) Q Qp oom := by
  have h0_ps : 0 < ps.length := by omega
  rcases hf with ⟨hpc, hrun, hsp_eq, hfp, hinv, hvregs, hsp0, hs_aligned⟩
  have hsp0_keep : Unit → s0.spAligned = true := fun () => hsp0
  clear hsp0
  have hfocus0 : argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps =
      (buf ↦₆₄ ps[0].1) ∗ ((buf + 8#64) ↦₆₄ BitVec.ofNat 64 ps[0].2.length) ∗
        argsBufRest A.repAlloc (BitVec.ofNat 64 n) buf ps 0 := by
    simpa only [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero] using
      argsBuf_focus A.repAlloc (BitVec.ofNat 64 n) buf ps 0 h0_ps
  rw [locals_nil_split_m2, hfocus0]
  refine sepWPp_seq_codeOk_vm (mid := lsρ lsFromUtf8Sym) hinv fun _m_strip0 => ?_
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
  intro _m_real0 hnsp0 hinv1
  have hpool0 : A.pool lim st s = A.pool lim st _ :=
    (A.pool_transport lim st _ _ (hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm]))).symm
  rw [← hfocus0]
  have hargv0 := argvAtROP_focus (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps)
    1 (by simp [hps_len]; omega)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hargv0
  have hstk_utf8 := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := hookStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  apply main_call_rocl (s0 := s0) (CodeOk := CodeOk) (fspOf s0 + 0x1b8#64, ps[0].1, ps[0].2) env.utf8_ok hinv1
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    (fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp_eq]))
    (ret_pc := (blkPl_617).base + 0x0cc#64)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    (F := argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      argvAtROPRest (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) 1 ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      A.pool lim st s ∗ Statics)
  · dsimp only [withVmPreserved, fromUtf8AsciiSpecRO]
    have hascii0_eq : (∀ b ∈ ps[0].2, b.toNat < 128) = True :=
      propext ⟨fun _ => trivial, fun _ => hascii 0 h0_ps⟩
    rw [hargv0, hstk_utf8]
    apply Entails.of_eq
    simp only [wp_norm, arm64_norm, hsp_eq, hx19, hascii0_eq, true_and,
      pure_true, emp_sepConj, BitVec.add_assoc, BitVec.reduceAdd]
    try sep_ac_rfl
  intro sf1 hinv2 hpc1 hrun1 hsp1 hcs1
  have hsp1_eq : sf1.sp = fspOf s0 := by simpa only [wp_norm, arm64_norm, hsp_eq] using hsp1
  clear hsp1
  have hx19_1 : sf1.readReg64 (.gpr 19#5) = buf := by
    rw [cs_x19 hcs1]; simp only [wp_norm, arm64_norm, hx19]
  have hx22_1 : sf1.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n) := by
    rw [cs_x22 hcs1]; simp only [wp_norm, arm64_norm, hx22]
  have hx24_1 : sf1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
    rw [cs_x24 hcs1]; simp only [wp_norm, arm64_norm, hx24]
  have hx25_1 : sf1.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n := by
    rw [cs_x25 hcs1]; simp only [wp_norm, arm64_norm, hx25]
  have hfp_1 : sf1.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [cs_fp hcs1]; simp only [wp_norm, arm64_norm, hfp]
  have hvregs_1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 :=
    calleeSavedVRegs_preserve (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs) hcs1
  have hs1_aligned : sf1.spAligned = true := fsp_spAligned (hsp0_keep ()) hsp1_eq
  clear hpc hrun hs_aligned
  dsimp only [withVmPreserved, fromUtf8AsciiSpecRO]
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun hvm_utf8 => ?_
  have hpool1 : A.pool lim st s = A.pool lim st sf1 :=
    hpool0.trans (A.pool_transport lim st _ _ hvm_utf8).symm
  clear hpool0 hnsp0 hvm_utf8
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨htr1_raw, hfs1_raw⟩ => ?_
  have htr1 : sf1.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr] using htr1_raw
  have hfs1 : sf1.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs] using hfs1_raw
  clear htr1_raw hfs1_raw
  apply sepWPp_mono_pre
    (P' := ((sf1.sp + 440#64) ↦₆₄ 0#64) ∗
      ((sf1.sp + 448#64) ↦₆₄ ps[0].1) ∗ ((sf1.sp + 456#64) ↦₆₄ BitVec.ofNat 64 ps[0].2.length) ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      stackAt (fspOf s0) (stk - mainFrameSize) ∗
      A.pool lim st sf1 ∗ Statics)
  · apply Entails.of_eq
    rw [hargv0, ← hpool1]
    simp only [wp_norm, arm64_norm, hsp_eq, hsp1_eq,
      BitVec.add_assoc, BitVec.reduceAdd]
    rw [hstk_utf8]
    try sep_ac_rfl
  simp only [wp_norm, arm64_norm, hsp1_eq]
  refine sepWPp_seq_codeOk_vm (mid := lsρ lsRustNoAllocShimSymCli) hinv2 fun _m_strip1 => ?_
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
  intro _m_real1 hnsp1 hinv3
  have hpool2 : A.pool lim st sf1 = A.pool lim st _ :=
    (A.pool_transport lim st _ _ (hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm]))).symm
  have hstk_ext := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := extHookStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  apply sepWPp_mono_pre
    (P' := stackAt (fspOf s0) extHookStack ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1b8#64) 24 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
      A.pool lim st sf1 ∗ Statics)
  · have hsret := words_to_memRegion_24 (fspOf s0 + 0x1b8#64) 0#64 ps[0].1
      (BitVec.ofNat 64 ps[0].2.length)
    simp only [wp_norm, arm64_norm, hsp1_eq, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd] at hsret ⊢
    rw [hstk_ext]
    exact entail_with_frame_p
      (F := argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 464#64) 320 ∗
        memRegion (fspOf s0 + 784#64) 24 ∗ memRegion (fspOf s0 + 808#64) 344 ∗
        mainSaved s0 ∗
        memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
        stackAt (fspOf s0) extHookStack ∗ A.pool lim st sf1 ∗ Statics) hsret
  apply main_call_rocl (s0 := s0) (CodeOk := CodeOk) () env.shim_ok hinv3
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    (fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp1_eq]))
    (ret_pc := (blkPl_617).base + 0x0e0#64)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    (F := argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1b8#64) 24 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
      A.pool lim st sf1 ∗ Statics)
  · simp only [Spec.keepsFs, session2ShimBudgetSpecX, wp_norm, arm64_norm, hsp1_eq]
    exact Entails.of_eq (by sep_ac_rfl)
  intro sf2 hinv4 hpc2 hrun2 hsp2 hcs2
  have hsp2_eq : sf2.sp = fspOf s0 := by simpa only [wp_norm, arm64_norm, hsp1_eq] using hsp2
  clear hsp2
  have hx19_2 : sf2.readReg64 (.gpr 19#5) = buf := by
    rw [cs_x19 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_1]
  have hx21_2 : sf2.readReg64 (.gpr 21#5) = ps[0].1 := by
    rw [cs_x21 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
  have hx22_2 : sf2.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n) := by
    rw [cs_x22 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx22_1]
  have hx23_2 : sf2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 ps[0].2.length := by
    rw [cs_x23 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
  have hx24_2 : sf2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
    rw [cs_x24 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_1]
  have hx25_2 : sf2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n := by
    rw [cs_x25 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx25_1]
  have hfp_2 : sf2.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [cs_fp hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_1]
  have hvregs_2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
    calleeSavedVRegs_preserve
      (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_1) hcs2
  have hs2_aligned : sf2.spAligned = true := fsp_spAligned (hsp0_keep ()) hsp2_eq
  clear hpc1 hrun1 hs1_aligned
  simp only [Spec.keepsFs, session2ShimBudgetSpecX, wp_norm, arm64_norm, hsp1_eq, sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨hfs2_raw, htr2_raw, hvm_sh⟩ => ?_
  have htr2 : sf2.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr1] using htr2_raw
  have hfs2 : sf2.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs1] using hfs2_raw
  have hpool3 : A.pool lim st sf1 = A.pool lim st sf2 := by
    have h2 := hpool2
    simp only [arm64_norm] at h2
    exact h2.trans (by
      have h := (A.pool_transport lim st _ _ hvm_sh).symm
      simpa only [RustCliAllocBudget.pool_setPC_norm, RustCliAllocBudget.pool_writeReg64_norm, arm64_norm] using h)
  clear htr2_raw hfs2_raw hpool2 hnsp1 hvm_sh
  refine sepWPp_seq_codeOk_vm (mid := lsρ lsRustAllocSymCli) hinv4 fun _m_strip2 => ?_
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
  intro _m_real2 hnsp2 hinv5
  have hpool4 : A.pool lim st sf1 = A.pool lim st _ :=
    hpool3.trans (A.pool_transport lim st _ _ (hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]))).symm
  refine main_call_rocl (s0 := s0) (CodeOk := CodeOk) (64, 8, st) env.alloc_ok hinv5
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    (fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp2_eq]))
    (ret_pc := (blkPl_617).base + 0x0ec#64)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    (F := argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1b8#64) 24 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
      Statics)
    ?_ (hoom := ?_) (hnext := ?_)
  · dsimp only [Spec.keepsFs, rustAllocSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocBudgetSpecWithStack]
    have hlay : CryptoVerification.RustHeap.LayoutOk 64 8 := ⟨by decide, ⟨3, rfl⟩, by decide⟩
    have hrlo : RustLayoutOk 64 8 := And.intro hlay (by decide)
    have hls_0ec :
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_617).base + 0x0ec#64) :=
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 617
        0x0ec#64 (by decide) (by decide)
    rw [← hpool4]
    simp only [wp_norm, arm64_norm, hsp1_eq, hsp2_eq, sepConj_assoc,
      show (64#64 : BitVec 64).toNat = 64 by rfl, show (8#64 : BitVec 64).toNat = 8 by rfl]
    refine Entails.pure_right ⟨hrlo, hls_0ec⟩ ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf R' hst_oom hmoom
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocBudgetSpecWithStack] at hmoom
    rw [satisfies_pure_sepConj] at hmoom
    exact hoom_cb _ sf R'
      (by simp only [wp_norm, arm64_norm, htr2])
      (by simp only [wp_norm, arm64_norm, hfs2])
      hst_oom hmoom.1.1 hmoom.1.2
      (Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmoom.2)
  · intro sf3 hinv6 hpc3 hrun3 hsp3 hcs3
    have hsp3_eq : sf3.sp = fspOf s0 := by simpa only [wp_norm, arm64_norm, hsp2_eq] using hsp3
    clear hsp3
    have hx19_3 : sf3.readReg64 (.gpr 19#5) = buf := by
      rw [cs_x19 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_2]
    have hx21_3 : sf3.readReg64 (.gpr 21#5) = ps[0].1 := by
      rw [cs_x21 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx21_2]
    have hx22_3 : sf3.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n) := by
      rw [cs_x22 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx22_2]
    have hx23_3 : sf3.readReg64 (.gpr 23#5) = BitVec.ofNat 64 ps[0].2.length := by
      rw [cs_x23 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_2]
    have hx24_3 : sf3.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
      rw [cs_x24 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_2]
    have hx25_3 : sf3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n := by
      rw [cs_x25 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx25_2]
    have hfp_3 : sf3.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [cs_fp hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_2]
    have hvregs_3 : calleeSavedVRegs sf3 = calleeSavedVRegs s0 :=
      calleeSavedVRegs_preserve
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_2) hcs3
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocBudgetSpecWithStack]
    simp only [wp_norm, arm64_norm, hsp2_eq, sepConj_assoc]
    refine sepWPp_pure_elim fun ⟨hfs3_raw, hacp⟩ => ?_
    have hfs3 : sf3.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs2] using hfs3_raw
    have htr3 : sf3.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr2] using hacp.2.1
    by_cases hv0 : sf3.readReg64 .x0 = (0 : BitVec 64)
    · simp only [hv0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWPp_mono_pre
        (P' := ⌜NullAllowed 64 8⌝ ∗
          (A.pool lim st sf3 ∗ stackAt (fspOf s0) extHookStack ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 0x1b8#64) 24 ∗
            memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗ memRegion (fspOf s0 + 0x310#64) 24 ∗
            memRegion (fspOf s0 + 0x328#64) 0x158 ∗ mainSaved s0 ∗
            memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
            Statics))
      · simp only [wp_norm, arm64_norm, fspOf, mainFrameSize,
          show BitVec.ofNat 64 1248 = 1248#64 by rfl, BitVec.add_assoc, BitVec.reduceAdd]
        exact Entails.of_eq (by sep_ac_rfl)
      refine sepWPp_pure_elim fun hna => ?_
      unfold NullAllowed at hna
      omega
    · simp only [hv0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWPp_mono_pre
        (P' := ⌜(sf3.readReg64 .x0).toNat % 8 = 0⌝ ∗
          (A.live (sf3.readReg64 .x0) 64 8 ∗ memRegion (sf3.readReg64 .x0) 64 ∗
            A.pool lim (M.stepEvents (rustAllocEvents 64 8) st) sf3 ∗
            stackAt (fspOf s0) extHookStack ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            memRegion (fspOf s0) 0x1b8 ∗
            memRegion (fspOf s0 + 0x1b8#64) 24 ∗
            memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
            memRegion (fspOf s0 + 0x310#64) 24 ∗
            memRegion (fspOf s0 + 0x328#64) 0x158 ∗
            mainSaved s0 ∗
            memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
            Statics))
      · simp only [wp_norm, arm64_norm, fspOf, mainFrameSize,
          show BitVec.ofNat 64 1248 = 1248#64 by rfl, BitVec.add_assoc, BitVec.reduceAdd]
        exact Entails.of_eq (by sep_ac_rfl)
      refine sepWPp_pure_elim fun _halign => ?_
      exact step_collect_post_alloc_placed env hstk hstk64 hn1_le hn_le hps_len hascii hfit_loop
        (hsp0_keep ()) hpc3 hrun3 hsp3_eq hfp_3 hinv6 hvregs_3
        hx19_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 htr3 hfs3 hv0
        (fun s' vcap vptr evs_loop hloop hf' hx19' hx20' hx21' hx23' hx24' htr' hfs' hvcap_ne' => by
          rw [← M.stepEvents_append]
          exact hnext s' vcap vptr (rustAllocEvents 64 8 ++ evs_loop)
            (M2CollectEnv.alloc_then_loop hloop)
            hf' hx19' hx20' hx21' hx23' hx24' htr' hfs' hvcap_ne')

/-- Total-correctness (`FitsEnv M lim st (M2CollectEnv n)`) entry phase `M+0x0c0 .. M+0x11c`
    on Block `617`. -/
theorem step_collect_first_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {ret : BitVec 64} {stk hookStack resStack n : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A lim hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hn1_le : 1 ≤ n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hascii : ∀ k (hk : k < ps.length), ∀ b ∈ ps[k].2, b.toNat < 128)
    (hfit : FitsEnv M lim st (M2CollectEnv n))
    (hf : M2FramePlaced CodeOk s0 s 0x0c0)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx22 : s.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n))
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hnext : ∀ (s' : State) (vcap vptr : BitVec 64) (evs : List AllocEvent),
      M2CollectEnv n evs →
      M2FramePlaced CodeOk s0 s' (if n = 2 then 0x2f4 else 0x1b0) →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = vptr →
      s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 23#5) = vcap →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      vcap ≠ 0#64 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (argsBuf A.repAlloc vcap vptr ps ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ Statics) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
      (argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics) Q Qp oom :=
  step_collect_first_oom_placed env hstk hstk64 hn1_le hn_le hps_len hascii
    (fun _ _ _ _ _ _ hnf _ _ => (hnf (hfit.seq_left _ rfl)).elim)
    (fun _ => hfit.seq_right (evs₁ := rustAllocEvents 64 8) rfl)
    hf hx19 hx22 hx23 hx24 hx25 htr hfs hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget
