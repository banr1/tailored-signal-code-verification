/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Frame
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `main` M2 Collect Loop Steps (`M+0xc0 → M+0x2f4 / M+0x1b0`)

Verifies the `Vec<&str>` push loop (`from_utf8` and capacity-doubling `reserve16`) and epilogue on
Block `617` with read-only `argvAtROP` and `RustCliAllocBudget M`, threading `A.pool` and
`M2CollectLoopEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.RustHeap (RustAlloc allocFailedEvent allocFailedIn arrayAt vecHeader)
open CryptoVerification.SignalSession
  (lsFromUtf8Sym lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkLib_eq_617 blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv Reserve16Call add_mul16_beq argsBuf argsBuf_focus
   argsBuf_push_reassemble argsBuf_push_split argsBuf_to_vec16At flatSliceBytes
   flatSliceBytes_length fsp_spAligned locals locals_nil_split_m2 lsHandleErrorSymMain m2At
   mainFrameSize mainSaved main_call_rocl ofNat_beq_ofNat sepWPp_seq_codeOk sliceRefAt
   stackAt_split_ge' vcap_add_one_beq_zero_false vcap_beq_max_false vec16At vec16At_to_argsBuf
   words_to_memRegion_24)
open CryptoVerification.SignalSession.Cli.MainHops.M2Steps
  (calleeSavedVRegs_preserve cs_fp cs_x19 cs_x20 cs_x21 cs_x22 cs_x23 cs_x24 cs_x25 cs_x26
   cs_x27 cs_x28 fspOf fspOf_def ofNat_beq_bv pointsTo64_zero_eq_pair32 sepWPp_exists_elim
   sepWPp_mono_pre sepWPp_mono_pre_sp sepWPp_pure_elim)
open CryptoVerification.SignalSession.Cli.MainHops.M2StepsPlaced
  (M2FramePlaced M2LoopInvPlaced)
open CryptoVerification.SpqrV1.Alloc (reserveCapStride)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget SeqEnv
   rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (MainCalleesROBlk617 fromUtf8AsciiSpecRO main_fromUtf8_ro_placed_ok
   main_panic_handle_error_ro_placed main_reserve16_ro_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cStrAtRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (Reserve16Env reserve16Events reserve16Spec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
  (main_alloc_fs_placed_ok main_shim_fs_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Remaining frame of `argvAtROP a ps` with `ps[k].1 ↦ᵣ ps[k].2` extracted for reading. -/
def argvAtROPRest : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → Nat → SepProp
  | a, [], _ => a ↦₆₄ᵣ 0#64
  | a, (p, s) :: rest, 0 =>
    (a ↦₆₄ᵣ p) ∗ ((p + BitVec.ofNat 64 s.length) ↦ᵣ [0#8]) ∗ argvAtROP (a + 8#64) rest
  | a, (p, s) :: rest, k + 1 =>
    (a ↦₆₄ᵣ p) ∗ cStrAtRO p s ∗ argvAtROPRest (a + 8#64) rest k

theorem argvAtROP_focus (a : BitVec 64) :
    (ps : List (BitVec 64 × List (BitVec 8))) → (k : Nat) → (hk : k < ps.length) →
    argvAtROP a ps = (ps[k].1 ↦ᵣ ps[k].2) ∗ argvAtROPRest a ps k
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | (p, s) :: rest, 0, _ => by
    simp only [argvAtROP, argvAtROPRest, cStrAtRO, List.getElem_cons_zero, pointsToBytesRO_append]
    sep_ac_rfl
  | (p, s) :: rest, k + 1, hk => by
    have hk' : k < rest.length := Nat.lt_of_succ_lt_succ hk
    simp only [argvAtROP, argvAtROPRest, List.getElem_cons_succ, argvAtROP_focus (a + 8#64) rest k hk']
    sep_ac_rfl

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

/-! ## 0. Callee Environment, Loop Frame, & Event Envelope -/

/-- Read-only-`argv` budget-threaded callee contracts for `M2Collect` on Block `617`. -/
structure M2EnvPlaced [LibsignalPlacement] {M : AllocCostModel} (H : LibsignalHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hookStack resStack : Nat) : Prop where
  shim_ok : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustNoAllocShimSymCli)
    (withLsRoCl lsmpl session2ShimBudgetSpecX.keepsFs)
  alloc_ok : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustAllocSymCli)
    (withLsRoCl lsmpl (rustAllocSpecWithStack M A lim false extHookStack).keepsFs)
  utf8_ok : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsFromUtf8Sym)
    (withLsRoCl lsmpl (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
  res16_ok : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 561)
    (withLsRoCl lsmpl (reserve16Spec A lim resStack))
  panic_ext : ((blkPC_617).rebase (blkPl_617).base H).externAt? (lsρ lsHandleErrorSymMain) =
    some Rust.panicked

theorem m2EnvPlaced_init [LibsignalPlacement] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack) :
    M2EnvPlaced H A lim hookStack resStack where
  shim_ok := main_shim_fs_placed_ok hc.allocFs
  alloc_ok := main_alloc_fs_placed_ok hc.allocFs
  utf8_ok := main_fromUtf8_ro_placed_ok hc
  res16_ok := main_reserve16_ro_placed_ok hc
  panic_ext := main_panic_handle_error_ro_placed hc

/-- State-independent spatial portion of `M2Collect`'s loop frame (`[sp + 0x310 .. +24)` split out). -/
abbrev m2LoopRest (A : RustAlloc) (s0 : State) (stk n : Nat)
    (buf p0 : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (Statics : SepProp) : SepProp :=
  argsBuf A (BitVec.ofNat 64 n) buf ps ∗
    argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
    memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x1b8 ∗
    memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64) 24 ∗
    memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1d0#64) 0x140 ∗
    memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x328#64) 0x158 ∗
    mainSaved s0 ∗
    stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
    Statics

/-- Budget-threaded spatial frame carried around `M2Collect`'s loop (`A.pool lim st s ∗ m2LoopRest ...`). -/
abbrev m2LoopMem {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s s0 : State) (stk n : Nat)
    (buf p0 : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (Statics : SepProp) : SepProp :=
  A.pool lim st s ∗ m2LoopRest A.repAlloc s0 stk n buf p0 ps Statics

/-- Deterministic reallocation events emitted when `reserve16` grows `Vec<&str>` at index `k = vcap.toNat`. -/
def m2GrowEventsAt (k : Nat) : List AllocEvent :=
  let new := reserveCapStride 16 k k 1
  rustReallocEvents (16 * k) (16 * new) 8

theorem reserve16Events_eq_m2GrowEventsAt {v ptr vcap : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {k : Nat}
    (hk_ps : k < ps.length) (hfull : k = vcap.toNat) (hvcap_ne : vcap ≠ 0#64) :
    reserve16Events { v := v, cap := vcap, ptr := ptr, bs := flatSliceBytes (ps.take k) } =
      m2GrowEventsAt k := by
  have htake_len : (ps.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk_ps)
  have hdiv : (flatSliceBytes (ps.take k)).length / 16 = k := by
    rw [flatSliceBytes_length, htake_len]; omega
  simp only [reserve16Events, m2GrowEventsAt, hdiv, ← hfull, hvcap_ne, ↓reduceIte]

/-- Envelope of allocation-event lists that `M2Collect`'s loop over `k .. n` may emit across
    capacity-doubling `reserve16` steps. -/
inductive M2CollectLoopEnv (n : Nat) : Nat → List AllocEvent → Prop where
  | done {k : Nat} : n ≤ k → M2CollectLoopEnv n k []
  | skip {k : Nat} {evs : List AllocEvent} :
      k < n → M2CollectLoopEnv n (k + 1) evs → M2CollectLoopEnv n k evs
  | grow {k : Nat} {evs : List AllocEvent} :
      1 ≤ k → k < n → M2CollectLoopEnv n (k + 1) evs →
      M2CollectLoopEnv n k (m2GrowEventsAt k ++ evs)

private theorem m2CollectLoopEnv_nil_aux (n : Nat) :
    ∀ (rem k : Nat), n - k = rem → M2CollectLoopEnv n k []
  | 0, k, _ => .done (by omega)
  | rem + 1, k, _ =>
    .skip (by omega) (m2CollectLoopEnv_nil_aux n rem (k + 1) (by omega))

theorem M2CollectLoopEnv.nil (n k : Nat) : M2CollectLoopEnv n k [] :=
  m2CollectLoopEnv_nil_aux n (n - k) k rfl

theorem M2CollectLoopEnv.seq_grow {n k : Nat} (hk1 : 1 ≤ k) (hk_lt : k < n)
    {evs : List AllocEvent}
    (h : SeqEnv (· = m2GrowEventsAt k) (M2CollectLoopEnv n (k + 1)) evs) :
    M2CollectLoopEnv n k evs := by
  rcases h with rfl | ⟨_, evs₂, rfl, rfl, h2⟩
  · simpa only [List.append_nil] using
      M2CollectLoopEnv.grow hk1 hk_lt (M2CollectLoopEnv.nil n (k + 1))
  · exact M2CollectLoopEnv.grow hk1 hk_lt h2

/-! ## 1. OOM Panic Handler (`M+0xff0 .. M+0xff8`) -/

theorem step_collect_panic_placed [LibsignalPlacement] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hookStack resStack : Nat} {s0 s : State}
    {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A lim hookStack resStack)
    (hpc : s.pc = (blkPl_617).base + 0xff0#64) (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent])
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s P Q Qp oom := by
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSymMain)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simpa only [wp_norm, arm64_norm] using env.panic_ext) ?_
  apply hpanic
  unfold allocFailedIn
  simp only [Rust.panicked, wp_norm, arm64_norm, htr, List.drop_left, List.mem_singleton]

/-! ## 2. Loop Epilogue (`M+0x2dc .. M+0x2f0 → M+0x2f4 / M+0x1b0`) -/

theorem step_collect_epilogue_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {ret : BitVec 64} {n : Nat} {buf vcap vptr : BitVec 64}
    {Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hf : M2FramePlaced CodeOk s0 s 0x2dc)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hn_le : n ≤ 1820) (_hvcap_ne : vcap ≠ 0#64) (hvcap63 : vcap.toNat * 16 < 2 ^ 63)
    (hnext : ∀ s' : State,
      M2FramePlaced CodeOk s0 s' (if n = 2 then 0x2f4 else 0x1b0) →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = vptr →
      s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 23#5) = vcap →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗ A.pool lim st s' ∗ Rest) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
      (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 n) ∗
        memRegion s.sp 0x1b8 ∗
        memRegion (s.sp + 0x1b8#64) 24 ∗
        memRegion (s.sp + 0x1d0#64) 0x140 ∗
        memRegion (s.sp + 0x328#64) 0x158 ∗
        A.pool lim st s ∗ Rest)
      Q Qp oom := by
  rcases hf with ⟨hpc, hrun, hsp_eq, hfp, hinv, hvregs, hsp0, hs_aligned⟩
  have hcmn : (vcap + 1#64 == 0#64) = false := vcap_add_one_beq_zero_false (by omega)
  have hmax : (vcap == 0xffffffffffffffff#64) = false := vcap_beq_max_false (by omega)
  have hcmp2 : (BitVec.ofNat 64 n == 2#64) = decide (n = 2) :=
    ofNat_beq_ofNat (by omega) (by decide)
  unfold vecHeader
  refine sepWPp_seq_codeOk_vm
    (mid := (blkPl_617).base + BitVec.ofNat 64 (if n = 2 then 0x2f4 else 0x1b0)) hinv fun _m_strip => ?_
  wp_steps
  apply SepWP.done
    (by
      by_cases hn2 : n = 2
      · simp only [wp_norm, arm64_norm, bne, hcmn, hmax, hx21, hcmp2, hn2, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, *]
      · simp only [wp_norm, arm64_norm, bne, hcmn, hmax, hx21, hcmp2, hn2, decide_false, Bool.not_false, ↓reduceIte, *])
    (hrun := by simp only [wp_norm, arm64_norm, *])
  intro _m_real hnsp hinv'
  have hpool' : A.pool lim st _ = A.pool lim st s :=
    A.pool_transport lim st _ _ (hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
  apply sepWPp_mono_pre (P' := locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗ A.pool lim st _ ∗ Rest)
  · rw [hpool', locals_nil_split_m2]
    have hhdr := words_to_memRegion_24 (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
      vcap vptr (BitVec.ofNat 64 n)
    simp only [hsp_eq, BitVec.add_assoc, BitVec.reduceAdd] at hhdr ⊢
    exact entail_with_frame_p
      (F := memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 440 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 440#64) 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 464#64) 320 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 808#64) 344 ∗ A.pool lim st s ∗ Rest) hhdr
  refine hnext _ ⟨?_, ?_, ?_, ?_, hinv', ?_, hsp0, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · by_cases hn2 : n = 2
    · simp only [wp_norm, arm64_norm, bne, hcmn, hmax, hx21, hcmp2, hn2, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, *]
    · simp only [wp_norm, arm64_norm, bne, hcmn, hmax, hx21, hcmp2, hn2, decide_false, Bool.not_false, ↓reduceIte, *]
  · simp only [wp_norm, arm64_norm, hrun]
  · simp only [wp_norm, arm64_norm, hsp_eq]
  · simp only [wp_norm, arm64_norm, hfp]
  · simp only [calleeSavedVRegs, wp_norm, arm64_norm]
    exact hvregs
  · exact fsp_spAligned hsp0 (by simp only [wp_norm, arm64_norm, hsp_eq])
  · simp only [wp_norm, arm64_norm, hx19]
  · simp only [wp_norm, arm64_norm]
  · simp only [wp_norm, arm64_norm, hx21]
  · simp only [wp_norm, arm64_norm]
  · simp only [wp_norm, arm64_norm, hx24]
  · simp only [wp_norm, arm64_norm, htr]
  · simp only [wp_norm, arm64_norm, hfs]

/-! ## 3. Loop Iteration Tail (`M+0x148 .. M+0x168`) -/

theorem step_collect_iter_tail_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {ret : BitVec 64} {n k : Nat} {buf vcap vptr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {FrameRest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hf : M2FramePlaced CodeOk s0 s 0x148)
    (hk1 : 1 ≤ k) (hk_lt : k < n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hk_cap : k < vcap.toNat)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 k)
    (hx22 : s.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n))
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (16 * (k - 1)))
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = buf + 16#64)
    (hx26 : s.readReg64 (.gpr 26#5) = buf + BitVec.ofNat 64 (16 * k))
    (hx27 : s.readReg64 (.gpr 27#5) = (ps[k]'(by omega)).1)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (ps[k]'(by omega)).2.length)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hloop : ∀ s' : State,
      k + 1 < n →
      M2LoopInvPlaced CodeOk s0 s' n (k + 1) buf vcap vptr →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (vecHeader (s'.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 (k + 1)) ∗
          argsBuf A.repAlloc vcap vptr (ps.take (k + 1)) ∗
          A.pool lim st s' ∗ FrameRest) Q Qp oom)
    (hexit : ∀ s' : State,
      M2FramePlaced CodeOk s0 s' 0x2dc →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = vptr →
      s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      vcap ≠ 0#64 →
      vcap.toNat * 16 < 2 ^ 63 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (vecHeader (s'.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 n) ∗
          argsBuf A.repAlloc vcap vptr ps ∗
          A.pool lim st s' ∗ FrameRest) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
      (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        argsBuf A.repAlloc vcap vptr (ps.take k) ∗
        A.pool lim st s ∗ FrameRest) Q Qp oom := by
  have hk_ps : k < ps.length := by omega
  have htake_len : (ps.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk_ps)
  have htake_succ : ps.take k ++ [ps[k]] = ps.take (k + 1) := (List.take_succ_eq_append_getElem hk_ps).symm
  rcases hf with ⟨hpc, hrun, hsp_eq, hfp, hinv, hvregs, hsp0, hs_aligned⟩
  apply sepWPp_mono_pre (sepConj_mono_right (sepConj_mono_left
    (argsBuf_push_split A.repAlloc vcap vptr (ps.take k) (by omega))))
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, htake_len]
  refine sepWPp_exists_elim fun w0 => sepWPp_exists_elim fun w1 => ?_
  rw [show vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
      (⌜vcap ≠ 0 ∧ vcap.toNat * 16 < 2 ^ 63 ∧ vptr ≠ 0⌝ ∗
        A.repAlloc.live vptr (vcap.toNat * 16) 8 ∗
        arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 vptr (ps.take k) ∗
        ((vptr + BitVec.ofNat 64 (16 * k)) ↦₆₄ w0) ∗
        (((vptr + BitVec.ofNat 64 (16 * k)) + 8#64) ↦₆₄ w1) ∗
        memRegion (vptr + BitVec.ofNat 64 ((k + 1) * 16)) ((vcap.toNat - (k + 1)) * 16)) ∗
      A.pool lim st s ∗ FrameRest =
      ⌜vcap ≠ 0 ∧ vcap.toNat * 16 < 2 ^ 63 ∧ vptr ≠ 0⌝ ∗
      (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        A.repAlloc.live vptr (vcap.toNat * 16) 8 ∗
        arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 vptr (ps.take k) ∗
        ((vptr + BitVec.ofNat 64 (16 * k)) ↦₆₄ w0) ∗
        (((vptr + BitVec.ofNat 64 (16 * k)) + 8#64) ↦₆₄ w1) ∗
        memRegion (vptr + BitVec.ofNat 64 ((k + 1) * 16)) ((vcap.toNat - (k + 1)) * 16) ∗
        A.pool lim st s ∗ FrameRest) by sep_ac_rfl]
  refine sepWPp_pure_elim fun ⟨hvcap_ne, hvcap63, hvptr_ne⟩ => ?_
  have hslot_off : vptr + BitVec.ofNat 64 (16 * (k - 1)) + 16#64 = vptr + BitVec.ofNat 64 (16 * k) := by
    rw [BitVec.add_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 by rfl, ← BitVec.ofNat_add]
    congr 2; omega
  have hx9_eq : buf + BitVec.ofNat 64 (16 * k) + 16#64 = buf + BitVec.ofNat 64 (16 * (k + 1)) := by
    rw [BitVec.add_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 by rfl, ← BitVec.ofNat_add]
    congr 2
  have hx21_next : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 by rfl, ← BitVec.ofNat_add]
  have hx23_next : BitVec.ofNat 64 (16 * (k - 1)) + 16#64 = BitVec.ofNat 64 (16 * k) := by
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 by rfl, ← BitVec.ofNat_add]
    congr 1; omega
  have hcmp_end : ((buf + BitVec.ofNat 64 (16 * n)) == (buf + BitVec.ofNat 64 (16 * (k + 1)))) =
      decide (n = k + 1) :=
    add_mul16_beq buf (by omega) (by omega)
  unfold vecHeader
  by_cases hdone : k + 1 = n
  · refine sepWPp_seq_codeOk_vm (mid := m2At (blkPl_617).base 0x2dc) hinv fun _m_strip => ?_
    wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, bne, hx22, hx26, hx9_eq, hcmp_end, hdone, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, *])
      (hrun := by simp only [wp_norm, arm64_norm, *])
    intro _m_real hnsp hinv'
    have hpool' : A.pool lim st _ = A.pool lim st s :=
      A.pool_transport lim st _ _ (hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    apply sepWPp_mono_pre_sp (fsp := fspOf s0)
      (F := fun sp => vecHeader (sp + 0x310#64) vcap vptr (BitVec.ofNat 64 n) ∗
        argsBuf A.repAlloc vcap vptr ps ∗ A.pool lim st _ ∗ FrameRest)
    · simp only [wp_norm, arm64_norm, hsp_eq]
    · rw [hpool']
      have hpush := argsBuf_push_reassemble A.repAlloc vcap vptr (ps.take k) ps[k]
        (by rw [htake_len]; exact hk_cap) hvcap63 hvptr_ne
      unfold vecHeader
      simp only [wp_norm, arm64_norm, hsp_eq, hx20, hx23, hx27, hx28, hx21, hx21_next,
        hslot_off, htake_len, htake_succ, hdone, ← hps_len, List.take_length,
        BitVec.add_assoc, BitVec.reduceAdd] at hpush ⊢
      exact entail_with_frame_p
        (F := (((fspOf s0 + 784#64) ↦₆₄ vcap) ∗ ((fspOf s0 + 792#64) ↦₆₄ vptr) ∗
            ((fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 ps.length)) ∗ A.pool lim st s ∗ FrameRest) hpush
    refine hexit _ ⟨?_, ?_, ?_, ?_, hinv', ?_, hsp0, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ hvcap_ne hvcap63
    · simp only [wp_norm, arm64_norm, bne, hx22, hx26, hx9_eq, hcmp_end, hdone, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, *]
    · simp only [wp_norm, arm64_norm, hrun]
    · simp only [wp_norm, arm64_norm, hsp_eq]
    · simp only [wp_norm, arm64_norm, hfp]
    · simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs
    · exact fsp_spAligned hsp0 (by simp only [wp_norm, arm64_norm, hsp_eq])
    · simp only [wp_norm, arm64_norm, hx19]
    · simp only [wp_norm, arm64_norm, hx20]
    · simp only [wp_norm, arm64_norm, hx21, hx21_next, hdone]
    · simp only [wp_norm, arm64_norm, hx24]
    · simp only [wp_norm, arm64_norm, htr]
    · simp only [wp_norm, arm64_norm, hfs]
  · have hk1_lt : k + 1 < n := by omega
    have hne_end : n ≠ k + 1 := by omega
    refine sepWPp_seq_codeOk_vm (mid := m2At (blkPl_617).base 0x120) hinv fun _m_strip => ?_
    wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, bne, hx22, hx26, hx9_eq, hcmp_end, hne_end, decide_false, Bool.not_false, ↓reduceIte, *])
      (hrun := by simp only [wp_norm, arm64_norm, *])
    intro _m_real hnsp hinv'
    have hpool' : A.pool lim st _ = A.pool lim st s :=
      A.pool_transport lim st _ _ (hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    apply sepWPp_mono_pre_sp (fsp := fspOf s0)
      (F := fun sp => vecHeader (sp + 0x310#64) vcap vptr (BitVec.ofNat 64 (k + 1)) ∗
        argsBuf A.repAlloc vcap vptr (ps.take (k + 1)) ∗ A.pool lim st _ ∗ FrameRest)
    · simp only [wp_norm, arm64_norm, hsp_eq]
    · rw [hpool']
      have hpush := argsBuf_push_reassemble A.repAlloc vcap vptr (ps.take k) ps[k]
        (by rw [htake_len]; exact hk_cap) hvcap63 hvptr_ne
      unfold vecHeader
      simp only [wp_norm, arm64_norm, hsp_eq, hx20, hx23, hx27, hx28, hx21, hx21_next,
        hslot_off, htake_len, htake_succ, BitVec.add_assoc, BitVec.reduceAdd] at hpush ⊢
      exact entail_with_frame_p
        (F := (((fspOf s0 + 784#64) ↦₆₄ vcap) ∗ ((fspOf s0 + 792#64) ↦₆₄ vptr) ∗
            ((fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 (k + 1))) ∗ A.pool lim st s ∗ FrameRest) hpush
    refine hloop _ hk1_lt ⟨⟨?_, ?_, ?_, ?_, hinv', ?_, hsp0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk_cap, hvcap_ne⟩
    · simp only [wp_norm, arm64_norm, bne, hx22, hx26, hx9_eq, hcmp_end, hne_end, decide_false, Bool.not_false, ↓reduceIte, *]
    · simp only [wp_norm, arm64_norm, hrun]
    · simp only [wp_norm, arm64_norm, hsp_eq]
    · simp only [wp_norm, arm64_norm, hfp]
    · simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs
    · exact fsp_spAligned hsp0 (by simp only [wp_norm, arm64_norm, hsp_eq])
    · simp only [wp_norm, arm64_norm, hx19]
    · simp only [wp_norm, arm64_norm, hx20]
    · simp only [wp_norm, arm64_norm, hx21, hx21_next]
    · simp only [wp_norm, arm64_norm, hx22]
    · simp only [wp_norm, arm64_norm, hx23, hx23_next, Nat.add_sub_cancel]
    · simp only [wp_norm, arm64_norm, hx24]
    · simp only [wp_norm, arm64_norm, hx25]
    · simp only [wp_norm, arm64_norm, htr]
    · simp only [wp_norm, arm64_norm, hfs]

/-! ## 4. Full Loop Iteration (`M+0x120`) & Induction (`M+0x120 → exit`) -/

set_option maxHeartbeats 800000 in
theorem step_collect_iter_grow_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 sf : State} {ret : BitVec 64} {stk hookStack resStack n k : Nat}
    {buf vcap vptr p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A lim hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk1 : 1 ≤ k) (hk_lt : k < n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (_hfull : k = vcap.toNat) (hvcap_ne : vcap ≠ 0#64)
    (hfit_grow : FitsEvents M lim st (m2GrowEventsAt k))
    (hsp0 : s0.spAligned = true)
    (hpc : sf.pc = (blkPl_617).base + 364#64) (hrun : sf.status = .Running)
    (hsp_eq : sf.sp = fspOf s0) (hfp : sf.readReg64 .fp = s0.sp - 0x60#64)
    (hinv : CodeOk sf.mem) (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0)
    (hx19 : sf.readReg64 (.gpr 19#5) = buf)
    (hx21 : sf.readReg64 (.gpr 21#5) = BitVec.ofNat 64 k)
    (hx22 : sf.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n))
    (hx23 : sf.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (16 * (k - 1)))
    (hx24 : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : sf.readReg64 (.gpr 25#5) = buf + 16#64)
    (hx26 : sf.readReg64 (.gpr 26#5) = buf + BitVec.ofNat 64 (16 * k))
    (hx27 : sf.readReg64 (.gpr 27#5) = (ps[k]'(by omega)).1)
    (hx28 : sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (ps[k]'(by omega)).2.length)
    (htr : sf.trace = s0.trace) (hfs : sf.fs = s0.fs)
    (hloop : ∀ (s' : State) (vcap' vptr' : BitVec 64),
      k + 1 < n →
      M2LoopInvPlaced CodeOk s0 s' n (k + 1) buf vcap' vptr' →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (vecHeader (s'.sp + 0x310#64) vcap' vptr' (BitVec.ofNat 64 (k + 1)) ∗
          argsBuf A.repAlloc vcap' vptr' (ps.take (k + 1)) ∗
          m2LoopMem A lim (M.stepEvents (m2GrowEventsAt k) st) s' s0 stk n buf p0 ps Statics)
        Q Qp oom)
    (hexit : ∀ (s' : State) (vcap' vptr' : BitVec 64),
      M2FramePlaced CodeOk s0 s' 0x2dc →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = vptr' →
      s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      vcap' ≠ 0#64 →
      vcap'.toNat * 16 < 2 ^ 63 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (vecHeader (s'.sp + 0x310#64) vcap' vptr' (BitVec.ofNat 64 n) ∗
          argsBuf A.repAlloc vcap' vptr' ps ∗
          m2LoopMem A lim (M.stepEvents (m2GrowEventsAt k) st) s' s0 stk n buf p0 ps Statics)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sf
      (((fspOf s0 + 440#64) ↦₃₂ 0#32) ∗ ((fspOf s0 + 444#64) ↦₃₂ 0#32) ∗
        ((fspOf s0 + 448#64) ↦₆₄ (ps[k]'(by omega)).1) ∗
        ((fspOf s0 + 456#64) ↦₆₄ BitVec.ofNat 64 (ps[k]'(by omega)).2.length) ∗
        ((fspOf s0 + 784#64) ↦₆₄ vcap) ∗ ((fspOf s0 + 792#64) ↦₆₄ vptr) ∗
        ((fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        argsBuf A.repAlloc vcap vptr (ps.take k) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        memRegion (fspOf s0) 0x1b8 ∗
        memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
        memRegion (fspOf s0 + 0x328#64) 0x158 ∗
        mainSaved s0 ∗
        stackAt (fspOf s0) (stk - mainFrameSize) ∗
        A.pool lim st sf ∗ Statics) Q Qp oom := by
  have hk_ps : k < ps.length := by omega
  have htake_len : (ps.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk_ps)
  have hflat_div : (flatSliceBytes (ps.take k)).length / 16 = k := by
    rw [flatSliceBytes_length, htake_len]; omega
  apply sepWPp_mono_pre
    (P' := vec16At A.repAlloc (fspOf s0 + 0x310#64) vcap vptr (flatSliceBytes (ps.take k)) ∗
      m2LoopMem A lim st sf s0 stk n buf p0 ps Statics)
  · have hsret : ((fspOf s0 + 440#64) ↦₃₂ 0#32) ∗ ((fspOf s0 + 444#64) ↦₃₂ 0#32) ∗
        ((fspOf s0 + 448#64) ↦₆₄ ps[k].1) ∗ ((fspOf s0 + 456#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ⊢
        memRegion (fspOf s0 + 0x1b8#64) 24 := by
      simpa only [pointsTo64_zero_eq_pair32, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd] using
        words_to_memRegion_24 (fspOf s0 + 0x1b8#64) 0#64 ps[k].1 (BitVec.ofNat 64 ps[k].2.length)
    have hv16 : (vecHeader (fspOf s0 + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        argsBuf A.repAlloc vcap vptr (ps.take k)) ⊢
        vec16At A.repAlloc (fspOf s0 + 0x310#64) vcap vptr (flatSliceBytes (ps.take k)) := by
      simpa only [htake_len] using
        argsBuf_to_vec16At A.repAlloc (fspOf s0 + 0x310#64) vcap vptr (ps.take k) hvcap_ne
    dsimp only [m2LoopMem, m2LoopRest]
    unfold vecHeader at hv16
    simp only [wp_norm, arm64_norm, hsp_eq, BitVec.add_assoc, BitVec.reduceAdd] at hsret hv16 ⊢
    exact Entails.trans
      (entail_with_frame_p
        (F := ((fspOf s0 + 784#64) ↦₆₄ vcap ∗ (fspOf s0 + 792#64) ↦₆₄ vptr ∗
            (fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          argsBuf A.repAlloc vcap vptr (ps.take k) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 464#64) 320 ∗
          memRegion (fspOf s0 + 808#64) 344 ∗
          mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool lim st sf ∗ Statics) hsret)
      (entail_with_frame_p
        (F := argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 440#64) 24 ∗
          memRegion (fspOf s0 + 464#64) 320 ∗ memRegion (fspOf s0 + 808#64) 344 ∗
          mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool lim st sf ∗ Statics) hv16)
  refine sepWPp_seq_codeOk_vm (mid := lsmpl.base 561) hinv fun _m_strip => ?_
  wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp only [wp_norm, arm64_norm, *])
  intro _m_real hnsp4 hinv4
  have hpool4 : A.pool lim st sf = A.pool lim st _ :=
    (A.pool_transport lim st _ _ (hnsp4.toVmPreserved (by simp only [wp_norm, arm64_norm]))).symm
  have _hvcap62 : 16 * vcap.toNat < 2 ^ 62 := by omega
  have hstk_res := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := resStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  let rcall : Reserve16Call :=
    { v := fspOf s0 + 0x310#64, cap := vcap, ptr := vptr, bs := flatSliceBytes (ps.take k) }
  have hevs_eq : reserve16Events rcall = m2GrowEventsAt k :=
    reserve16Events_eq_m2GrowEventsAt hk_ps _hfull hvcap_ne
  have hfit_rcall : FitsEnv M lim st (Reserve16Env rcall) := by
    rintro _ rfl
    rwa [hevs_eq]
  apply main_call_rocl (s0 := s0) (CodeOk := CodeOk)
    (rcall, st)
    env.res16_ok hinv4
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
    (fsp_spAligned hsp0 (by simp only [wp_norm, arm64_norm, hsp_eq]))
    (ret_pc := (blkPl_617).base + 388#64)
    (by simp only [wp_norm, arm64_norm])
    (F := argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1b8#64) 24 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
      Statics)
  · have hfit_eq : FitsEnv M lim st (Reserve16Env rcall) = True :=
      propext ⟨fun _ => trivial, fun _ => hfit_rcall⟩
    dsimp only [reserve16Spec, m2LoopMem, m2LoopRest]
    rw [hfit_eq, hstk_res, hpool4, fspOf_def]
    dsimp only [rcall]
    have hvcap_eq : vcap = BitVec.ofNat 64 k := by rw [_hfull]; simp
    have hsz : 16 * (k + 1) < 4611686018427387904 := by omega
    have hcap62 : 16 * (BitVec.ofNat 64 k).toNat < 4611686018427387904 := by
      rw [← hvcap_eq]; exact _hvcap62
    apply Entails.of_eq
    simp only [wp_norm, arm64_norm, hsp_eq, fspOf_def, hx21, hvcap_eq, hflat_div, hsz, hcap62,
      and_self, true_and, and_true, pure_true, emp_sepConj, BitVec.add_assoc, BitVec.reduceAdd]
    try sep_ac_rfl
  intro sf2 hinv5 hpc2 hrun2 hsp2 hcs2
  have hsp2_eq : sf2.sp = fspOf s0 := by simpa only [wp_norm, arm64_norm, hsp_eq] using hsp2
  clear hsp2
  have hx19_2 : sf2.readReg64 (.gpr 19#5) = buf := by
    rw [cs_x19 hcs2]; simp only [wp_norm, arm64_norm, hx19]
  have hx21_2 : sf2.readReg64 (.gpr 21#5) = BitVec.ofNat 64 k := by
    rw [cs_x21 hcs2]; simp only [wp_norm, arm64_norm, hx21]
  have hx22_2 : sf2.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n) := by
    rw [cs_x22 hcs2]; simp only [wp_norm, arm64_norm, hx22]
  have hx23_2 : sf2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (16 * (k - 1)) := by
    rw [cs_x23 hcs2]; simp only [wp_norm, arm64_norm, hx23]
  have hx24_2 : sf2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
    rw [cs_x24 hcs2]; simp only [wp_norm, arm64_norm, hx24]
  have hx25_2 : sf2.readReg64 (.gpr 25#5) = buf + 16#64 := by
    rw [cs_x25 hcs2]; simp only [wp_norm, arm64_norm, hx25]
  have hx26_2 : sf2.readReg64 (.gpr 26#5) = buf + BitVec.ofNat 64 (16 * k) := by
    rw [cs_x26 hcs2]; simp only [wp_norm, arm64_norm, hx26]
  have hx27_2 : sf2.readReg64 (.gpr 27#5) = ps[k].1 := by
    rw [cs_x27 hcs2]; simp only [wp_norm, arm64_norm, hx27]
  have hx28_2 : sf2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 ps[k].2.length := by
    rw [cs_x28 hcs2]; simp only [wp_norm, arm64_norm, hx28]
  have hfp_2 : sf2.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [cs_fp hcs2]; simp only [wp_norm, arm64_norm, hfp]
  have hvregs_2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
    calleeSavedVRegs_preserve
      (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs) hcs2
  have hs2_aligned : sf2.spAligned = true := fsp_spAligned hsp0 hsp2_eq
  have hsp0_keep : Unit → s0.spAligned = true := fun () => hsp0
  clear hpc hrun hsp0 hpool4 hnsp4
  dsimp only [reserve16Spec]
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun evs => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨htr2_raw, hfs2_raw, hevs_rcall⟩ => ?_
  have hevs_val : evs = m2GrowEventsAt k := hevs_rcall.trans hevs_eq
  subst hevs_val
  have htr2 : sf2.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr] using htr2_raw
  have hfs2 : sf2.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs] using hfs2_raw
  clear htr2_raw hfs2_raw
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun cap' => sepWPp_exists_elim fun p' => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine sepWPp_pure_elim fun hfit => ?_
  dsimp only [rcall] at hfit ⊢
  apply sepWPp_mono_pre
    (P' := ⌜cap' ≠ 0 ∧ k < cap'.toNat⌝ ∗
      (vecHeader (sf2.sp + 0x310#64) cap' p' (BitVec.ofNat 64 k) ∗
        argsBuf A.repAlloc cap' p' (ps.take k) ∗
        m2LoopMem A lim (M.stepEvents (m2GrowEventsAt k) st) sf2 s0 stk n buf p0 ps Statics))
  · have hunpack := vec16At_to_argsBuf A.repAlloc (fspOf s0 + 0x310#64) cap' p' (ps.take k) hfit
    dsimp only [m2LoopMem, m2LoopRest]
    simp only [htake_len] at hunpack
    rw [hstk_res]
    simp only [wp_norm, arm64_norm, hsp_eq, hsp2_eq, BitVec.add_assoc, BitVec.reduceAdd] at hunpack ⊢
    exact entail_with_frame_p
      (F := A.pool lim (M.stepEvents (m2GrowEventsAt k) st) sf2 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) resStack ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x1b8 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 440#64) 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 464#64) 320 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 808#64) 344 ∗
        mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - resStack) ∗
        Statics) hunpack
  refine sepWPp_pure_elim fun ⟨_, hk_cap'⟩ => ?_
  unfold vecHeader
  simp only [wp_norm, arm64_norm, hsp2_eq, BitVec.add_assoc, BitVec.reduceAdd]
  refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 328#64) hinv5 fun _m_strip => ?_
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
  intro _m_real hnsp6 hinv6
  have hpool6 : A.pool lim (M.stepEvents (m2GrowEventsAt k) st) _ =
      A.pool lim (M.stepEvents (m2GrowEventsAt k) st) sf2 :=
    A.pool_transport lim _ _ _ (hnsp6.toVmPreserved (by simp only [wp_norm, arm64_norm]))
  apply sepWPp_mono_pre_sp (fsp := fspOf s0)
    (F := fun sp => vecHeader (sp + 0x310#64) cap' p' (BitVec.ofNat 64 k) ∗
      argsBuf A.repAlloc cap' p' (ps.take k) ∗
      A.pool lim (M.stepEvents (m2GrowEventsAt k) st) _ ∗
      m2LoopRest A.repAlloc s0 stk n buf p0 ps Statics)
  · simp only [wp_norm, arm64_norm, hsp2_eq]
  · rw [hpool6]
    apply Entails.of_eq
    unfold vecHeader m2LoopMem
    simp only [wp_norm, arm64_norm, hsp2_eq, BitVec.add_assoc, BitVec.reduceAdd]
    try sep_ac_rfl
  refine step_collect_iter_tail_placed
    ⟨?_, ?_, ?_, ?_, hinv6, ?_, hsp0_keep (), ?_⟩ hk1 hk_lt hn_le hps_len hk_cap'
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun s' hk1_lt hinv' => hloop s' cap' p' hk1_lt hinv')
    (fun s' hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63' =>
      hexit s' cap' p' hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63')
  · simp only [wp_norm, arm64_norm, *]; try bv_omega
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hrun2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp2_eq]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_2]
  · simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_2
  · exact fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp2_eq])
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_2]
  · rfl
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx21_2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx22_2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx25_2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx26_2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx27_2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx28_2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr2]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfs2]

set_option maxHeartbeats 800000 in
theorem step_collect_iter_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {ret : BitVec 64} {stk hookStack resStack n k : Nat}
    {buf vcap vptr p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A lim hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk1 : 1 ≤ k) (hk_lt : k < n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hascii : ∀ b ∈ (ps[k]'(by omega)).2, b.toNat < 128)
    (hfit : FitsEnv M lim st (M2CollectLoopEnv n k))
    (hinv_loop : M2LoopInvPlaced CodeOk s0 s n k buf vcap vptr)
    (hloop : ∀ (s' : State) (vcap' vptr' : BitVec 64) (evs : List AllocEvent),
      k + 1 < n →
      (evs = [] ∨ evs = m2GrowEventsAt k) →
      FitsEnv M lim (M.stepEvents evs st) (M2CollectLoopEnv n (k + 1)) →
      M2LoopInvPlaced CodeOk s0 s' n (k + 1) buf vcap' vptr' →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (vecHeader (s'.sp + 0x310#64) vcap' vptr' (BitVec.ofNat 64 (k + 1)) ∗
          argsBuf A.repAlloc vcap' vptr' (ps.take (k + 1)) ∗
          m2LoopMem A lim (M.stepEvents evs st) s' s0 stk n buf p0 ps Statics) Q Qp oom)
    (hexit : ∀ (s' : State) (vcap' vptr' : BitVec 64) (evs : List AllocEvent),
      (evs = [] ∨ evs = m2GrowEventsAt k) →
      M2FramePlaced CodeOk s0 s' 0x2dc →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = vptr' →
      s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      vcap' ≠ 0#64 →
      vcap'.toNat * 16 < 2 ^ 63 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (vecHeader (s'.sp + 0x310#64) vcap' vptr' (BitVec.ofNat 64 n) ∗
          argsBuf A.repAlloc vcap' vptr' ps ∗
          m2LoopMem A lim (M.stepEvents evs st) s' s0 stk n buf p0 ps Statics) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
      (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        argsBuf A.repAlloc vcap vptr (ps.take k) ∗
        m2LoopMem A lim st s s0 stk n buf p0 ps Statics) Q Qp oom := by
  have hk_ps : k < ps.length := by omega
  rcases hinv_loop with ⟨⟨hpc, hrun, hsp_eq, hfp, hinv, hvregs, hsp0, hs_aligned⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, htr, hfs, hk_le_cap, hvcap_ne⟩
  have hsp0_keep : Unit → s0.spAligned = true := fun () => hsp0
  clear hsp0
  have hx26_val : (buf + 16#64) + BitVec.ofNat 64 (16 * (k - 1)) = buf + BitVec.ofNat 64 (16 * k) := by
    rw [BitVec.add_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 by rfl, ← BitVec.ofNat_add]
    congr 2; omega
  dsimp only [m2LoopMem, m2LoopRest]
  rw [argsBuf_focus A.repAlloc (BitVec.ofNat 64 n) buf ps k hk_ps]
  refine sepWPp_seq_codeOk_vm (mid := lsρ lsFromUtf8Sym) hinv fun _m_strip => ?_
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp only [wp_norm, arm64_norm, *])
  intro _m_real hnsp1 hinv1
  have hpool0 : A.pool lim st s = A.pool lim st _ :=
    (A.pool_transport lim st _ _ (hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm]))).symm
  rw [← argsBuf_focus A.repAlloc (BitVec.ofNat 64 n) buf ps k hk_ps]
  have hargv_eq := argvAtROP_focus (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps)
    (k + 1) (by simp [hps_len]; omega)
  simp only [List.getElem_cons_succ] at hargv_eq
  have hstk_utf8 := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := hookStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  apply main_call_rocl (s0 := s0) (CodeOk := CodeOk) (fspOf s0 + 0x1b8#64, ps[k].1, ps[k].2) env.utf8_ok hinv1
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
    (fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp_eq]))
    (ret_pc := (blkPl_617).base + 304#64)
    (by simp only [wp_norm, arm64_norm])
    (F := vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
      argsBuf A.repAlloc vcap vptr (ps.take k) ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      argvAtROPRest (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) (k + 1) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      A.pool lim st s ∗ Statics)
  · dsimp only [withVmPreserved, fromUtf8AsciiSpecRO]
    have hascii_eq : (∀ b ∈ ps[k].2, b.toNat < 128) = True :=
      propext ⟨fun _ => trivial, fun _ => hascii⟩
    rw [hargv_eq, hstk_utf8]
    apply Entails.of_eq
    simp only [wp_norm, arm64_norm, hsp_eq, hx25, hx23, hx26_val, hascii_eq,
      true_and, pure_true, emp_sepConj, BitVec.add_assoc, BitVec.reduceAdd]
    try sep_ac_rfl
  intro sf1 hinv2 hpc1 hrun1 hsp1 hcs1
  have hsp1_eq : sf1.sp = fspOf s0 := by simpa only [wp_norm, arm64_norm, hsp_eq] using hsp1
  clear hsp1
  have hx19_1 : sf1.readReg64 (.gpr 19#5) = buf := by
    rw [cs_x19 hcs1]; simp only [wp_norm, arm64_norm, hx19]
  have hx20_1 : sf1.readReg64 (.gpr 20#5) = vptr := by
    rw [cs_x20 hcs1]; simp only [wp_norm, arm64_norm, hx20]
  have hx21_1 : sf1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 k := by
    rw [cs_x21 hcs1]; simp only [wp_norm, arm64_norm, hx21]
  have hx22_1 : sf1.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n) := by
    rw [cs_x22 hcs1]; simp only [wp_norm, arm64_norm, hx22]
  have hx23_1 : sf1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (16 * (k - 1)) := by
    rw [cs_x23 hcs1]; simp only [wp_norm, arm64_norm, hx23]
  have hx24_1 : sf1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
    rw [cs_x24 hcs1]; simp only [wp_norm, arm64_norm, hx24]
  have hx25_1 : sf1.readReg64 (.gpr 25#5) = buf + 16#64 := by
    rw [cs_x25 hcs1]; simp only [wp_norm, arm64_norm, hx25]
  have hx26_1 : sf1.readReg64 (.gpr 26#5) = buf + BitVec.ofNat 64 (16 * k) := by
    rw [cs_x26 hcs1]; simp only [wp_norm, arm64_norm, hx25, hx23, hx26_val]
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
  clear hpool0 hnsp1 hvm_utf8
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨htr1_raw, hfs1_raw⟩ => ?_
  have htr1 : sf1.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr] using htr1_raw
  have hfs1 : sf1.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs] using hfs1_raw
  clear htr1_raw hfs1_raw
  apply sepWPp_mono_pre
    (P' := ((sf1.sp + 440#64) ↦₃₂ 0#32) ∗ ((sf1.sp + 444#64) ↦₃₂ 0#32) ∗
      ((sf1.sp + 448#64) ↦₆₄ ps[k].1) ∗ ((sf1.sp + 456#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ∗
      vecHeader (sf1.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
      argsBuf A.repAlloc vcap vptr (ps.take k) ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
      argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      stackAt (fspOf s0) (stk - mainFrameSize) ∗
      A.pool lim st sf1 ∗ Statics)
  · apply Entails.of_eq
    rw [hargv_eq, hpool1]
    simp only [wp_norm, arm64_norm, hsp_eq, hsp1_eq, pointsTo64_zero_eq_pair32,
      BitVec.add_assoc, BitVec.reduceAdd]
    rw [hstk_utf8]
    try sep_ac_rfl
  clear hpool1
  have hcmp_cap : (BitVec.ofNat 64 k == vcap) = decide (k = vcap.toNat) :=
    ofNat_beq_bv vcap (by omega)
  by_cases hfull : k = vcap.toNat
  · have hseq : FitsEnv M lim st (SeqEnv (· = m2GrowEventsAt k) (M2CollectLoopEnv n (k + 1))) :=
      hfit.mono fun _ hh => M2CollectLoopEnv.seq_grow hk1 hk_lt hh
    have hfit_grow : FitsEvents M lim st (m2GrowEventsAt k) := hseq.seq_left _ rfl
    have hfit_next : FitsEnv M lim (M.stepEvents (m2GrowEventsAt k) st) (M2CollectLoopEnv n (k + 1)) :=
      hseq.seq_right rfl
    unfold vecHeader
    simp only [wp_norm, arm64_norm, hsp1_eq, BitVec.add_assoc, BitVec.reduceAdd]
    refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 364#64) hinv2 fun _m_strip => ?_
    wp_step; wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, hx21_1, hcmp_cap, hfull, decide_true, ↓reduceIte, *]; try bv_omega)
      (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    intro _m_real hnsp3 hinv3
    have hpool3 : A.pool lim st _ = A.pool lim st sf1 :=
      A.pool_transport lim st _ _ (hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    apply sepWPp_mono_pre
      (P' := ((fspOf s0 + 440#64) ↦₃₂ 0#32) ∗ ((fspOf s0 + 444#64) ↦₃₂ 0#32) ∗
        ((fspOf s0 + 448#64) ↦₆₄ ps[k].1) ∗ ((fspOf s0 + 456#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ∗
        ((fspOf s0 + 784#64) ↦₆₄ vcap) ∗ ((fspOf s0 + 792#64) ↦₆₄ vptr) ∗
        ((fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        argsBuf A.repAlloc vcap vptr (ps.take k) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        memRegion (fspOf s0) 0x1b8 ∗
        memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
        memRegion (fspOf s0 + 0x328#64) 0x158 ∗
        mainSaved s0 ∗
        stackAt (fspOf s0) (stk - mainFrameSize) ∗
        A.pool lim st _ ∗ Statics)
    · rw [hpool3]
      apply Entails.of_eq
      simp only [wp_norm, arm64_norm, hsp1_eq, hfull, BitVec.add_assoc, BitVec.reduceAdd]
      try sep_ac_rfl
    refine step_collect_iter_grow_placed env hstk hstk64 hk1 hk_lt hn_le hps_len hfull hvcap_ne
      hfit_grow (hsp0_keep ())
      ?_ ?_ ?_ ?_ hinv3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun s' cap' p' hk1_lt hinv' =>
        hloop s' cap' p' (m2GrowEventsAt k) hk1_lt (Or.inr rfl) hfit_next hinv')
      (fun s' cap' p' hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63' =>
        hexit s' cap' p' (m2GrowEventsAt k) (Or.inr rfl) hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63')
    · simp only [wp_norm, arm64_norm, hx21_1, hcmp_cap, hfull, decide_true, ↓reduceIte, *]; try bv_omega
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hrun1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1_eq]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_1]
    · simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_1
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx21_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx22_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx25_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx26_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfull]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfull]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfs1]
  · have hk_cap : k < vcap.toNat := by omega
    have hfit_next : FitsEnv M lim st (M2CollectLoopEnv n (k + 1)) :=
      fun evs hevs => hfit evs (.skip hk_lt hevs)
    unfold vecHeader
    simp only [wp_norm, arm64_norm, hsp1_eq, BitVec.add_assoc, BitVec.reduceAdd]
    refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 328#64) hinv2 fun _m_strip => ?_
    wp_step; wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, hx21_1, hcmp_cap, hfull, decide_false, Bool.false_eq_true, ↓reduceIte, *]; try bv_omega)
      (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    intro _m_real hnsp3 hinv3
    have hpool3 : A.pool lim st _ = A.pool lim st sf1 :=
      A.pool_transport lim st _ _ (hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    apply sepWPp_mono_pre_sp (fsp := fspOf s0)
      (F := fun sp => vecHeader (sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        argsBuf A.repAlloc vcap vptr (ps.take k) ∗
        A.pool lim st _ ∗
        m2LoopRest A.repAlloc s0 stk n buf p0 ps Statics)
    · simp only [wp_norm, arm64_norm, hsp1_eq]
    · rw [hpool3]
      have hsret : ((fspOf s0 + 440#64) ↦₃₂ 0#32) ∗ ((fspOf s0 + 444#64) ↦₃₂ 0#32) ∗
          ((fspOf s0 + 448#64) ↦₆₄ ps[k].1) ∗ ((fspOf s0 + 456#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ⊢
          memRegion (fspOf s0 + 0x1b8#64) 24 := by
        simpa only [pointsTo64_zero_eq_pair32, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd] using
          words_to_memRegion_24 (fspOf s0 + 0x1b8#64) 0#64 ps[k].1 (BitVec.ofNat 64 ps[k].2.length)
      dsimp only [m2LoopRest]
      unfold vecHeader
      simp only [wp_norm, arm64_norm, hsp1_eq, BitVec.add_assoc, BitVec.reduceAdd] at hsret ⊢
      exact entail_with_frame_p
        (F := ((fspOf s0 + 784#64) ↦₆₄ vcap ∗ (fspOf s0 + 792#64) ↦₆₄ vptr ∗
            (fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          argsBuf A.repAlloc vcap vptr (ps.take k) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 464#64) 320 ∗
          memRegion (fspOf s0 + 808#64) 344 ∗
          mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool lim st sf1 ∗ Statics) hsret
    refine step_collect_iter_tail_placed
      ⟨?_, ?_, ?_, ?_, hinv3, ?_, hsp0_keep (), ?_⟩ hk1 hk_lt hn_le hps_len hk_cap
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun s' hk1_lt hinv' =>
        hloop s' vcap vptr [] hk1_lt (Or.inl rfl) hfit_next hinv')
      (fun s' hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63' =>
        hexit s' vcap vptr [] (Or.inl rfl) hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63')
    · simp only [wp_norm, arm64_norm, hx21_1, hcmp_cap, hfull, decide_false, Bool.false_eq_true, ↓reduceIte, *]; try bv_omega
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hrun1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1_eq]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_1]
    · simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_1
    · exact fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp1_eq])
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx21_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx22_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx25_1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx26_1]
    · rfl
    · rfl
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr1]
    · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfs1]

/-! ## 5. Full Loop Induction (`step_collect_loop_placed`: `k .. n → epilogue`) -/

theorem step_collect_loop_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {s0 : State} {ret : BitVec 64} {stk hookStack resStack n : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A lim hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hascii : ∀ k (hk : k < ps.length), ∀ b ∈ ps[k].2, b.toNat < 128)
    (rem : Nat) :
    ∀ (k : Nat) (st : M.σ) (s : State) (vcap vptr : BitVec 64),
      n - k = rem →
      1 ≤ k →
      k < n →
      FitsEnv M lim st (M2CollectLoopEnv n k) →
      M2LoopInvPlaced CodeOk s0 s n k buf vcap vptr →
      (∀ (s' : State) (vcap' vptr' : BitVec 64) (evs : List AllocEvent),
        M2CollectLoopEnv n k evs →
        M2FramePlaced CodeOk s0 s' (if n = 2 then 0x2f4 else 0x1b0) →
        s'.readReg64 (.gpr 19#5) = buf →
        s'.readReg64 (.gpr 20#5) = vptr' →
        s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
        s'.readReg64 (.gpr 23#5) = vcap' →
        s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
        s'.trace = s0.trace →
        s'.fs = s0.fs →
        vcap' ≠ 0#64 →
        SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
          (argsBuf A.repAlloc vcap' vptr' ps ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim (M.stepEvents evs st) s' ∗ Statics) Q Qp oom) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
        (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
          argsBuf A.repAlloc vcap vptr (ps.take k) ∗
          m2LoopMem A lim st s s0 stk n buf p0 ps Statics) Q Qp oom := by
  induction rem with
  | zero =>
    intro k _ _ _ _ hrem _ hk_lt _ _ _
    omega
  | succ rem ih =>
    intro k st s vcap vptr hrem hk1 hk_lt hfit hinv_loop hnext
    exact step_collect_iter_placed env hstk hstk64 hk1 hk_lt hn_le hps_len
      (hascii k (by omega)) hfit hinv_loop
      (fun s' vcap' vptr' evs₁ hk1_lt hevs₁ hfit₁ hinv' =>
        ih (k + 1) (M.stepEvents evs₁ st) s' vcap' vptr' (by omega) (by omega) hk1_lt hfit₁ hinv'
          (fun s'' vcap'' vptr'' evs₂ hevs₂ hf'' hx19'' hx20'' hx21'' hx23'' hx24'' htr'' hfs'' hvcap_ne'' => by
            rcases hevs₁ with rfl | rfl
            · simpa only [AllocCostModel.stepEvents_nil] using
                hnext s'' vcap'' vptr'' evs₂ (.skip hk_lt hevs₂)
                  hf'' hx19'' hx20'' hx21'' hx23'' hx24'' htr'' hfs'' hvcap_ne''
            · rw [← M.stepEvents_append]
              exact hnext s'' vcap'' vptr'' (m2GrowEventsAt k ++ evs₂) (.grow hk1 hk_lt hevs₂)
                hf'' hx19'' hx20'' hx21'' hx23'' hx24'' htr'' hfs'' hvcap_ne''))
      (fun s' vcap' vptr' evs₁ hevs₁ hf' hx19' hx20' hx21' hx24' htr' hfs' hvcap_ne' hvcap63' => by
        have hevs_k : M2CollectLoopEnv n k evs₁ := by
          rcases hevs₁ with rfl | rfl
          · exact .skip hk_lt (M2CollectLoopEnv.nil n (k + 1))
          · simpa only [List.append_nil] using
              M2CollectLoopEnv.grow hk1 hk_lt (M2CollectLoopEnv.nil n (k + 1))
        apply sepWPp_mono_pre
          (P' := vecHeader (s'.sp + 0x310#64) vcap' vptr' (BitVec.ofNat 64 n) ∗
            memRegion s'.sp 0x1b8 ∗
            memRegion (s'.sp + 0x1b8#64) 24 ∗
            memRegion (s'.sp + 0x1d0#64) 0x140 ∗
            memRegion (s'.sp + 0x328#64) 0x158 ∗
            A.pool lim (M.stepEvents evs₁ st) s' ∗
            (argsBuf A.repAlloc vcap' vptr' ps ∗
              argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
              argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
              mainSaved s0 ∗
              stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
              Statics))
        · dsimp only [m2LoopMem, m2LoopRest]
          apply Entails.of_eq
          simp only [← hf'.sp, BitVec.add_assoc, BitVec.reduceAdd]
          sep_ac_rfl
        exact step_collect_epilogue_placed
          hf' hx19' hx21' hx24' htr' hfs' hn_le hvcap_ne' hvcap63'
          (fun s'' hf'' hx19'' hx20'' hx21'' hx23'' hx24'' htr'' hfs'' => by
            apply sepWPp_mono_pre
              (P' := argsBuf A.repAlloc vcap' vptr' ps ∗
                argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗
                argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
                mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
                stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
                A.pool lim (M.stepEvents evs₁ st) s'' ∗ Statics)
            · exact Entails.of_eq (by sep_ac_rfl)
            exact hnext s'' vcap' vptr' evs₁ hevs_k hf'' hx19'' hx20'' hx21'' hx23'' hx24'' htr'' hfs'' hvcap_ne'))

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlacedBudget
