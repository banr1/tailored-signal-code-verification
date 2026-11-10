/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.Helpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Frame
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `main` M2 Collect Loop Steps (`M+0xc0 → M+0x2f4 / M+0x1b0`, Block `617`)

Verifies the OOM panic handler, `Vec<&str>` push loop (`from_utf8` and `reserve16`), and loop
epilogue of `main`'s argument collection on Block `617` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open M2Steps

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace M2StepsPlaced

/-- Callee contracts for `M2Collect` on Block `617` under `[LibsignalPlacement]`. -/
structure M2EnvPlaced [LibsignalPlacement] (H : LibsignalHooks) (A : RustAlloc)
    (hookStack resStack : Nat) : Prop where
  shim_ok : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustNoAllocShimSymCli)
    (withLsRoCl lsmpl
      (withStack CryptoVerification.LibsignalTripleRatchet.sessionShimSpec extHookStack).keepsFs)
  alloc_ok : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustAllocSymCli)
    (withLsRoCl lsmpl (rustAllocSpecWithStack A extHookStack).keepsFs)
  utf8_ok : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsFromUtf8Sym)
    (withLsRoCl lsmpl (fromUtf8AsciiSpec hookStack))
  res16_ok : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 561)
    (withLsRoCl lsmpl (reserve16Spec A resStack))
  panic_ext : ((blkPC_617).rebase (blkPl_617).base H).externAt? (lsρ lsHandleErrorSymMain) =
    some Rust.panicked

theorem m2EnvPlaced_init [LibsignalPlacement] {H : LibsignalHooks} {A : RustAlloc}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    M2EnvPlaced H A hookStack resStack where
  shim_ok := hc.allocFs.shim_rocl (prog := lsProg_617 H) (i := 617) extHookStack (Nat.le_refl _) (by decide)
  alloc_ok := main_alloc_fs_placed_ok hc.allocFs
  utf8_ok := main_fromUtf8_placed_ok hc
  res16_ok := main_reserve16_placed_ok hc
  panic_ext := main_panic_handle_error_placed hc

/-- Relocatable machine invariant at offset `off` inside Block `617` (`main`). -/
structure M2FramePlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (off : Nat) : Prop where
  pc : s.pc = (blkPl_617).base + BitVec.ofNat 64 off
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  inv : CodeOk s.mem
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true
  s_aligned : s.spAligned = true

/-! ## 1. OOM Panic Handler (`M+0xff0 .. M+0xff8`) -/

theorem step_collect_panic_placed [LibsignalPlacement] {H : LibsignalHooks}
    {A : RustAlloc} {hookStack resStack : Nat} {s0 s : State} {ret : BitVec 64}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A hookStack resStack)
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
    {H : LibsignalHooks}
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
        (locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗ Rest) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
      (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 n) ∗
        memRegion s.sp 0x1b8 ∗
        memRegion (s.sp + 0x1b8#64) 24 ∗
        memRegion (s.sp + 0x1d0#64) 0x140 ∗
        memRegion (s.sp + 0x328#64) 0x158 ∗
        Rest)
      Q Qp oom := by
  rcases hf with ⟨hpc, hrun, hsp_eq, hfp, hinv, hvregs, hsp0, hs_aligned⟩
  have hcmn : (vcap + 1#64 == 0#64) = false := vcap_add_one_beq_zero_false (by omega)
  have hmax : (vcap == 0xffffffffffffffff#64) = false := vcap_beq_max_false (by omega)
  have hcmp2 : (BitVec.ofNat 64 n == 2#64) = decide (n = 2) :=
    ofNat_beq_ofNat (by omega) (by decide)
  unfold vecHeader
  apply sepWPp_seq_codeOk (CodeOk := CodeOk)
    (mid := (blkPl_617).base + BitVec.ofNat 64 (if n = 2 then 0x2f4 else 0x1b0)) hinv
  wp_steps
  apply SepWP.done
    (by
      by_cases hn2 : n = 2
      · simp only [wp_norm, arm64_norm, bne, hcmn, hmax, hx21, hcmp2, hn2, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm, arm64_norm, bne, hcmn, hmax, hx21, hcmp2, hn2, decide_false, Bool.not_false, ↓reduceIte])
    (hrun := by simp only [wp_norm, arm64_norm, *])
  intro hinv'
  apply sepWPp_mono_pre (P' := locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗ Rest)
  · rw [locals_nil_split_m2]
    have hhdr := words_to_memRegion_24 (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
      vcap vptr (BitVec.ofNat 64 n)
    simp only [hsp_eq, BitVec.add_assoc, BitVec.reduceAdd] at hhdr ⊢
    exact entail_with_frame
      (F := memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 440 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 440#64) 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 464#64) 320 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize + 808#64) 344 ∗ Rest) hhdr
  refine hnext _ ⟨?_, ?_, ?_, ?_, hinv', ?_, hsp0, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · by_cases hn2 : n = 2
    · simp only [wp_norm, arm64_norm, bne, hcmn, hmax, hx21, hcmp2, hn2, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · simp only [wp_norm, arm64_norm, bne, hcmn, hmax, hx21, hcmp2, hn2, decide_false, Bool.not_false, ↓reduceIte]
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

/-- State bundle at loop header `M+0x120` with `1 ≤ k < n` elements already pushed into `Vec<&str>`. -/
structure M2LoopInvPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (s0 s : State)
    (n k : Nat) (buf vcap vptr : BitVec 64) : Prop where
  frame : M2FramePlaced CodeOk s0 s 0x120
  x19 : s.readReg64 (.gpr 19#5) = buf
  x20 : s.readReg64 (.gpr 20#5) = vptr
  x21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 k
  x22 : s.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n)
  x23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (16 * (k - 1))
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n
  x25 : s.readReg64 (.gpr 25#5) = buf + 16#64
  trace : s.trace = s0.trace
  fs : s.fs = s0.fs
  cap_ge : k ≤ vcap.toNat
  cap_ne : vcap ≠ 0#64

theorem step_collect_iter_tail_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks}
    {A : RustAlloc} {s0 s : State} {ret : BitVec 64} {n k : Nat} {buf vcap vptr : BitVec 64}
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
          argsBuf A vcap vptr (ps.take (k + 1)) ∗
          FrameRest) Q Qp oom)
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
          argsBuf A vcap vptr ps ∗
          FrameRest) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
      (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        argsBuf A vcap vptr (ps.take k) ∗
        FrameRest) Q Qp oom := by
  have hk_ps : k < ps.length := by omega
  have htake_len : (ps.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk_ps)
  have htake_succ : ps.take k ++ [ps[k]] = ps.take (k + 1) := (List.take_succ_eq_append_getElem hk_ps).symm
  rcases hf with ⟨hpc, hrun, hsp_eq, hfp, hinv, hvregs, hsp0, hs_aligned⟩
  apply sepWPp_mono_pre (sepConj_mono_right (sepConj_mono_left
    (argsBuf_push_split A vcap vptr (ps.take k) (by omega))))
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, htake_len]
  refine sepWPp_exists_elim fun w0 => sepWPp_exists_elim fun w1 => ?_
  rw [show vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
      (⌜vcap ≠ 0 ∧ vcap.toNat * 16 < 2 ^ 63 ∧ vptr ≠ 0⌝ ∗
        A.live vptr (vcap.toNat * 16) 8 ∗
        arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 vptr (ps.take k) ∗
        ((vptr + BitVec.ofNat 64 (16 * k)) ↦₆₄ w0) ∗
        (((vptr + BitVec.ofNat 64 (16 * k)) + 8#64) ↦₆₄ w1) ∗
        memRegion (vptr + BitVec.ofNat 64 ((k + 1) * 16)) ((vcap.toNat - (k + 1)) * 16)) ∗
      FrameRest =
      ⌜vcap ≠ 0 ∧ vcap.toNat * 16 < 2 ^ 63 ∧ vptr ≠ 0⌝ ∗
      (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        A.live vptr (vcap.toNat * 16) 8 ∗
        arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 vptr (ps.take k) ∗
        ((vptr + BitVec.ofNat 64 (16 * k)) ↦₆₄ w0) ∗
        (((vptr + BitVec.ofNat 64 (16 * k)) + 8#64) ↦₆₄ w1) ∗
        memRegion (vptr + BitVec.ofNat 64 ((k + 1) * 16)) ((vcap.toNat - (k + 1)) * 16) ∗
        FrameRest) by ac_rfl]
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
  · apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := m2At (blkPl_617).base 0x2dc) hinv
    wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, bne, hx22, hx26, hx9_eq, hcmp_end, hdone, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
      (hrun := by simp only [wp_norm, arm64_norm, *])
    intro hinv'
    apply sepWPp_mono_pre_sp (fsp := fspOf s0)
      (F := fun sp => vecHeader (sp + 0x310#64) vcap vptr (BitVec.ofNat 64 n) ∗
        argsBuf A vcap vptr ps ∗ FrameRest)
    · simp only [wp_norm, arm64_norm, hsp_eq]
    · have hpush := argsBuf_push_reassemble A vcap vptr (ps.take k) ps[k]
        (by rw [htake_len]; exact hk_cap) hvcap63 hvptr_ne
      unfold vecHeader
      simp only [wp_norm, arm64_norm, hsp_eq, hx20, hx23, hx27, hx28, hx21, hx21_next,
        hslot_off, htake_len, htake_succ, hdone, ← hps_len, List.take_length,
        BitVec.add_assoc, BitVec.reduceAdd] at hpush ⊢
      exact entail_with_frame
        (F := (((fspOf s0 + 784#64) ↦₆₄ vcap) ∗ ((fspOf s0 + 792#64) ↦₆₄ vptr) ∗
            ((fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 ps.length)) ∗ FrameRest) hpush
    refine hexit _ ⟨?_, ?_, ?_, ?_, hinv', ?_, hsp0, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ hvcap_ne hvcap63
    · simp only [wp_norm, arm64_norm, bne, hx22, hx26, hx9_eq, hcmp_end, hdone, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
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
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := m2At (blkPl_617).base 0x120) hinv
    wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, bne, hx22, hx26, hx9_eq, hcmp_end, hne_end, decide_false, Bool.not_false, ↓reduceIte])
      (hrun := by simp only [wp_norm, arm64_norm, *])
    intro hinv'
    apply sepWPp_mono_pre_sp (fsp := fspOf s0)
      (F := fun sp => vecHeader (sp + 0x310#64) vcap vptr (BitVec.ofNat 64 (k + 1)) ∗
        argsBuf A vcap vptr (ps.take (k + 1)) ∗ FrameRest)
    · simp only [wp_norm, arm64_norm, hsp_eq]
    · have hpush := argsBuf_push_reassemble A vcap vptr (ps.take k) ps[k]
        (by rw [htake_len]; exact hk_cap) hvcap63 hvptr_ne
      unfold vecHeader
      simp only [wp_norm, arm64_norm, hsp_eq, hx20, hx23, hx27, hx28, hx21, hx21_next,
        hslot_off, htake_len, htake_succ, BitVec.add_assoc, BitVec.reduceAdd] at hpush ⊢
      exact entail_with_frame
        (F := (((fspOf s0 + 784#64) ↦₆₄ vcap) ∗ ((fspOf s0 + 792#64) ↦₆₄ vptr) ∗
            ((fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 (k + 1))) ∗ FrameRest) hpush
    refine hloop _ hk1_lt ⟨⟨?_, ?_, ?_, ?_, hinv', ?_, hsp0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk_cap, hvcap_ne⟩
    · simp only [wp_norm, arm64_norm, bne, hx22, hx26, hx9_eq, hcmp_end, hne_end, decide_false, Bool.not_false, ↓reduceIte]
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
    {H : LibsignalHooks}
    {A : RustAlloc} {s0 sf : State} {ret : BitVec 64} {stk hookStack resStack n k : Nat}
    {buf vcap vptr p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk1 : 1 ≤ k) (hk_lt : k < n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (_hfull : k = vcap.toNat) (hvcap_ne : vcap ≠ 0#64)
    (hsp0 : s0.spAligned = true)
    (hpc : sf.pc = (blkPl_617).base + 0x16c#64) (hrun : sf.status = .Running)
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
    (hpanic : ∀ sf' Pf, allocFailedIn s0 sf' → Qp sf' Pf)
    (hloop : ∀ (s' : State) (vcap' vptr' : BitVec 64),
      k + 1 < n →
      M2LoopInvPlaced CodeOk s0 s' n (k + 1) buf vcap' vptr' →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (vecHeader (s'.sp + 0x310#64) vcap' vptr' (BitVec.ofNat 64 (k + 1)) ∗
          argsBuf A vcap' vptr' (ps.take (k + 1)) ∗
          m2LoopMem A s0 stk n buf p0 ps Statics) Q Qp oom)
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
          argsBuf A vcap' vptr' ps ∗
          m2LoopMem A s0 stk n buf p0 ps Statics) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sf
      (((fspOf s0 + 440#64) ↦₃₂ 0#32) ∗ ((fspOf s0 + 444#64) ↦₃₂ 0#32) ∗
        ((fspOf s0 + 448#64) ↦₆₄ (ps[k]'(by omega)).1) ∗
        ((fspOf s0 + 456#64) ↦₆₄ BitVec.ofNat 64 (ps[k]'(by omega)).2.length) ∗
        ((fspOf s0 + 784#64) ↦₆₄ vcap) ∗ ((fspOf s0 + 792#64) ↦₆₄ vptr) ∗
        ((fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        argsBuf A vcap vptr (ps.take k) ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        memRegion (fspOf s0) 0x1b8 ∗
        memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
        memRegion (fspOf s0 + 0x328#64) 0x158 ∗
        mainSaved s0 ∗
        stackAt (fspOf s0) (stk - mainFrameSize) ∗
        A.pool ∗ Statics) Q Qp oom := by
  have hk_ps : k < ps.length := by omega
  have htake_len : (ps.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk_ps)
  have hflat_div : (flatSliceBytes (ps.take k)).length / 16 = k := by
    rw [flatSliceBytes_length, htake_len]; omega
  apply sepWPp_mono_pre
    (P' := vec16At A (fspOf s0 + 0x310#64) vcap vptr (flatSliceBytes (ps.take k)) ∗
      m2LoopMem A s0 stk n buf p0 ps Statics)
  · have hsret : ((fspOf s0 + 440#64) ↦₃₂ 0#32) ∗ ((fspOf s0 + 444#64) ↦₃₂ 0#32) ∗
        ((fspOf s0 + 448#64) ↦₆₄ ps[k].1) ∗ ((fspOf s0 + 456#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ⊢
        memRegion (fspOf s0 + 0x1b8#64) 24 := by
      simpa only [pointsTo64_zero_eq_pair32, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd] using
        words_to_memRegion_24 (fspOf s0 + 0x1b8#64) 0#64 ps[k].1 (BitVec.ofNat 64 ps[k].2.length)
    have hv16 : (vecHeader (fspOf s0 + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        argsBuf A vcap vptr (ps.take k)) ⊢
        vec16At A (fspOf s0 + 0x310#64) vcap vptr (flatSliceBytes (ps.take k)) := by
      simpa only [htake_len] using argsBuf_to_vec16At A (fspOf s0 + 0x310#64) vcap vptr (ps.take k) hvcap_ne
    dsimp only [m2LoopMem]
    unfold vecHeader at hv16
    simp only [wp_norm, arm64_norm, hsp_eq, BitVec.add_assoc, BitVec.reduceAdd] at hsret hv16 ⊢
    exact Entails.trans
      (entail_with_frame
        (F := ((fspOf s0 + 784#64) ↦₆₄ vcap ∗ (fspOf s0 + 792#64) ↦₆₄ vptr ∗
            (fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          argsBuf A vcap vptr (ps.take k) ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 464#64) 320 ∗
          memRegion (fspOf s0 + 808#64) 344 ∗
          mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool ∗ Statics) hsret)
      (entail_with_frame
        (F := argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 440#64) 24 ∗
          memRegion (fspOf s0 + 464#64) 320 ∗ memRegion (fspOf s0 + 808#64) 344 ∗
          mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool ∗ Statics) hv16)
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsmpl.base 561) hinv
  wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp only [wp_norm, arm64_norm, *])
  intro hinv4
  have _hvcap62 : 16 * vcap.toNat < 2 ^ 62 := by omega
  have hstk_res := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := resStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  apply main_call_rocl (s0 := s0) (CodeOk := CodeOk)
    ({ v := fspOf s0 + 0x310#64, cap := vcap, ptr := vptr, bs := flatSliceBytes (ps.take k) } : Reserve16Call)
    env.res16_ok hinv4
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
    (fsp_spAligned hsp0 (by simp only [wp_norm, arm64_norm, hsp_eq]))
    (ret_pc := (blkPl_617).base + 0x184#64)
    (by simp only [wp_norm, arm64_norm])
    (F := argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1b8#64) 24 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
      Statics)
    (hpanic := fun sf_p R' _ hp => by
      dsimp only [reserve16Spec] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      apply hpanic
      have h1 := hp.1
      simp only [allocFailedIn, wp_norm, arm64_norm, htr] at h1 ⊢
      exact h1)
  · dsimp only [reserve16Spec, m2LoopMem]
    rw [hstk_res]
    have hvcap_eq : vcap = BitVec.ofNat 64 k := by rw [_hfull]; simp
    have hsz : 16 * (k + 1) < 4611686018427387904 := by omega
    have hcap62 : 16 * (BitVec.ofNat 64 k).toNat < 4611686018427387904 := by
      rw [← hvcap_eq]; exact _hvcap62
    apply Entails.of_eq
    simp only [wp_norm, arm64_norm, hsp_eq, hx21, hvcap_eq, hflat_div, hsz, hcap62, and_self,
      true_and, pure_true, emp_sepConj, BitVec.add_assoc, BitVec.reduceAdd]
    try ac_rfl
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
  clear hpc hrun hsp0
  dsimp only [reserve16Spec]
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨htr2_raw, hfs2_raw⟩ => ?_
  have htr2 : sf2.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr] using htr2_raw
  have hfs2 : sf2.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs] using hfs2_raw
  clear htr2_raw hfs2_raw
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun cap' => sepWPp_exists_elim fun p' => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine sepWPp_pure_elim fun hfit => ?_
  apply sepWPp_mono_pre
    (P' := ⌜cap' ≠ 0 ∧ k < cap'.toNat⌝ ∗
      (vecHeader (sf2.sp + 0x310#64) cap' p' (BitVec.ofNat 64 k) ∗
        argsBuf A cap' p' (ps.take k) ∗
        m2LoopMem A s0 stk n buf p0 ps Statics))
  · have hunpack := vec16At_to_argsBuf A (fspOf s0 + 0x310#64) cap' p' (ps.take k) hfit
    dsimp only [m2LoopMem]
    simp only [htake_len] at hunpack
    rw [hstk_res]
    simp only [wp_norm, arm64_norm, hsp_eq, hsp2_eq, BitVec.add_assoc, BitVec.reduceAdd] at hunpack ⊢
    exact entail_with_frame
      (F := A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) resStack ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
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
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x148#64) hinv5
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
  intro hinv6
  apply sepWPp_mono_pre_sp (fsp := fspOf s0)
    (F := fun sp => vecHeader (sp + 0x310#64) cap' p' (BitVec.ofNat 64 k) ∗
      argsBuf A cap' p' (ps.take k) ∗
      m2LoopMem A s0 stk n buf p0 ps Statics)
  · simp only [wp_norm, arm64_norm, hsp2_eq]
  · apply Entails.of_eq
    unfold vecHeader
    simp only [wp_norm, arm64_norm, hsp2_eq, BitVec.add_assoc, BitVec.reduceAdd]
    try ac_rfl
  refine step_collect_iter_tail_placed
    ⟨?_, ?_, ?_, ?_, hinv6, ?_, hsp0_keep (), ?_⟩ hk1 hk_lt hn_le hps_len hk_cap'
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun s' hk1_lt hinv' => hloop s' cap' p' hk1_lt hinv')
    (fun s' hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63' =>
      hexit s' cap' p' hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63')
  · simp only [wp_norm, arm64_norm]; try bv_omega
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
    {H : LibsignalHooks}
    {A : RustAlloc} {s0 s : State} {ret : BitVec 64} {stk hookStack resStack n k : Nat}
    {buf vcap vptr p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hk1 : 1 ≤ k) (hk_lt : k < n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hascii : ∀ b ∈ (ps[k]'(by omega)).2, b.toNat < 128)
    (hinv_loop : M2LoopInvPlaced CodeOk s0 s n k buf vcap vptr)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hloop : ∀ (s' : State) (vcap' vptr' : BitVec 64),
      k + 1 < n →
      M2LoopInvPlaced CodeOk s0 s' n (k + 1) buf vcap' vptr' →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (vecHeader (s'.sp + 0x310#64) vcap' vptr' (BitVec.ofNat 64 (k + 1)) ∗
          argsBuf A vcap' vptr' (ps.take (k + 1)) ∗
          m2LoopMem A s0 stk n buf p0 ps Statics) Q Qp oom)
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
          argsBuf A vcap' vptr' ps ∗
          m2LoopMem A s0 stk n buf p0 ps Statics) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
      (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        argsBuf A vcap vptr (ps.take k) ∗
        m2LoopMem A s0 stk n buf p0 ps Statics) Q Qp oom := by
  have hk_ps : k < ps.length := by omega
  rcases hinv_loop with ⟨⟨hpc, hrun, hsp_eq, hfp, hinv, hvregs, hsp0, hs_aligned⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, htr, hfs, hk_le_cap, hvcap_ne⟩
  have hsp0_keep : Unit → s0.spAligned = true := fun () => hsp0
  clear hsp0
  have hx26_val : (buf + 16#64) + BitVec.ofNat 64 (16 * (k - 1)) = buf + BitVec.ofNat 64 (16 * k) := by
    rw [BitVec.add_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 by rfl, ← BitVec.ofNat_add]
    congr 2; omega
  dsimp only [m2LoopMem]
  rw [argsBuf_focus A (BitVec.ofNat 64 n) buf ps k hk_ps]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsFromUtf8Sym) hinv
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp only [wp_norm, arm64_norm, *])
  intro hinv1
  rw [← argsBuf_focus A (BitVec.ofNat 64 n) buf ps k hk_ps]
  have hargv_eq := argvAtP_focus (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps)
    (k + 1) (by simp [hps_len]; omega)
  simp only [List.getElem_cons_succ] at hargv_eq
  have hstk_utf8 := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := hookStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  apply main_call_rocl (s0 := s0) (CodeOk := CodeOk) (fspOf s0 + 0x1b8#64, ps[k].1, ps[k].2) env.utf8_ok hinv1
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
    (fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp_eq]))
    (ret_pc := (blkPl_617).base + 0x130#64)
    (by simp only [wp_norm, arm64_norm])
    (F := vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
      argsBuf A vcap vptr (ps.take k) ∗
      argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      argvAtPRest (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) (k + 1) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      A.pool ∗ Statics)
  · dsimp only [fromUtf8AsciiSpec]
    have hascii_eq : (∀ b ∈ ps[k].2, b.toNat < 128) = True :=
      propext ⟨fun _ => trivial, fun _ => hascii⟩
    rw [hargv_eq, hstk_utf8]
    apply Entails.of_eq
    simp only [wp_norm, arm64_norm, hsp_eq, hx25, hx23, hx26_val, hascii_eq,
      true_and, pure_true, emp_sepConj, BitVec.add_assoc, BitVec.reduceAdd]
    try ac_rfl
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
  dsimp only [fromUtf8AsciiSpec]
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨htr1_raw, hfs1_raw⟩ => ?_
  have htr1 : sf1.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr] using htr1_raw
  have hfs1 : sf1.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs] using hfs1_raw
  clear htr1_raw hfs1_raw
  apply sepWPp_mono_pre
    (P' := ((sf1.sp + 440#64) ↦₃₂ 0#32) ∗ ((sf1.sp + 444#64) ↦₃₂ 0#32) ∗
      ((sf1.sp + 448#64) ↦₆₄ ps[k].1) ∗ ((sf1.sp + 456#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ∗
      vecHeader (sf1.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
      argsBuf A vcap vptr (ps.take k) ∗
      argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      stackAt (fspOf s0) (stk - mainFrameSize) ∗
      A.pool ∗ Statics)
  · apply Entails.of_eq
    rw [hargv_eq]
    simp only [wp_norm, arm64_norm, hsp_eq, hsp1_eq, pointsTo64_zero_eq_pair32,
      BitVec.add_assoc, BitVec.reduceAdd]
    rw [hstk_utf8]
    try ac_rfl
  have hcmp_cap : (BitVec.ofNat 64 k == vcap) = decide (k = vcap.toNat) :=
    ofNat_beq_bv vcap (by omega)
  by_cases hfull : k = vcap.toNat
  · unfold vecHeader
    simp only [wp_norm, arm64_norm, hsp1_eq, BitVec.add_assoc, BitVec.reduceAdd]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x16c#64) hinv2
    wp_step; wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, hx21_1, hcmp_cap, hfull, decide_true, ↓reduceIte, *]; try bv_omega)
      (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    intro hinv3
    apply sepWPp_mono_pre
      (P' := ((fspOf s0 + 440#64) ↦₃₂ 0#32) ∗ ((fspOf s0 + 444#64) ↦₃₂ 0#32) ∗
        ((fspOf s0 + 448#64) ↦₆₄ ps[k].1) ∗ ((fspOf s0 + 456#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ∗
        ((fspOf s0 + 784#64) ↦₆₄ vcap) ∗ ((fspOf s0 + 792#64) ↦₆₄ vptr) ∗
        ((fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        argsBuf A vcap vptr (ps.take k) ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        memRegion (fspOf s0) 0x1b8 ∗
        memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
        memRegion (fspOf s0 + 0x328#64) 0x158 ∗
        mainSaved s0 ∗
        stackAt (fspOf s0) (stk - mainFrameSize) ∗
        A.pool ∗ Statics)
    · apply Entails.of_eq
      simp only [wp_norm, arm64_norm, hsp1_eq, hfull, BitVec.add_assoc, BitVec.reduceAdd]
      try ac_rfl
    refine step_collect_iter_grow_placed env hstk hstk64 hk1 hk_lt hn_le hps_len hfull hvcap_ne (hsp0_keep ())
      ?_ ?_ ?_ ?_ hinv3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hpanic hloop hexit
    · simp only [wp_norm, arm64_norm, hx21_1, hcmp_cap, hfull, decide_true, ↓reduceIte]; try bv_omega
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
    unfold vecHeader
    simp only [wp_norm, arm64_norm, hsp1_eq, BitVec.add_assoc, BitVec.reduceAdd]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x148#64) hinv2
    wp_step; wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, hx21_1, hcmp_cap, hfull, decide_false, Bool.false_eq_true, ↓reduceIte, *]; try bv_omega)
      (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    intro hinv3
    apply sepWPp_mono_pre_sp (fsp := fspOf s0)
      (F := fun sp => vecHeader (sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
        argsBuf A vcap vptr (ps.take k) ∗
        m2LoopMem A s0 stk n buf p0 ps Statics)
    · simp only [wp_norm, arm64_norm, hsp1_eq]
    · have hsret : ((fspOf s0 + 440#64) ↦₃₂ 0#32) ∗ ((fspOf s0 + 444#64) ↦₃₂ 0#32) ∗
          ((fspOf s0 + 448#64) ↦₆₄ ps[k].1) ∗ ((fspOf s0 + 456#64) ↦₆₄ BitVec.ofNat 64 ps[k].2.length) ⊢
          memRegion (fspOf s0 + 0x1b8#64) 24 := by
        simpa only [pointsTo64_zero_eq_pair32, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd] using
          words_to_memRegion_24 (fspOf s0 + 0x1b8#64) 0#64 ps[k].1 (BitVec.ofNat 64 ps[k].2.length)
      dsimp only [m2LoopMem]
      unfold vecHeader
      simp only [wp_norm, arm64_norm, hsp1_eq, BitVec.add_assoc, BitVec.reduceAdd] at hsret ⊢
      exact entail_with_frame
        (F := ((fspOf s0 + 784#64) ↦₆₄ vcap ∗ (fspOf s0 + 792#64) ↦₆₄ vptr ∗
            (fspOf s0 + 800#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          argsBuf A vcap vptr (ps.take k) ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 464#64) 320 ∗
          memRegion (fspOf s0 + 808#64) 344 ∗
          mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool ∗ Statics) hsret
    refine step_collect_iter_tail_placed
      ⟨?_, ?_, ?_, ?_, hinv3, ?_, hsp0_keep (), ?_⟩ hk1 hk_lt hn_le hps_len hk_cap
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun s' hk1_lt hinv' => hloop s' vcap vptr hk1_lt hinv')
      (fun s' hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63' =>
        hexit s' vcap vptr hf' hx19' hx20' hx21' hx24' htr' hfs' hne' h63')
    · simp only [wp_norm, arm64_norm, hx21_1, hcmp_cap, hfull, decide_false, Bool.false_eq_true, ↓reduceIte]; try bv_omega
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
    {H : LibsignalHooks}
    {A : RustAlloc} {s0 : State} {ret : BitVec 64} {stk hookStack resStack n : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hascii : ∀ k (hk : k < ps.length), ∀ b ∈ ps[k].2, b.toNat < 128)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hnext : ∀ (s' : State) (vcap vptr : BitVec 64),
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
        (argsBuf A vcap vptr ps ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics) Q Qp oom)
    (rem : Nat) :
    ∀ (k : Nat) (s : State) (vcap vptr : BitVec 64),
      n - k = rem →
      1 ≤ k →
      k < n →
      M2LoopInvPlaced CodeOk s0 s n k buf vcap vptr →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
        (vecHeader (s.sp + 0x310#64) vcap vptr (BitVec.ofNat 64 k) ∗
          argsBuf A vcap vptr (ps.take k) ∗
          m2LoopMem A s0 stk n buf p0 ps Statics) Q Qp oom := by
  induction rem with
  | zero =>
    intro k _ _ _ hrem _ hk_lt _
    omega
  | succ rem ih =>
    intro k s vcap vptr hrem hk1 hk_lt hinv_loop
    exact step_collect_iter_placed env hstk hstk64 hk1 hk_lt hn_le hps_len
      (hascii k (by omega)) hinv_loop hpanic
      (fun s' vcap' vptr' hk1_lt hinv' =>
        ih (k + 1) s' vcap' vptr' (by omega) (by omega) hk1_lt hinv')
      (fun s' vcap' vptr' hf' hx19' hx20' hx21' hx24' htr' hfs' hvcap_ne' hvcap63' => by
        apply sepWPp_mono_pre
          (P' := vecHeader (s'.sp + 0x310#64) vcap' vptr' (BitVec.ofNat 64 n) ∗
            memRegion s'.sp 0x1b8 ∗
            memRegion (s'.sp + 0x1b8#64) 24 ∗
            memRegion (s'.sp + 0x1d0#64) 0x140 ∗
            memRegion (s'.sp + 0x328#64) 0x158 ∗
            (argsBuf A vcap' vptr' ps ∗
              argsBuf A (BitVec.ofNat 64 n) buf ps ∗
              argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
              mainSaved s0 ∗
              stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
              A.pool ∗ Statics))
        · dsimp only [m2LoopMem]
          apply Entails.of_eq
          simp only [← hf'.sp, BitVec.add_assoc, BitVec.reduceAdd]
          ac_rfl
        exact step_collect_epilogue_placed
          hf' hx19' hx21' hx24' htr' hfs' hn_le hvcap_ne' hvcap63'
          (fun s'' hf'' hx19'' hx20'' hx21'' hx23'' hx24'' htr'' hfs'' => by
            apply sepWPp_mono_pre
              (P' := argsBuf A vcap' vptr' ps ∗
                argsBuf A (BitVec.ofNat 64 n) buf ps ∗
                argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
                mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
                stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
                A.pool ∗ Statics)
            · exact Entails.of_eq (by ac_rfl)
            exact hnext s'' vcap' vptr' hf'' hx19'' hx20'' hx21'' hx23'' hx24'' htr'' hfs'' hvcap_ne'))

end M2StepsPlaced

end CryptoVerification.SignalSession.Cli.MainHops
