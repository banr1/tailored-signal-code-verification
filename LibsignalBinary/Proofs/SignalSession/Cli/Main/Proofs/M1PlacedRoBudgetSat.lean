/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Frame -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WP.Structural

/-!
# Honest `strlenSpecROSat` Sibling of `M1PlacedRoBudget`
(`M+0x00 → M+0xc0`, Block `617`, `Cli/Main/Proofs/M1PlacedRoBudgetSat.lean`)

- **Role**: `Role::Proof` (outside the TCB).
- **Overview**:
  Additive `*Sat` sibling of `M1PlacedRoBudget` consuming the honest SWAR-padded
  `ArgvPad.strlenSpecROSat hookStack` (discharged either from
  `HookSat H "strlen" (strlenSpecROSat hookStack)` or from real `muslStrlenWords` bytes) over
  `b2MainFrameFinePad` / `argvAtROPad` / `argvAtROPPad`:
  - `main_m1_ro_pool_placed_oom_proof_sat`: general OOM-callback Hop M1 proof;
  - `main_m1_ro_pool_placed_proof_sat`: total-correctness (`FitsEvents`) corollary;
  - `main_m1_ro_pool_placed_step1_sat` and `main_m1_ro_pool_placed_step1_of_sat`: invariant-threaded
    `St0 → St1` adapters;
  - `main_m1_ro_placed_proof_sat`: pool-erasing `ExitKPlaced` corollary.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1PlacedRoBudgetSat

open Arm64 ProofLib
open Arm64.Process (bytesOfString)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (allocFailedIn arrayAt)
open CryptoVerification.SignalSession
  (Inputs PrintableAsciiArg lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (CliInputsOk)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkLib_eq_617 blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtEntryPlaced AtM1EndPlaced AtRetPlaced InMainPlaced LsCodeInv argc_cmp_two argsBuf
   argsBufPartial argsBufPartial_close_slot argsBufPartial_finish argsBufPartial_open_slot
   argsBufPartial_zero argvFits_length_le argv_no_nul_at fsp_spAligned layoutOk_argsBuf locals
   locals_nil_eq loop_cmp_ne_true mPcPlaced_eq mPcPlaced_zero mProgPlaced mProgPlaced_eq
   mainFrameSize mainOom mainSaved main_call_rocl ofNat_16_beq_zero ofNat_16_toNat ofNat_lsr_60
   ofNat_shl_3 ofNat_shl_4 ofNat_succ_beq_zero ofNat_succ_sub_one sepWPp_of_mainOom
   sepWPp_seq_codeOk sliceRefAt stackAt_main_open subStack_split_extHook subStack_split_hook
   zero_store_entails_memRegion_480)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents NullAllowed OomPreserved RustCliAllocBudget
   VmPreserved rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (withStrlenPadRO)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad
  (StrlenPadOk argvAtROPPad argvAtROPPadPrefix argvAtROPPad_append argvAtROPad
   argvAtROPad_entails_argvAtROPPad b2MainFrameFinePad cStrAtROPad
   cStrAtRO_pad_entails_cStrAtROPad pointsToBytesRO_pad_entails_withStrlenPadRO
   strlenSpecROSat strlen_ro_sat_placed_ok_of_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (cStrAtRO strlenSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (ExitKPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
  (main_alloc_fs_placed_ok main_shim_fs_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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

@[local simp, local arm64_norm]
private theorem sp_sub_96_sub_1152_p (sp0 : BitVec 64) :
    (sp0 - 96#64) - 1152#64 = sp0 - 1248#64 := by
  rw [BitVec.sub_sub]; rfl

private theorem mainSaved_eq_sub_p (s0 : State) :
    mainSaved s0 =
      ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
      ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
      ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
  dsimp only [mainSaved]
  rw [BitVec.add_zero (s0.sp - 0x60#64),
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x08,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x10,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x18,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x20,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x28,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x30,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x38,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x40,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x48,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x50,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x58]

private theorem sepWPp_exists_left_p {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x : α, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hmx⟩ := hm
  exact h x R hmx hL

private theorem sepWPp_pure_third_p {prog : Program} {ret : BitVec 64} {s : State}
    {A B Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    {φ : Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ Rest) Q Qp oom) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ Rest) Q Qp oom :=
  SepWPp.congr_pre (by sep_ac_rfl) (SepWPp.pure_left h)

private theorem sepWPp_open_argvAtROPad_p {prog : Program} {ret : BitVec 64} {s : State}
    {base : BitVec 64} {strs : List (List (BitVec 8))} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ psAll : List (BitVec 64 × List (BitVec 8)),
      psAll.map (·.2) = strs →
      SepWPp prog ret s (argvAtROPPad base psAll ∗ Rest) Q Qp oom) :
    SepWPp prog ret s (argvAtROPad base strs ∗ Rest) Q Qp oom := by
  refine SepWPp.weaken_pre (sepConj_mono_left (argvAtROPad_entails_argvAtROPPad base strs)) ?_
  rw [sepExists_sepConj_left]
  apply sepWPp_exists_left_p
  intro psAll
  rw [sepConj_assoc]
  exact SepWPp.pure_left (h psAll)

private theorem sepWPp_open_cStrAtROPad_p {prog : Program} {ret : BitVec 64} {s : State}
    {pk : BitVec 64} {sk : List (BitVec 8)} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ pad : List (BitVec 8), StrlenPadOk pk sk pad →
      SepWPp prog ret s ((pk ↦ᵣ (sk ++ [0#8] ++ pad)) ∗ Rest) Q Qp oom) :
    SepWPp prog ret s (cStrAtROPad pk sk ∗ Rest) Q Qp oom := by
  unfold cStrAtROPad
  rw [sepExists_sepConj_left]
  apply sepWPp_exists_left_p
  intro pad
  rw [sepConj_assoc]
  exact SepWPp.pure_left (h pad)

private theorem sbfm_sxtw_eq_p {x : BitVec 64} {n : Nat}
    (hn : n ≤ 1820)
    (hx : x.setWidth 32 = BitVec.ofNat 32 (n + 1))
    (m1 m2 : BitVec 64) :
    (x >>> 0 &&& 4294967295#64 |||
      (if x.getLsbD 31 = true then m1 else 0#64) &&& m2) =
      BitVec.ofNat 64 (n + 1) := by
  have hx32 : x.toNat % 4294967296 = n + 1 := by
    have ht := congrArg BitVec.toNat hx
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at ht
    change x.toNat % 4294967296 = (n + 1) % 4294967296 at ht
    omega
  have h31 : x.getLsbD 31 = false := by
    show x.toNat.testBit 31 = false
    have hmod := Nat.testBit_mod_two_pow x.toNat 32 31
    change (x.toNat % 4294967296).testBit 31 = (decide (31 < 32) && x.toNat.testBit 31) at hmod
    rw [hx32, show decide (31 < 32) = true by decide, Bool.true_and] at hmod
    exact hmod.symm.trans (Nat.testBit_lt_two_pow (by omega : n + 1 < 2 ^ 31))
  have hushr : x >>> 0 = x := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [h31, hushr]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (4294967295#64).toNat = 2 ^ 32 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  change x.toNat % 4294967296 = (n + 1) % 2 ^ 64
  omega

private theorem ofNat_16_ule_max_true_p {n : Nat} (hn : n ≤ 1820) :
    (BitVec.ofNat 64 (16 * n)).ule 9223372036854775800#64 = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat]
  have h1 : (9223372036854775800#64).toNat = 9223372036854775800 := by decide
  rw [h1]
  omega

/-! ## Phase 1: Prologue & capacity check (`M+0x00 → M+0x5c`) -/

private theorem step_prologue_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {i : Inputs} {s0 : State} {stk : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hstk : mainFrameSize ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtEntryPlaced CodeOk i s0)
    (hn : i.argv.length ≤ 1820)
    (hnext : ∀ s1 : State,
      InMainPlaced CodeOk s0 s1 0x5c →
      s1.trace = s0.trace →
      s1.fs = s0.fs →
      (s1.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) →
      s1.readReg64 .x0 = s0.readReg64 .x0 →
      s1.readReg64 .x1 = s0.readReg64 .x1 →
      s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (16 * i.argv.length) →
      s1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (i.argv.length + 1) →
      s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s1
        (mainSaved s0 ∗
          memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          argvAtROPad (s0.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          A.pool lim st s1 ∗ Statics)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (b2MainFrameFinePad A lim st stk Statics i s0)
      Q Qp oom := by
  have hpc0 : s0.pc = (blkPl_617).base := mPcPlaced_zero ▸ hs0.pc
  have hrun0 : s0.status = .Running := hs0.run
  have hargc0 : (s0.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) := hs0.argc
  have hsp0 : s0.spAligned = true := hs0.spAligned
  have hsp0_al : (s0.sp &&& 15#64 == 0#64) = true := hsp0
  have hsp60_al : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0
  have hsp4e0_al : ((s0.sp - 1248#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1248#64 hsp0
  have hsxtw := sbfm_sxtw_eq_p hn hargc0 0xffff_ffff_ffff_ffff#64 0xffff_ffff_0000_0000#64
  have hbeq0 := ofNat_succ_beq_zero hn
  have hsub1 := ofNat_succ_sub_one i.argv.length
  have hlsr := ofNat_lsr_60 hn
  have hshl := ofNat_shl_4 hn
  have hule := ofNat_16_ule_max_true_p hn
  unfold b2MainFrameFinePad
  rw [stackAt_main_open s0.sp hstk hstk64]
  cells_unfold
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 92#64) hs0.inv fun _m_strip => ?_
  dsimp only [mainFrameSize]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply SepWP.exists_left; intro)
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, *]; try bv_omega)
    (by simp only [arm64_norm, *])
  intro _m_real hvm1 hinv1
  have hbase1 : InMainPlaced CodeOk s0 _ 0x5c :=
    { pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]; try bv_omega
      run := by simp only [arm64_norm, *]
      sp := by unfold mainFrameSize; simp only [arm64_norm, *]; try bv_omega
      fp := by simp only [arm64_norm, *]; try bv_omega
      inv := hinv1
      vregs := by simp only [calleeSavedVRegs, arm64_norm]
      spAligned := hsp0 }
  refine SepWPp.weaken_pre ?_
    (hnext _ hbase1
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hargc0])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]))
  rw [A.pool_transport lim st _ _ (hvm1.toVmPreserved (by simp only [wp_norm, arm64_norm]))]
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  refine Entails.trans
    (Entails.of_eq (Q := ((fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 0x478) ∗
      (mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗
        argvAtROPad (s0.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
        A.pool lim st s0 ∗ Statics))
      (by rw [mainSaved_eq_sub_p s0]; dsimp only [mainFrameSize]; sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left (zero_store_entails_memRegion_480 fsp))
    (Entails.of_eq (by sep_ac_rfl))

/-! ## Phase 2a: Fast-path early return `2` when `i.argv = []` (`M+0x5c → M+0xb80`) -/

private theorem step_empty_argv_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {i : Inputs} {s0 s1 : State} {stk : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    (hemp : i.argv = [])
    (hs1 : InMainPlaced CodeOk s0 s1 0x5c)
    (htr1 : s1.trace = s0.trace)
    (hfs1 : s1.fs = s0.fs)
    (hw0 : (s1.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1))
    (hx20 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (16 * i.argv.length))
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s1
      (mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        argvAtROPad (s0.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
        A.pool lim st s1 ∗ Statics)
      Q Qp (mainOom s0) := by
  rw [hemp] at hw0 hx20 ⊢
  simp only [List.length_nil, Nat.mul_zero, List.map_cons, List.map_nil] at hw0 hx20 ⊢
  have hpc1 : s1.pc = (blkPl_617).base + 92#64 := hs1.pc
  have hrun1 : s1.status = .Running := hs1.run
  have hsp1 : s1.sp = s0.sp - BitVec.ofNat 64 mainFrameSize := hs1.sp
  have hfp1 : s1.readReg64 .fp = s0.sp - 0x60#64 := hs1.fp
  have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hs1.vregs
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 2944#64) hs1.inv fun _m_strip => ?_
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, hw0, hx20, *]; try bv_omega)
    (by simp only [arm64_norm, *])
  intro _m_real hvm2 hinv2
  have hret : AtRetPlaced CodeOk s0 _ 2 :=
    { base :=
        { pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, hw0, hx20, *]; try bv_omega
          run := by simp only [arm64_norm, *]
          sp := by simp only [arm64_norm, hsp1]
          fp := by simp only [arm64_norm, hfp1]
          inv := hinv2
          vregs := by simpa only [calleeSavedVRegs, arm64_norm] using hv1
          spAligned := hs1.spAligned }
      w26 := by simp only [arm64_norm] }
  refine SepWPp.weaken_pre ?_
    (hexit _ st 2 hret ⟨rfl, hemp, by simp only [arm64_norm, htr1], by simp only [arm64_norm, hfs1]⟩)
  unfold CryptoVerification.SignalSession.Cli.MainHops.retMem
  dsimp only [RustCliAllocBudget.atState]
  rw [A.pool_transport lim st _ _ (hvm2.toVmPreserved (by simp only [wp_norm, arm64_norm]))]
  have hany : argvAtROPad (s0.readReg64 .x1) [bytesOfString "libsignal-cli"] ∗ Statics ⊢ anyHeap :=
    entails_anyHeap _
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hany))))

/-! ## Phase 2b: Allocate `args` buffer & setup loop registers (`M+0x5c → M+0xa4`) -/

private theorem step_alloc_buf_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {i : Inputs} {s0 s1 : State}
    {stk hookStack resStack : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc_alloc : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (h0 : 0 < i.argv.length)
    (hn : i.argv.length ≤ 1820)
    (hs1 : InMainPlaced CodeOk s0 s1 0x5c)
    (htr1 : s1.trace = s0.trace)
    (hfs1 : s1.fs = s0.fs)
    (hw0 : (s1.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1))
    (hx0 : s1.readReg64 .x0 = s0.readReg64 .x0)
    (hx1 : s1.readReg64 .x1 = s0.readReg64 .x1)
    (hx20 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (16 * i.argv.length))
    (hx22 : s1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (i.argv.length + 1))
    (hx24 : s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hoom_cb : ∀ s_pre sf R',
      s_pre.trace = s0.trace → s_pre.fs = s0.fs →
      sf.status = .OutOfMemory →
      ¬ FitsEvents M lim st (rustAllocEvents (16 * i.argv.length) 8) →
      OomPreserved s_pre sf →
      (sf.mem ⊨ anyHeap ∗ R') → (sf.mem ⊨ oom sf ∗ R'))
    (hnext : ∀ (s3 : State) (buf : BitVec 64),
      buf ≠ 0#64 →
      InMainPlaced CodeOk s0 s3 0xa4 →
      s3.trace = s0.trace →
      s3.fs = s0.fs →
      s3.readReg64 (.gpr 19#5) = buf →
      s3.readReg64 (.gpr 21#5) = s0.readReg64 .x1 + 8#64 →
      s3.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * 0) →
      s3.readReg64 (.gpr 23#5) = BitVec.ofNat 64 i.argv.length →
      s3.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length →
      s3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 0 →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s3
        (argsBufPartial A.repAlloc i.argv.length buf [] ∗
          mainSaved s0 ∗
          memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          argvAtROPad (s0.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st) s3 ∗ Statics)
        Q Qp oom) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s1
      (mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        argvAtROPad (s0.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
        A.pool lim st s1 ∗ Statics)
      Q Qp oom := by
  have hshim := main_shim_fs_placed_ok hc_alloc
  have halloc := main_alloc_fs_placed_ok hc_alloc
  have hpc1 : s1.pc = (blkPl_617).base + 92#64 := hs1.pc
  have hrun1 : s1.status = .Running := hs1.run
  have hsp1 : s1.sp = s0.sp - BitVec.ofNat 64 mainFrameSize := hs1.sp
  have hfp1 : s1.readReg64 .fp = s0.sp - 0x60#64 := hs1.fp
  have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hs1.vregs
  have hsp0 : s0.spAligned = true := hs1.spAligned
  have h16_nz := ofNat_16_beq_zero h0 hn
  have h16_toNat := ofNat_16_toNat hn
  have hlay := layoutOk_argsBuf h0 hn
  have hcmp2 := argc_cmp_two h0 hn
  have hsub1 := ofNat_succ_sub_one i.argv.length
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  -- 1. Step `0x5c .. 0x68` and call `shim`
  rw [subStack_split_extHook fsp hstk hstk64, mProgPlaced_eq]
  refine sepWPp_seq_codeOk (mid := lsρ lsRustNoAllocShimSymCli) hs1.inv ?_
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, hx20, h16_nz, *]; try bv_omega)
    (by simp only [arm64_norm, *])
  intro hinv_sh
  apply main_call_rocl (s0 := s0) (ret_pc := (blkPl_617).base + 108#64)
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            ((stk - mainFrameSize) - extHookStack) ∗
          mainSaved s0 ∗ memRegion fsp 0x480 ∗
          argvAtROPad (s0.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          A.pool lim st s1 ∗ Statics)
    () hshim hinv_sh
    (by simp only [arm64_norm, hx20, h16_nz, *]; try bv_omega)
    (by simp only [arm64_norm, *])
    (fsp_spAligned hsp0 (by simp only [arm64_norm, hsp1]; rfl))
    (by simp only [arm64_norm, hx20, h16_nz, *]; try bv_omega)
  · simp only [Spec.keepsFs, session2ShimBudgetSpecX, arm64_norm, hsp1]
    exact Entails.of_eq (by sep_ac_rfl)
  intro s_sh hinv_sh2 hpc_sh hrun_sh hsp_sh hcs_sh
  rcases hcs_sh with ⟨_, hx20_sh, _, hx22_sh, hx23_sh, hx24_sh, hx25_sh, _, _, _, hfp_sh, hv_sh⟩
  simp only [arm64_norm, hx0, hx1, hx20, hx22, hx24, hfp1, hsp1]
    at hx20_sh hx22_sh hx23_sh hx24_sh hx25_sh hfp_sh hv_sh hsp_sh
  simp only [Spec.keepsFs, session2ShimBudgetSpecX, arm64_norm, hsp1, sepConj_assoc]
  apply SepWPp.pure_left
  rintro ⟨hfs_sh_step, htr_sh_step, hvm_sh⟩
  have hfs_sh : s_sh.fs = s0.fs := by simpa only [arm64_norm, hfs1] using hfs_sh_step
  have htr_sh : s_sh.trace = s0.trace := by simpa only [arm64_norm, htr1] using htr_sh_step
  have hpool_sh : A.pool lim st s1 = A.pool lim st s_sh := by
    have h := (A.pool_transport lim st _ _ hvm_sh).symm
    simpa only [RustCliAllocBudget.pool_setPC_norm, RustCliAllocBudget.pool_writeReg64_norm] using h
  -- 2. Step `0x6c .. 0x78` and call `__rust_alloc(16 * n, 8)`
  refine sepWPp_seq_codeOk (mid := lsρ lsRustAllocSymCli) hinv_sh2 ?_
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, hpc_sh, *]; try bv_omega)
    (by simp only [arm64_norm, *])
  intro hinv_al
  refine main_call_rocl (s0 := s0) (ret_pc := (blkPl_617).base + 124#64)
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            ((stk - mainFrameSize) - extHookStack) ∗
          mainSaved s0 ∗ memRegion fsp 0x480 ∗
          argvAtROPad (s0.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          Statics)
    (16 * i.argv.length, 8, st) halloc hinv_al
    (by simp only [arm64_norm, hpc_sh, *]; try bv_omega)
    (by simp only [arm64_norm, *])
    (fsp_spAligned hsp0 (by simp only [arm64_norm, hsp_sh]; rfl))
    (by simp only [arm64_norm, hpc_sh, *]; try bv_omega)
    ?_ (hoom := ?_) (hnext := ?_)
  · dsimp only [Spec.keepsFs, rustAllocSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocBudgetSpecWithStack]
    simp only [arm64_norm, hx20_sh, h16_toNat, hsp_sh, ← hpool_sh, sepConj_assoc]
    refine Entails.pure_right ⟨⟨hlay, by decide⟩,
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 617 124#64
        (by decide) (by decide)⟩ ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf R' hst_oom hmoom
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocBudgetSpecWithStack] at hmoom
    rw [satisfies_pure_sepConj] at hmoom
    exact hoom_cb _ sf R'
      (by simp only [arm64_norm, htr_sh])
      (by simp only [arm64_norm, hfs_sh])
      hst_oom hmoom.1.1 hmoom.1.2
      (Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmoom.2)
  · intro s_al hinv_al2 hpc_al hrun_al hsp_al hcs_al
    rcases hcs_al with ⟨_, _, _, hx22_al, hx23_al, hx24_al, hx25_al, _, _, _, hfp_al, hv_al⟩
    simp only [arm64_norm, hx22_sh, hx23_sh, hx24_sh, hx25_sh, hfp_sh, hsp_sh]
      at hx22_al hx23_al hx24_al hx25_al hfp_al hv_al hsp_al
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocBudgetSpecWithStack]
    simp only [arm64_norm, hx20_sh, h16_toNat, hsp_sh, sepConj_assoc]
    apply SepWPp.pure_left
    rintro ⟨hfs_al_step, hacp⟩
    have hfs_al : s_al.fs = s0.fs := by simpa only [arm64_norm, hfs_sh] using hfs_al_step
    have htr_al : s_al.trace = s0.trace := by simpa only [arm64_norm, htr_sh] using hacp.2.1
    by_cases hnull : s_al.readReg64 .x0 = (0 : BitVec 64)
    · simp only [hnull, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_third_p
      intro hna
      unfold NullAllowed at hna
      omega
    · have hbeq_f : (s_al.readReg64 .x0 == 0#64) = false := beq_false_of_ne hnull
      simp only [hnull, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_third_p
      intro _hmod
      have hult2 : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5))).ult 2#32 = false := by
        change ((s0.readReg64 .x0).setWidth 32).ult 2#32 = false
        rw [← hx0, hw0]
        exact hcmp2
      -- 3. Step `0x7c .. 0xa0` to loop header `0xa4`
      refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 164#64) hinv_al2 fun _m_strip => ?_
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, hpc_al, hbeq_f, hx25_al, hult2, *]; try bv_omega)
        (by simp only [arm64_norm, *])
      intro _m_real hvm3 hinv3
      have hbase3 : InMainPlaced CodeOk s0 _ 0xa4 :=
        { pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, hpc_al, hbeq_f, hx25_al, hult2, *]; try bv_omega
          run := by simp only [arm64_norm, *]
          sp := by simp only [arm64_norm, hsp_al]; rfl
          fp := by simp only [arm64_norm, hfp_al]
          inv := hinv3
          vregs := by simp only [calleeSavedVRegs, arm64_norm] at hv_al hv_sh hv1 ⊢; exact hv_al.trans (hv_sh.trans hv1)
          spAligned := hsp0 }
      refine SepWPp.weaken_pre ?_
        (hnext _ (s_al.readReg64 .x0) hnull hbase3
          (by simp only [arm64_norm, htr_al])
          (by simp only [arm64_norm, hfs_al])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm, hx23_al])
          (by simp only [arm64_norm, Nat.mul_zero, BitVec.add_zero])
          (by simp only [arm64_norm, hx22_al, hsub1])
          (by simp only [arm64_norm, hx24_al])
          (by simp only [arm64_norm]))
      rw [A.pool_transport lim _ _ _ (hvm3.toVmPreserved (by simp only [wp_norm, arm64_norm]))]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [subStack_split_extHook fsp hstk hstk64]
      have hpart := argsBufPartial_zero A.repAlloc i.argv.length (s_al.readReg64 .x0)
      rw [A.repAlloc_live_norm] at hpart
      rw [← hpart]
      simp only [Reg.x0, Reg.x1, List.map_cons]
      exact Entails.of_eq (by sep_ac_rfl)

/-! ## Phase 3: `strlen` loop (`M+0xa4 → M+0xc0`) by structural induction on `ps_todo` -/

private theorem step_strlen_loop_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st1 : M.σ}
    {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {buf p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hstrlen : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpecROSat hookStack)))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : ∀ a ∈ i.argv, PrintableAsciiArg a)
    (_hne : i.argv ≠ [])
    (hn : i.argv.length ≤ 1820)
    (hbuf : buf ≠ 0#64)
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hnext : ∀ s : State,
      InMainPlaced CodeOk s0 s 0xc0 →
      s.readReg64 (.gpr 19#5) = buf →
      s.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * i.argv.length) →
      s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 i.argv.length →
      s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length →
      s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 i.argv.length →
      s.trace = s0.trace →
      s.fs = s0.fs →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROPPad (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp oom) :
    ∀ (ps_todo ps_done : List (BitVec 64 × List (BitVec 8))) (s : State),
      ps_todo ≠ [] →
      ps_done ++ ps_todo = ps →
      InMainPlaced CodeOk s0 s 0xa4 →
      s.trace = s0.trace →
      s.fs = s0.fs →
      s.readReg64 (.gpr 19#5) = buf →
      s.readReg64 (.gpr 21#5) = s0.readReg64 .x1 + 8#64 →
      s.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * ps_done.length) →
      s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 i.argv.length →
      s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length →
      s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ps_done.length →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBufPartial A.repAlloc i.argv.length buf ps_done ∗
          ((s0.readReg64 .x1 ↦₆₄ᵣ p0) ∗ cStrAtROPad p0 (bytesOfString "libsignal-cli")) ∗
          argvAtROPPad (s0.readReg64 .x1 + 8#64) ps ∗
          mainSaved s0 ∗
          memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp oom := by
  have hps_len : ps.length = i.argv.length := by
    have := congrArg List.length hps
    simpa only [List.length_map] using this
  intro ps_todo
  induction ps_todo with
  | nil => intro _ _ hne_t; exact (hne_t rfl).elim
  | cons hd ps_rest ih =>
    rcases hd with ⟨pk, sk⟩
    intro ps_done s _ hsplit hs htr hfs hx19 hx21 hx22 hx23 hx24 hx25
    have hpc : s.pc = (blkPl_617).base + 164#64 := hs.pc
    set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    have hlt : ps_done.length < i.argv.length := by
      have : (ps_done ++ (pk, sk) :: ps_rest).length = i.argv.length := hsplit ▸ hps_len
      simp only [List.length_append, List.length_cons] at this
      omega
    have hk_le : ps_done.length ≤ 1820 := by omega
    have hshl3 := ofNat_shl_3 hk_le
    have hnul : ∀ b ∈ sk, b ≠ 0#8 :=
      argv_no_nul_at hok (hsplit.symm ▸ hps)
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = fsp := hs.sp
    have hfp : s.readReg64 .fp = s0.sp - 0x60#64 := hs.fp
    have hv : calleeSavedVRegs s = calleeSavedVRegs s0 := hs.vregs
    have hsp0 : s0.spAligned = true := hs.spAligned
    rw [← hsplit, argvAtROPPad_append (s0.readReg64 .x1 + 8#64) ps_done ((pk, sk) :: ps_rest),
      subStack_split_hook fsp hstk hstk64, mProgPlaced_eq]
    dsimp only [argvAtROPPad, Reg.x1]
    refine SepWPp.weaken_pre (Entails.of_eq
      (Q := cStrAtROPad pk sk ∗
        (argsBufPartial A.repAlloc i.argv.length buf ps_done ∗
          ((s0.readReg64 (.gpr 1#5) ↦₆₄ᵣ p0) ∗ cStrAtROPad p0 (bytesOfString "libsignal-cli")) ∗
          argvAtROPPadPrefix (s0.readReg64 (.gpr 1#5) + 8#64) ps_done ∗
          ((s0.readReg64 (.gpr 1#5) + 8#64 + BitVec.ofNat 64 (8 * ps_done.length)) ↦₆₄ᵣ pk) ∗
          argvAtROPPad
            (s0.readReg64 (.gpr 1#5) + 8#64 + BitVec.ofNat 64 (8 * ps_done.length) + 8#64)
            ps_rest ∗
          mainSaved s0 ∗ memRegion fsp 0x480 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              ((stk - mainFrameSize) - hookStack) ∗ stackAt fsp hookStack) ∗
          A.pool lim st1 s ∗ Statics))
      (by sep_ac_rfl)) ?_
    apply sepWPp_open_cStrAtROPad_p
    intro pad hpad_ok
    -- 1. Step `0xa4 .. 0xac` and call `strlen(pk)`
    refine sepWPp_seq_codeOk (mid := lsρ "strlen") hs.inv ?_
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, hpc, hx21, hx25, hshl3, *]; try bv_omega)
      (by simp only [arm64_norm, *])
    intro hinv_sl
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (Q :=
        (pk ↦ᵣ (sk ++ [0#8] ++ pad)) ∗
          (stackAt fsp hookStack ∗
            (((s0.readReg64 (.gpr 1#5) + 8#64 + BitVec.ofNat 64 (8 * ps_done.length)) ↦₆₄ᵣ pk) ∗
              argvAtROPPadPrefix (s0.readReg64 (.gpr 1#5) + 8#64) ps_done ∗
              argvAtROPPad
                (s0.readReg64 (.gpr 1#5) + 8#64 + BitVec.ofNat 64 (8 * ps_done.length) + 8#64)
                ps_rest ∗
              memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                ((stk - mainFrameSize) - hookStack) ∗
              argsBufPartial A.repAlloc i.argv.length buf ps_done ∗
              ((s0.readReg64 (.gpr 1#5) ↦₆₄ᵣ p0) ∗ cStrAtROPad p0 (bytesOfString "libsignal-cli")) ∗
              mainSaved s0 ∗ memRegion fsp 0x480 ∗ A.pool lim st1 s ∗ Statics)))
        (by sep_ac_rfl))
        (sepConj_mono_left (pointsToBytesRO_pad_entails_withStrlenPadRO pk sk pad hpad_ok))) ?_
    apply main_call_rocl (ret_pc := (blkPl_617).base + 176#64)
      (F := ((pk + BitVec.ofNat 64 (sk.length + 1)) ↦ᵣ pad) ∗
            ((s0.readReg64 (.gpr 1#5) + 8#64 + BitVec.ofNat 64 (8 * ps_done.length)) ↦₆₄ᵣ pk) ∗
            argvAtROPPadPrefix (s0.readReg64 (.gpr 1#5) + 8#64) ps_done ∗
            argvAtROPPad
              (s0.readReg64 (.gpr 1#5) + 8#64 + BitVec.ofNat 64 (8 * ps_done.length) + 8#64)
              ps_rest ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              ((stk - mainFrameSize) - hookStack) ∗
            argsBufPartial A.repAlloc i.argv.length buf ps_done ∗
            ((s0.readReg64 (.gpr 1#5) ↦₆₄ᵣ p0) ∗ cStrAtROPad p0 (bytesOfString "libsignal-cli")) ∗
            mainSaved s0 ∗ memRegion fsp 0x480 ∗ A.pool lim st1 s ∗ Statics)
      (pk, sk) hstrlen hinv_sl
      (by simp only [arm64_norm, hpc, hx21, hx25, hshl3, *]; try bv_omega)
      (by simp only [arm64_norm, *])
      (fsp_spAligned hsp0 (by simp only [arm64_norm, hsp]; rfl))
      (by simp only [arm64_norm, hpc, hx21, hx25, hshl3, *]; try bv_omega)
    · simp only [strlenSpecROSat, withVmPreserved, withStrlenPadRO, strlenSpecRO, arm64_norm, hsp,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply Entails.sepExists_elim; intro pad'
      apply Entails.pure_left; intro hswar'
      refine Entails.sepExists_right pad' (Entails.pure_right ⟨hswar', hnul⟩ ?_)
      exact Entails.of_eq (by sep_ac_rfl)
    intro s_sl hinv_sl2 hpc_sl hrun_sl hsp_sl hcs_sl
    rcases hcs_sl with ⟨hx19_sl, hx20_sl, hx21_sl, hx22_sl, hx23_sl, hx24_sl, hx25_sl, _, _, _, hfp_sl, hv_sl⟩
    simp only [arm64_norm, hx19, hx21, hx22, hx23, hx24, hx25, hfp, hsp]
      at hx19_sl hx20_sl hx21_sl hx22_sl hx23_sl hx24_sl hx25_sl hfp_sl hv_sl hsp_sl
    dsimp only [strlenSpecROSat, withVmPreserved, withStrlenPadRO, strlenSpecRO]
    simp only [arm64_norm, hsp, sepConj_assoc]
    apply SepWPp.pure_left
    rintro ⟨hvm_sl, hx0_sl, htr_sl_step, hfs_sl_step⟩
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (Q :=
        (cStrAtRO pk sk ∗ ((pk + BitVec.ofNat 64 (sk.length + 1)) ↦ᵣ pad)) ∗
          (stackAt fsp hookStack ∗
            (((s0.readReg64 (.gpr 1#5) + 8#64 + BitVec.ofNat 64 (8 * ps_done.length)) ↦₆₄ᵣ pk) ∗
              argvAtROPPadPrefix (s0.readReg64 (.gpr 1#5) + 8#64) ps_done ∗
              argvAtROPPad
                (s0.readReg64 (.gpr 1#5) + 8#64 + BitVec.ofNat 64 (8 * ps_done.length) + 8#64)
                ps_rest ∗
              memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                ((stk - mainFrameSize) - hookStack) ∗
              argsBufPartial A.repAlloc i.argv.length buf ps_done ∗
              ((s0.readReg64 (.gpr 1#5) ↦₆₄ᵣ p0) ∗ cStrAtROPad p0 (bytesOfString "libsignal-cli")) ∗
              mainSaved s0 ∗ memRegion fsp 0x480 ∗ A.pool lim st1 s ∗ Statics)))
        (by sep_ac_rfl))
        (sepConj_mono_left (cStrAtRO_pad_entails_cStrAtROPad pk sk pad hpad_ok))) ?_
    have hfs_sl : s_sl.fs = s0.fs := by simpa only [arm64_norm, hfs] using hfs_sl_step
    have htr_sl : s_sl.trace = s0.trace := by simpa only [arm64_norm, htr] using htr_sl_step
    have hpool_sl : A.pool lim st1 s = A.pool lim st1 s_sl := by
      have h := (A.pool_transport lim st1 _ _ hvm_sl).symm
      simpa only [RustCliAllocBudget.pool_setPC_norm, RustCliAllocBudget.pool_writeReg64_norm] using h
    rw [argsBufPartial_open_slot A.repAlloc buf ps_done hlt hn]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWPp_exists_left_p; intro w1
    apply sepWPp_exists_left_p; intro w0
    have hinc : BitVec.ofNat 64 ps_done.length + 1#64 = BitVec.ofNat 64 (ps_done.length + 1) := by
      rw [BitVec.ofNat_add]
    have hslot_next : buf + BitVec.ofNat 64 (16 * ps_done.length) + 16#64 =
        buf + BitVec.ofNat 64 (16 * (ps_done.length + 1)) := by
      have : 16 * (ps_done.length + 1) = 16 * ps_done.length + 16 := by omega
      rw [this, BitVec.ofNat_add]; bv_omega
    cases ps_rest with
    | nil =>
      have hend_len : ps_done.length + 1 = i.argv.length := by
        have : (ps_done ++ [(pk, sk)]).length = i.argv.length := hsplit ▸ hps_len
        simpa only [List.length_append, List.length_singleton] using this
      refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 192#64) hinv_sl2 fun _m_strip => ?_
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, hpc_sl, hx23_sl, hx25_sl, hinc, hend_len, *]; try bv_omega)
        (by simp only [arm64_norm, *])
      intro _m_real hvm_end hinv_end
      have h0 : 0 < i.argv.length := by omega
      have hbase_end : InMainPlaced CodeOk s0 _ 0xc0 :=
        { pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, hpc_sl, hx23_sl, hx25_sl, hinc, hend_len, *]; try bv_omega
          run := by simp only [arm64_norm, *]
          sp := by simp only [arm64_norm, hsp_sl]; rfl
          fp := by simp only [arm64_norm, hfp_sl]
          inv := hinv_end
          vregs := by simp only [calleeSavedVRegs, arm64_norm] at hv_sl ⊢; exact hv_sl.trans hv
          spAligned := hsp0 }
      refine SepWPp.weaken_pre ?_
        (hnext _ hbase_end
          (by simp only [arm64_norm, hx19_sl])
          (by simp only [arm64_norm, hx22_sl, hslot_next, hend_len])
          (by simp only [arm64_norm, hx23_sl])
          (by simp only [arm64_norm, hx24_sl])
          (by simp only [arm64_norm, hx25_sl, hinc, hend_len])
          (by simp only [arm64_norm, htr_sl])
          (by simp only [arm64_norm, hfs_sl]))
      rw [A.pool_transport lim st1 _ _ (hvm_end.toVmPreserved (by simp only [wp_norm, arm64_norm])), ← hpool_sl]
      have hclose := argsBufPartial_close_slot A.repAlloc i.argv.length buf ps_done pk sk
      have hclose_ps :
          A.repAlloc.live buf (16 * i.argv.length) 8 ∗
            arrayAt (fun pb a => sliceRefAt a pb.1 pb.2.length) 16 buf ps_done ∗
            sliceRefAt (buf + BitVec.ofNat 64 (16 * ps_done.length)) pk sk.length ∗
            memRegion (buf + BitVec.ofNat 64 (16 * (ps_done.length + 1)))
              (16 * (i.argv.length - (ps_done.length + 1))) =
            argsBufPartial A.repAlloc i.argv.length buf ps := by
        rw [← hsplit]; exact hclose
      have hfin := argsBufPartial_finish A.repAlloc h0 hn hbuf hps_len
      have hargv_re :
          argvAtROPPadPrefix (s0.readReg64 .x1 + 8#64) ps_done ∗
            (((s0.readReg64 .x1 + 8#64 + BitVec.ofNat 64 (8 * ps_done.length)) ↦₆₄ᵣ pk) ∗
              cStrAtROPad pk sk ∗
              argvAtROPPad (s0.readReg64 .x1 + 8#64 + BitVec.ofNat 64 (8 * ps_done.length) + 8#64) []) =
            argvAtROPPad (s0.readReg64 .x1 + 8#64) ps := by
        rw [← hsplit]
        simpa only [argvAtROPPad] using
          (argvAtROPPad_append (s0.readReg64 .x1 + 8#64) ps_done [(pk, sk)]).symm
      rw [locals_nil_eq, subStack_split_hook fsp hstk hstk64]
      refine Entails.trans ?_ (sepConj_mono_left hfin)
      conv => rhs; dsimp only [argvAtROPPad]
      rw [← hclose_ps, ← hargv_re]
      dsimp only [Reg.x1]
      unfold sliceRefAt
      exact Entails.of_eq (by sep_ac_rfl)
    | cons next rest =>
      have hlt_next : ps_done.length + 1 < i.argv.length := by
        have : (ps_done ++ (pk, sk) :: next :: rest).length = i.argv.length := hsplit ▸ hps_len
        simp only [List.length_append, List.length_cons] at this
        omega
      have hcmp_ne := loop_cmp_ne_true hlt_next hn
      refine sepWPp_seq_codeOk_vm (mid := (blkPl_617).base + 164#64) hinv_sl2 fun _m_strip => ?_
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, hpc_sl, hx23_sl, hx25_sl, hinc, hcmp_ne, *]; try bv_omega)
        (by simp only [arm64_norm, *])
      intro _m_real hvm_back hinv_back
      have hbase_back : InMainPlaced CodeOk s0 _ 0xa4 :=
        { pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, hpc_sl, hx23_sl, hx25_sl, hinc, hcmp_ne, *]; try bv_omega
          run := by simp only [arm64_norm, *]
          sp := by simp only [arm64_norm, hsp_sl]; rfl
          fp := by simp only [arm64_norm, hfp_sl]
          inv := hinv_back
          vregs := by simp only [calleeSavedVRegs, arm64_norm] at hv_sl ⊢; exact hv_sl.trans hv
          spAligned := hsp0 }
      have hsplit_next : (ps_done ++ [(pk, sk)]) ++ next :: rest = ps := by
        simpa only [List.append_assoc, List.singleton_append] using hsplit
      refine SepWPp.weaken_pre ?_
        (ih (ps_done ++ [(pk, sk)]) _ (List.cons_ne_nil _ _) hsplit_next hbase_back
          (by simp only [arm64_norm, htr_sl])
          (by simp only [arm64_norm, hfs_sl])
          (by simp only [arm64_norm, hx19_sl])
          (by simp only [arm64_norm, hx21_sl])
          (by simp only [arm64_norm, hx22_sl, hslot_next, List.length_append, List.length_singleton])
          (by simp only [arm64_norm, hx23_sl])
          (by simp only [arm64_norm, hx24_sl])
          (by simp only [arm64_norm, hx25_sl, hinc, List.length_append, List.length_singleton]))
      rw [A.pool_transport lim st1 _ _ (hvm_back.toVmPreserved (by simp only [wp_norm, arm64_norm])), ← hpool_sl]
      have hclose := argsBufPartial_close_slot A.repAlloc i.argv.length buf ps_done pk sk
      have hargv_re :
          argvAtROPPadPrefix (s0.readReg64 .x1 + 8#64) ps_done ∗
            (((s0.readReg64 .x1 + 8#64 + BitVec.ofNat 64 (8 * ps_done.length)) ↦₆₄ᵣ pk) ∗
              cStrAtROPad pk sk ∗
              argvAtROPPad (s0.readReg64 .x1 + 8#64 + BitVec.ofNat 64 (8 * ps_done.length) + 8#64)
                (next :: rest)) =
            argvAtROPPad (s0.readReg64 .x1 + 8#64) ps := by
        rw [← hsplit]
        simpa only [argvAtROPPad] using
          (argvAtROPPad_append (s0.readReg64 .x1 + 8#64) ps_done ((pk, sk) :: next :: rest)).symm
      rw [subStack_split_hook fsp hstk hstk64, ← hclose, ← hargv_re]
      dsimp only [Reg.x1]
      unfold sliceRefAt
      exact Entails.of_eq (by sep_ac_rfl)

/-! ## Top-level Honest `strlenSpecROSat` Read-Only `argv` Relocatable Hop M1 Proofs -/

/-- General OOM-callback read-only `argv` Hop M1 proof (`M+0x00 → M+0xc0` on Block `617`)
consuming `strlenSpecROSat hookStack` over `b2MainFrameFinePad` / `argvAtROPPad`, retaining
`A.pool` across the empty-`argv` fast exit (`ExitKPoolPlaced`). -/
theorem main_m1_ro_pool_placed_oom_proof_sat [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {i : Inputs} {s0 : State} {stk hookStack resStack : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc_alloc : AllocContractsFsPlaced A lim H)
    (hstrlen : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpecROSat hookStack)))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtEntryPlaced CodeOk i s0)
    (hok : CliInputsOk i)
    (hoom_cb : i.argv ≠ [] → ∀ s_pre sf R',
      s_pre.trace = s0.trace → s_pre.fs = s0.fs →
      sf.status = .OutOfMemory →
      ¬ FitsEvents M lim st (rustAllocEvents (16 * i.argv.length) 8) →
      OomPreserved s_pre sf →
      (sf.mem ⊨ anyHeap ∗ R') → (sf.mem ⊨ oom sf ∗ R'))
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp)
    (hnext : ∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64),
      i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROPPad (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st) s ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
      (b2MainFrameFinePad A lim st stk Statics i s0) Q Qp oom := by
  have hn : i.argv.length ≤ 1820 := argvFits_length_le hok.2
  have hstk_min : mainFrameSize ≤ stk := by omega
  refine step_prologue_placed hstk_min hstk64 hs0 hn ?_
  intro s1 hs1 htr1 hfs1 hw0 hx0 hx1 hx20 hx22 hx24
  by_cases hemp : i.argv = []
  · exact sepWPp_of_mainOom (step_empty_argv_placed hemp hs1 htr1 hfs1 hw0 hx20 hexit)
  · have h0 : 0 < i.argv.length := List.length_pos_of_ne_nil hemp
    refine step_alloc_buf_placed hc_alloc hstk hstk64 h0 hn hs1 htr1
      hfs1 hw0 hx0 hx1 hx20 hx22 hx24 (hoom_cb hemp) ?_
    intro s3 buf hbuf hs3 htr3 hfs3 hx19 hx21 hx22_3 hx23 hx24_3 hx25
    refine SepWPp.weaken_pre (Entails.of_eq (Q :=
      argvAtROPad (s0.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
      (argsBufPartial A.repAlloc i.argv.length buf [] ∗
        mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st) s3 ∗ Statics))
      (by sep_ac_rfl)) ?_
    apply sepWPp_open_argvAtROPad_p
    intro psAll hpsAll
    rcases psAll with _ | ⟨⟨p0, s0_str⟩, ps⟩
    · simp at hpsAll
    · simp only [List.map_cons, List.cons.injEq] at hpsAll
      rcases hpsAll with ⟨rfl, hps⟩
      dsimp only [argvAtROPPad]
      have hps_ne : ps ≠ [] := by
        intro hp0_nil
        rw [hp0_nil, List.map_nil] at hps
        exact hemp (List.map_eq_nil_iff.mp hps.symm)
      exact SepWPp.congr_pre (by sep_ac_rfl)
        (step_strlen_loop_placed hstrlen hstk hstk64 hok.1 hemp hn hbuf hps
          (fun s hb hx19' hx22' hx23' hx24' hx25' htr' hfs' =>
            hnext s buf ps p0 hemp hps
              { base := hb
                x19 := hx19'
                x22 := hx22'
                x23 := hx23'
                x24 := hx24'
                x25 := hx25'
                trace := htr'
                fs := hfs' })
          ps [] s3 hps_ne rfl hs3 htr3 hfs3 hx19 hx21 hx22_3 hx23 hx24_3 hx25)

/-- Total-correctness (`FitsEvents`) read-only `argv` Hop M1 proof (`M+0x00 → M+0xc0` on Block
`617`) consuming `strlenSpecROSat hookStack` over `b2MainFrameFinePad` / `argvAtROPPad`. -/
theorem main_m1_ro_pool_placed_proof_sat [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {i : Inputs} {s0 : State} {stk hookStack resStack : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc_alloc : AllocContractsFsPlaced A lim H)
    (hstrlen : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpecROSat hookStack)))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtEntryPlaced CodeOk i s0)
    (hok : CliInputsOk i)
    (hfits : i.argv ≠ [] → FitsEvents M lim st (rustAllocEvents (16 * i.argv.length) 8))
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp)
    (hnext : ∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64),
      i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROPPad (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st) s ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
      (b2MainFrameFinePad A lim st stk Statics i s0) Q Qp oom :=
  main_m1_ro_pool_placed_oom_proof_sat hc_alloc hstrlen hstk hstk64 hs0 hok
    (fun hemp _ _ _ _ _ _ hnf _ _ => (hnf (hfits hemp)).elim)
    hexit hnext

/-- Invariant-threaded `St0 → St1` Hop M1 adapter consuming `strlenSpecROSat hookStack` over
`b2MainFrameFinePad` / `argvAtROPPad`. -/
theorem main_m1_ro_pool_placed_step1_sat [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {St0 St1 : Inputs → M.σ → Prop}
    {stk hookStack resStack : Nat}
    (hc_alloc : AllocContractsFsPlaced A lim H)
    (hstrlen : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpecROSat hookStack)))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i st0 → i.argv ≠ [] →
      FitsEvents M lim st0 (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0))
    {i : Inputs} {s0 : State} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hst0 : St0 i st0)
    (hs0 : AtEntryPlaced CodeOk i s0)
    (hok : CliInputsOk i)
    (_hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp)
    (hnext : ∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64)
        (st1 : M.σ),
      St1 i st1 →
      i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROPPad (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
      (b2MainFrameFinePad A lim st0 stk Statics i s0) Q Qp oom :=
  main_m1_ro_pool_placed_proof_sat hc_alloc hstrlen hstk hstk64 hs0 hok
    (fun hemp => (hSt01 hok hst0 hemp).1)
    hexit
    (fun s buf ps p0 hemp hps hm1 =>
      hnext s buf ps p0 _ (hSt01 hok hst0 hemp).2 hemp hps hm1)

/-- `HookSat H "strlen" (strlenSpecROSat hookStack)` specialization of
`main_m1_ro_pool_placed_step1_sat`. -/
theorem main_m1_ro_pool_placed_step1_of_sat [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {St0 St1 : Inputs → M.σ → Prop}
    {stk hookStack resStack : Nat}
    (hc_alloc : AllocContractsFsPlaced A lim H)
    (hsat : HookSat H "strlen" (strlenSpecROSat hookStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i st0 → i.argv ≠ [] →
      FitsEvents M lim st0 (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0))
    {i : Inputs} {s0 : State} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hst0 : St0 i st0)
    (hs0 : AtEntryPlaced CodeOk i s0)
    (hok : CliInputsOk i)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp)
    (hnext : ∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64)
        (st1 : M.σ),
      St1 i st1 →
      i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROPPad (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
      (b2MainFrameFinePad A lim st0 stk Statics i s0) Q Qp oom :=
  main_m1_ro_pool_placed_step1_sat hc_alloc (strlen_ro_sat_placed_ok_of_sat hsat)
    hstk hstk64 hSt01 hst0 hs0 hok hpanic hexit hnext

/-- Pool-erasing `ExitKPlaced` corollary of `main_m1_ro_pool_placed_proof_sat`. -/
theorem main_m1_ro_placed_proof_sat [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {i : Inputs} {s0 : State} {stk hookStack resStack : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc_alloc : AllocContractsFsPlaced A lim H)
    (hstrlen : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpecROSat hookStack)))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtEntryPlaced CodeOk i s0)
    (hok : CliInputsOk i)
    (hfits : i.argv ≠ [] → FitsEvents M lim st (rustAllocEvents (16 * i.argv.length) 8))
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp)
    (hnext : ∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64),
      i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROPPad (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st) s ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
      (b2MainFrameFinePad A lim st stk Statics i s0) Q Qp oom :=
  main_m1_ro_pool_placed_proof_sat hc_alloc hstrlen hstk hstk64 hs0 hok hfits
    (exitKPoolPlaced_of_exitKPlaced hexit) hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1PlacedRoBudgetSat
