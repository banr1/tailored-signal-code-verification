/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Relocatable `signal_session::public::split_id` (Block `593`)

Verifies `splitIdSpecPlaced` on Block `593` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement LibsignalRoLoaded lsmpl lsρ
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt speWord)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost dropSpeStackX)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (SplitGhost splitId splitIdResultAt utf8)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_593 blkPl_593 lsProg_593)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (
  SepWP.call_lscro ls_transfer_lscro satisfies_lscro_pre stk_le_pow64_of_roLoaded
)
open CryptoVerification.SignalSession.Cli.SplitId.Helpers (
  SidUpperSaved buf14_close buf14_open_lo buf14_realign bytesAt_cons4_false bytesAt_cons4_true
  malfHead6 malfHi malfLo ret48_open_err ret48_open_ok sidBundleSym sidMalfRO_bundle_intro_p
  sidMalfRO_p sidMalfSym sidSavedRegs sp_sub_96_spAligned speAt_invalidState_intro_p speWord1_eq
  stackAt_hook_split stackAt_sid_pack_cells stackAt_sid_pack_region stackAt_sid_split
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved rustAllocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsXCliPlaced splitIdSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (
  allocNoOom_lscro_of_cli shim_lscro_of_cli
)

/-- Allocator event envelope of `split_id`: allocates a 14-byte `"malformed file"` buffer, and additionally drops it (`FreeOnlyEvs`) when `4 ≤ file.length`. -/
def SplitIdEnv (file : List (BitVec 8)) : List AllocEvent → Prop :=
  if file.length < 4 then (· = rustAllocEvents 14 1)
  else SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs

theorem splitIdEnv_alloc14 (file : List (BitVec 8)) :
    SplitIdEnv file (rustAllocEvents 14 1) := by
  unfold SplitIdEnv
  split
  · rfl
  · have h : SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs (rustAllocEvents 14 1 ++ []) :=
      SeqEnv.append rfl FreeOnlyEvs.nil
    rwa [List.append_nil] at h

theorem fitsEvents_14_of_splitIdEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {file : List (BitVec 8)} (hfit : FitsEnv M lim st (SplitIdEnv file)) :
    FitsEvents M lim st (rustAllocEvents 14 1) :=
  hfit _ (splitIdEnv_alloc14 file)

namespace Helpers

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

noncomputable abbrev sidProg [LibsignalPlacement] (H : LibsignalHooks) : Program :=
  (blkPC_593).rebase (blkPl_593).base H

private theorem bind_sepWP_state_p {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

private theorem sepWP_pull_pure_p {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {φ : Prop} {Q : State → SepProp → Prop}
    (hf : P = ⌜φ⌝ ∗ F := by sep_focus)
    (h : φ → SepWP prog ret s F Q) :
    SepWP prog ret s P Q := by
  rw [hf]
  exact SepWP.pure_elim h

private theorem sepWP_realign_buf14_p {prog : Program} {ret : BitVec 64} {s : State}
    {P F1 F2 : SepProp} {buf : BitVec 64} {Q : State → SepProp → Prop}
    (hf1 : P = (buf ↦₆₄ malfLo) ∗ F1 := by sep_focus)
    (hf2 : F1 = memRegion (buf + 8#64) 6 ∗ F2 := by sep_focus)
    (h : SepWP prog ret s
      ((buf ↦ₛ malfHead6) ∗ (∃∗ w1 : BitVec 64, (buf + 6#64) ↦₆₄ w1) ∗ F2) Q) :
    SepWP prog ret s P Q := by
  rw [hf1, hf2, ← sepConj_assoc]
  exact SepWP.weaken_pre
    (Entails.trans (sepConj_mono_left (buf14_realign buf)) (Entails.of_eq (sepConj_assoc _ _ _))) h

@[local simp, local arm64_norm]
private theorem sid_sub_add_p (a k m : BitVec 64) : a - k + m = a - (k - m) := by
  bv_omega

@[local simp, local arm64_norm]
private theorem add4_sub4_64_p (a : BitVec 64) :
    (a + 4#64) - 4#64 = a := by
  bv_omega

@[local simp, local arm64_norm]
private theorem zext32_trunc32_p (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

@[local simp, local arm64_norm]
private theorem sp_restore_96_p (sp0 : BitVec 64) :
    sp0 - 96#64 + 96#64 = sp0 := by
  bv_bits

@[local simp, local arm64_norm]
private theorem append64_extract_lo_p (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[local simp, local arm64_norm]
private theorem append64_extract_hi_p (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

private theorem sid_call_lscro_budget [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {α : Type} {callee_pc : BitVec 64} (ret_pc : BitVec 64) {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R') := by
      intro _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R') := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default)
    (hnext : ∀ sf : State,
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWP prog ret sf (spec.post x s sf ∗ F) Q) :
    SepWP prog ret s P Q :=
  SepWP.call_lscro (x := x) hcall hcrl hpc hrun hsp hlr
    (fun R hm => by rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hP) hm)
    h_no_panic h_no_exit
    (fun sf hpcm hrunm hspm hcsm hcrlm => hnext sf hcrlm hpcm hrunm hspm hcsm)
    h_no_oom

set_option linter.unusedSimpArgs false in
theorem step_ok_path_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat} {st : M.σ} {post : State → SepProp → Prop}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDrop : subroutine_ok (sidProg H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)))
    (hstk : 96 + dropSpeStackX ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (hfit14 : FitsEvents M lim st (rustAllocEvents 14 1))
    (retAddr fp : BitVec 64) (ro : Bool)
    (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8))
    (v24 : BitVec 64)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_593).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hx1 : s.readReg64 .x1 = fp)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 rest.length + 4#64)
    (hcs : SidUpperSaved s0 s)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.pc = s0.readReg64 Reg.lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ sidMalfRO_p ∗
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SplitIdEnv (b0 :: b1 :: b2 :: b3 :: rest) evs⌝ ∗
            splitIdResultAt A.repAlloc retAddr fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
            bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
            stackAt s0.sp stk ∗
            A.pool lim (M.stepEvents evs st) sf) →
      post sf P_f) :
    SepWP (sidProg H) (s0.readReg64 Reg.lr) s
      (sidMalfRO_p ∗
        ((lsρ sidBundleSym) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        sidSavedRegs s0.sp s0 v24 ∗
        stackAt (s0.sp - 96#64) dropSpeStackX ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
        memRegion retAddr 48 ∗
        A.pool lim st s)
      post := by
  have hshim := shim_lscro_of_cli (callerProg := sidProg H) hC (stk := extHookStack)
  have halloc := allocNoOom_lscro_of_cli (callerProg := sidProg H) hC
  clear hC
  have hal_s : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal_s
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
  intro hcrl1
  apply bind_sepWP_state_p; intro s_sh
  have hal_sh : s_sh.spAligned = true :=
    sp_sub_96_spAligned hal0 (by simp only [s_sh, wp_norm, arm64_norm, hsp])
  have hcs_sh : SidUpperSaved s0 s_sh := by
    rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
    simp only [s_sh, SidUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *]
  refine sid_call_lscro_budget ((blkPl_593).base + 44#64) () hshim hcrl1
    (by simp only [s_sh, wp_norm, arm64_norm, *])
    (by simp only [s_sh, wp_norm, arm64_norm, *])
    hal_sh
    (by simp only [s_sh, wp_norm, arm64_norm, *])
    (F := sidMalfRO_p ∗
      ((lsρ sidBundleSym) ↦ᵣ utf8 "bundle") ∗
      cells (s0.sp - 96#64) 6 ∗
      sidSavedRegs s0.sp s0 v24 ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
      bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
      memRegion retAddr 48 ∗ A.pool lim st s_sh)
    ?_ (hnext := ?_)
  · rw [stackAt_hook_split (s0.sp - 96#64)]
    dsimp only [withStack, sessionShimBudgetSpec]
    have hsp_eq : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, wp_norm, arm64_norm, hsp]
    rw [hsp_eq]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s_after_sh hcrl2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [withStack, sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    refine sepWP_pull_pure_p (φ := VmPreserved s_sh s_after_sh) (h := fun hvm_sh => ?_)
    refine sepWP_pull_pure_p (φ := s_after_sh.trace = s_sh.trace) (h := fun htr2 => ?_)
    refine ProofLib.SepWP.transport_budgetPool hvm_sh (hnext := ?_)
    have hx19_2 : s_after_sh.readReg64 .x19 = retAddr := by
      rw [hcsp2.1]; simp only [s_sh, wp_norm, arm64_norm, hx19]
    let _ := And.intro hx1 hx2
    have hx20_2 : s_after_sh.readReg64 .x20 = fp := by
      rw [hcsp2.2.1]; simp only [s_sh, wp_norm, arm64_norm, *]
    have hx21_2 : s_after_sh.readReg64 .x21 = BitVec.ofNat 64 rest.length + 4#64 := by
      rw [hcsp2.2.2.1]; simp only [s_sh, wp_norm, arm64_norm, *]
    have hsp2' : s_after_sh.sp = s0.sp - 96#64 := by
      rw [hsp2]; simp only [s_sh, wp_norm, arm64_norm, hsp]
    clear hsp2
    have hal2 : s_after_sh.spAligned = true := sp_sub_96_spAligned hal0 hsp2'
    let _ := hal2
    have htr2' : s_after_sh.trace = s0.trace := by
      rw [htr2]; simp only [s_sh, wp_norm, arm64_norm, htr]
    have hcs2 : SidUpperSaved s0 s_after_sh := hcs_sh.trans_calleeSaved hcsp2
    apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl2
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
    intro hcrl3
    apply bind_sepWP_state_p; intro s_al
    have hal_al : s_al.spAligned = true :=
      sp_sub_96_spAligned hal0 (by simp only [s_al, wp_norm, arm64_norm, hsp2'])
    have hcs_al : SidUpperSaved s0 s_al := by
      rcases hcs2 with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
      simp only [s_al, SidUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *]
    have hlay : RustLayoutOk 14 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
    refine sid_call_lscro_budget ((blkPl_593).base + 56#64) (14, 1, st) halloc hcrl3
      (by simp only [s_al, wp_norm, arm64_norm, *])
      (by simp only [s_al, wp_norm, arm64_norm, *])
      hal_al
      (by simp only [s_al, wp_norm, arm64_norm, *])
      (F := sidMalfRO_p ∗
        ((lsρ sidBundleSym) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        sidSavedRegs s0.sp s0 v24 ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
        memRegion retAddr 48)
      ?_ (hnext := ?_)
    · dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack]
      have hpure_al :
          ((s_al.readReg64 .x0).toNat = 14 ∧ (s_al.readReg64 .x1).toNat = 1 ∧
            RustLayoutOk 14 1 ∧ FitsEvents M lim st (rustAllocEvents 14 1) ∧
            LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_al.readReg64 .lr)) = True :=
        eq_true ⟨by simp only [s_al, wp_norm, arm64_norm],
          by simp only [s_al, wp_norm, arm64_norm], hlay, hfit14,
          ⟨593, by decide, 56, by decide, by simp only [s_al, wp_norm, arm64_norm, *]; rfl⟩⟩
      have hsp_eq1 : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, wp_norm, arm64_norm, hsp]
      have hsp_eq2 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, wp_norm, arm64_norm, hsp2']
      rw [hpure_al, pure_true, emp_sepConj, hsp_eq1, hsp_eq2]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after_al hcrl4 hpc4 hrun4 hsp4 hcsp4
      dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine sepWP_pull_pure_p (h := fun hp => ?_)
      rcases hp with ⟨hacp_al, hnull, _⟩
      have hx19_4 : s_after_al.readReg64 .x19 = retAddr := by
        rw [hcsp4.1]; simp only [s_al, wp_norm, arm64_norm, hx19_2]
      have hx20_4 : s_after_al.readReg64 .x20 = fp := by
        rw [hcsp4.2.1]; simp only [s_al, wp_norm, arm64_norm, hx20_2]
      have hx21_4 : s_after_al.readReg64 .x21 = BitVec.ofNat 64 rest.length + 4#64 := by
        rw [hcsp4.2.2.1]; simp only [s_al, wp_norm, arm64_norm, hx21_2]
      have hsp4' : s_after_al.sp = s0.sp - 96#64 := by
        rw [hsp4]; simp only [s_al, wp_norm, arm64_norm, hsp2']
      clear hsp4
      have hal4 : s_after_al.spAligned = true := sp_sub_96_spAligned hal0 hsp4'
      let _ := hal4
      have htr4' : s_after_al.trace = s0.trace := by
        rw [hacp_al.2.1]; simp only [s_al, wp_norm, arm64_norm, htr2']
      have hcs4 : SidUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved hcsp4
      set buf := s_after_al.readReg64 .x0 with hbuf_def
      let _ := hbuf_def
      have hptr_ne : buf ≠ 0#64 := hnull
      have hptr_beq : (buf == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
      have hptr_bne : (buf != 0#64) = true := bne_iff_ne.mpr hptr_ne
      have _ := And.intro hptr_beq hptr_bne
      rw [buf14_open_lo buf]
      unfold sidMalfRO_p
      cells_unfold
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun w0 =>
        SepWP.exists_elim fun c0 => SepWP.exists_elim fun c1 =>
        SepWP.exists_elim fun c2 => SepWP.exists_elim fun c3 =>
        SepWP.exists_elim fun c4 => SepWP.exists_elim fun c5 => ?_
      apply sepWP_seq_lscro (mid := (blkPl_593).base + 84#64) hcrl4
      wp_steps_sync_pool ((blkPl_593).base + 84#64)
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      intro hcrl5
      apply sepWP_realign_buf14_p (buf := buf)
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun w1 => ?_
      apply sepWP_seq_lscro (mid := lsmpl.base 553) hcrl5
      wp_steps_sync_pool (lsmpl.base 553)
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      intro hcrl6
      apply bind_sepWP_state_p; intro s_dr
      have _ := hx21_4
      have hal_dr : s_dr.spAligned = true :=
        sp_sub_96_spAligned hal0 (by simp only [s_dr, wp_norm, arm64_norm, hsp4'])
      have hcs_dr : SidUpperSaved s0 s_dr := by
        rcases hcs4 with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
        simp only [s_dr, SidUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *]
      let st_al := M.stepEvents (rustAllocEvents 14 1) st
      refine sid_call_lscro_budget ((blkPl_593).base + 132#64)
        (⟨s0.sp - 96#64, utf8 "bundle", .invalidState⟩, st_al) hDrop hcrl6
        (by simp only [s_dr, wp_norm, arm64_norm, *])
        (by simp only [s_dr, wp_norm, arm64_norm, *])
        hal_dr
        (by simp only [s_dr, wp_norm, arm64_norm, *])
        (F := sidMalfRO_p ∗
          sidSavedRegs s0.sp s0 v24 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
          bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
          memRegion retAddr 48)
        ?_ (hnext := ?_)
      · dsimp only [dropSpeSpecX]
        have hx0_dr :
            (s_dr.readReg64 .x0 = s0.sp - 96#64 ∧
              LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_dr.readReg64 .x30)) = True :=
          eq_true ⟨by simp only [s_dr, wp_norm, arm64_norm, *],
            ⟨593, by decide, 132, by decide, by simp only [s_dr, wp_norm, arm64_norm, *]; rfl⟩⟩
        have hsp_dr : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, wp_norm, arm64_norm, hsp4']
        have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, wp_norm, arm64_norm, hsp2']
        rw [hx0_dr, pure_true, emp_sepConj, hsp_dr, stackAt_hook_split (s0.sp - 96#64), hsp_al0]
        unfold sidMalfRO_p
        rw [speWord1_eq]
        have hbuf_pack : ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) =
            (buf ↦ₛ utf8 "malformed file") := buf14_close buf
        have hspe_pack :
            (((s0.sp - 96#64) ↦₆₄ speWord 1) ∗
              (((s0.sp - 96#64) + 8#64) ↦₆₄ 14#64) ∗
              (((s0.sp - 96#64) + 16#64) ↦₆₄ buf) ∗
              (((s0.sp - 96#64) + 24#64) ↦₆₄ 14#64) ∗
              A.repAlloc.live buf 14 1 ∗
              ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) ∗
              (((s0.sp - 96#64) + 32#64) ↦₆₄ (lsρ sidBundleSym)) ∗
              (((s0.sp - 96#64) + 40#64) ↦₆₄ 6#64) ∗
              ((lsρ sidBundleSym) ↦ᵣ utf8 "bundle")) ⊢
            speAt A.repAlloc (utf8 "bundle") (s0.sp - 96#64) .invalidState := by
          rw [hbuf_pack]
          exact speAt_invalidState_intro_p A.repAlloc (lsρ sidBundleSym) (s0.sp - 96#64) buf hptr_ne
        dsimp only [RustCliAllocBudget.repAlloc_live_norm] at hspe_pack
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q :=
            A.pool lim st_al s_dr ∗
              memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
              stackAt (s0.sp - 96#64) extHookStack ∗
              sidMalfRO_p ∗
              sidSavedRegs s0.sp s0 v24 ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
              bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
              memRegion retAddr 48) hspe_pack) ?_)
        · unfold sidMalfRO_p lsρ
          dsimp only [blkPl_593, sidBundleSym, sidMalfSym, st_al]
          simp only [sid_sub_add_p, BitVec.reduceSub, sepConj_assoc]
          exact Entails.of_eq (by sep_ac_rfl)
        · unfold sidMalfRO_p lsρ
          dsimp only [blkPl_593, sidBundleSym, sidMalfSym, st_al]
          simp only [sepConj_assoc]
          exact Entails.of_eq (by sep_ac_rfl)
      ·
        intro s_ep hcrl7 hpc7 hrun7 hsp7 hcsp7
        let _ := hcrl7
        dsimp only [dropSpeSpecX]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWP.exists_elim fun evs_dr => ?_
        refine sepWP_pull_pure_p (φ := s_ep.trace = s_dr.trace) (h := fun htr7 => ?_)
        refine sepWP_pull_pure_p (φ := FreeOnlyEvs evs_dr) (h := fun hfree_dr => ?_)
        have hx19_7 : s_ep.readReg64 .x19 = retAddr := by
          rw [hcsp7.1]; simp only [s_dr, wp_norm, arm64_norm, hx19_4]
        have hx20_7 : s_ep.readReg64 .x20 = fp := by
          rw [hcsp7.2.1]; simp only [s_dr, wp_norm, arm64_norm, hx20_4]
        have hx21_7 : s_ep.readReg64 .x21 = BitVec.ofNat 64 rest.length := by
          rw [hcsp7.2.2.1]; simp only [s_dr, wp_norm, arm64_norm, *]
        have hsp7' : s_ep.sp = s0.sp - 96#64 := by
          rw [hsp7]; simp only [s_dr, wp_norm, arm64_norm, hsp4']
        clear hsp7
        have hal7 : s_ep.spAligned = true := sp_sub_96_spAligned hal0 hsp7'
        let _ := hal7
        have htr7' : s_ep.trace = s0.trace := by
          rw [htr7]; simp only [s_dr, wp_norm, arm64_norm, htr4']
        have hcs7 : SidUpperSaved s0 s_ep := hcs_dr.trans_calleeSaved hcsp7
        rcases hcs7 with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
        have hsdr_sp : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, wp_norm, arm64_norm, hsp4']
        rw [hsdr_sp, ret48_open_ok retAddr]
        unfold sidSavedRegs
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWP.exists_elim fun r0 => SepWP.exists_elim fun r8 =>
          SepWP.exists_elim fun r16 => SepWP.exists_elim fun r24 => ?_
        have hevs_ok : SplitIdEnv (b0 :: b1 :: b2 :: b3 :: rest) (rustAllocEvents 14 1 ++ evs_dr) := by
          unfold SplitIdEnv
          have hlt_f : ¬ (b0 :: b1 :: b2 :: b3 :: rest).length < 4 := by
            simp only [List.length_cons]; omega
          simp only [hlt_f, ↓reduceIte]
          exact SeqEnv.append rfl hfree_dr
        dsimp only [st_al]
        rw [← M.stepEvents_append]
        cases ro with
        | false =>
          rw [bytesAt_cons4_false fp b0 b1 b2 b3 rest]
          simp only [sepConj_assoc]
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          apply bind_sepWP_state_p; intro sf
          apply SepWP.done (by simp only [sf, wp_norm, arm64_norm, *]) (by wp_norm_lhs)
          refine hk sf _
            (by simp only [sf, wp_norm, arm64_norm, *])
            (by simp only [sf, wp_norm, arm64_norm, *])
            (by simp only [sf, wp_norm, arm64_norm, *])
            ?_ ?_
          · refine ⟨by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, calleeSavedVRegs, wp_norm, arm64_norm] at hvregs ⊢; exact hvregs⟩
          · have htrf : sf.trace = s0.trace := by simp only [sf, wp_norm, arm64_norm, htr7']
            rw [← sepExists_sepConj_right]
            refine Entails.trans ?_
              (sepConj_mono_right
                (Entails.sepExists_right (rustAllocEvents 14 1 ++ evs_dr)
                  (Entails.pure_right ⟨htrf, hevs_ok⟩ (Entails.refl _))))
            refine Entails.trans (Q :=
              (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
                stackAt (s0.sp - 96#64) dropSpeStackX ∗
                memRegion (s0.sp - 96#64) 48 ∗
                sidSavedRegs s0.sp s0 v24) ∗
              (sidMalfRO_p ∗
                splitIdResultAt A.repAlloc retAddr fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
                bytesAt false fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
                A.pool lim (M.stepEvents (rustAllocEvents 14 1 ++ evs_dr) st) sf)) ?_
              (Entails.trans
                (sepConj_mono_left (stackAt_sid_pack_region s0.sp stk s0 v24 hstk hstkle)) ?_)
            · dsimp only [splitIdResultAt, splitId]
              rw [bytesAt_cons4_false fp b0 b1 b2 b3 rest]
              unfold sidSavedRegs
              simp only [sepConj_assoc]
              exact Entails.of_eq (by sep_ac_rfl)
            · unfold sidMalfRO_p
              rw [bytesAt_cons4_false fp b0 b1 b2 b3 rest]
              simp only [sepConj_assoc]
              exact Entails.of_eq (by sep_ac_rfl)
        | true =>
          rw [bytesAt_cons4_true fp b0 b1 b2 b3 rest]
          simp only [sepConj_assoc]
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          apply bind_sepWP_state_p; intro sf
          apply SepWP.done (by simp only [sf, wp_norm, arm64_norm, *]) (by wp_norm_lhs)
          refine hk sf _
            (by simp only [sf, wp_norm, arm64_norm, *])
            (by simp only [sf, wp_norm, arm64_norm, *])
            (by simp only [sf, wp_norm, arm64_norm, *])
            ?_ ?_
          · refine ⟨by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, wp_norm, arm64_norm, *],
              by simp only [sf, calleeSavedVRegs, wp_norm, arm64_norm] at hvregs ⊢; exact hvregs⟩
          · have htrf : sf.trace = s0.trace := by simp only [sf, wp_norm, arm64_norm, htr7']
            rw [← sepExists_sepConj_right]
            refine Entails.trans ?_
              (sepConj_mono_right
                (Entails.sepExists_right (rustAllocEvents 14 1 ++ evs_dr)
                  (Entails.pure_right ⟨htrf, hevs_ok⟩ (Entails.refl _))))
            refine Entails.trans (Q :=
              (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
                stackAt (s0.sp - 96#64) dropSpeStackX ∗
                memRegion (s0.sp - 96#64) 48 ∗
                sidSavedRegs s0.sp s0 v24) ∗
              (sidMalfRO_p ∗
                splitIdResultAt A.repAlloc retAddr fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
                bytesAt true fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
                A.pool lim (M.stepEvents (rustAllocEvents 14 1 ++ evs_dr) st) sf)) ?_
              (Entails.trans
                (sepConj_mono_left (stackAt_sid_pack_region s0.sp stk s0 v24 hstk hstkle)) ?_)
            · dsimp only [splitIdResultAt, splitId]
              rw [bytesAt_cons4_true fp b0 b1 b2 b3 rest]
              unfold sidSavedRegs
              simp only [sepConj_assoc]
              exact Entails.of_eq (by sep_ac_rfl)
            · unfold sidMalfRO_p lsρ
              dsimp only [blkPl_593, sidBundleSym, sidMalfSym]
              rw [bytesAt_cons4_true fp b0 b1 b2 b3 rest]
              simp only [sepConj_assoc]
              exact Entails.of_eq (by sep_ac_rfl)

set_option linter.unusedSimpArgs false in
theorem step_err_path_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat} {st : M.σ} {post : State → SepProp → Prop}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 96 + dropSpeStackX ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (hfit14 : FitsEvents M lim st (rustAllocEvents 14 1))
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8))
    (hnone : splitId file = none)
    (v24 : BitVec 64)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_593).base + 172#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hcs : SidUpperSaved s0 s)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.pc = s0.readReg64 Reg.lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ sidMalfRO_p ∗
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SplitIdEnv file evs⌝ ∗
            splitIdResultAt A.repAlloc retAddr fp file ∗
            bytesAt ro fp file ∗
            stackAt s0.sp stk ∗
            A.pool lim (M.stepEvents evs st) sf) →
      post sf P_f) :
    SepWP (sidProg H) (s0.readReg64 Reg.lr) s
      (sidMalfRO_p ∗
        ((lsρ sidBundleSym) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        sidSavedRegs s0.sp s0 v24 ∗
        stackAt (s0.sp - 96#64) dropSpeStackX ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        bytesAt ro fp file ∗
        memRegion retAddr 48 ∗
        A.pool lim st s)
      post := by
  have hshim := shim_lscro_of_cli (callerProg := sidProg H) hC (stk := extHookStack)
  have halloc := allocNoOom_lscro_of_cli (callerProg := sidProg H) hC
  clear hC
  have hal_s : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal_s
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
  intro hcrl1
  apply bind_sepWP_state_p; intro s_sh
  have hal_sh : s_sh.spAligned = true :=
    sp_sub_96_spAligned hal0 (by simp only [s_sh, wp_norm, arm64_norm, hsp])
  have hcs_sh : SidUpperSaved s0 s_sh := by
    rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
    simp only [s_sh, SidUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *]
  refine sid_call_lscro_budget ((blkPl_593).base + 176#64) () hshim hcrl1
    (by simp only [s_sh, wp_norm, arm64_norm, *])
    (by simp only [s_sh, wp_norm, arm64_norm, *])
    hal_sh
    (by simp only [s_sh, wp_norm, arm64_norm, *])
    (F := sidMalfRO_p ∗
      ((lsρ sidBundleSym) ↦ᵣ utf8 "bundle") ∗
      cells (s0.sp - 96#64) 6 ∗
      sidSavedRegs s0.sp s0 v24 ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
      bytesAt ro fp file ∗
      memRegion retAddr 48 ∗ A.pool lim st s_sh)
    ?_ (hnext := ?_)
  · rw [stackAt_hook_split (s0.sp - 96#64)]
    dsimp only [withStack, sessionShimBudgetSpec]
    have hsp_eq : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, wp_norm, arm64_norm, hsp]
    rw [hsp_eq]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s_after_sh hcrl2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [withStack, sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    refine sepWP_pull_pure_p (φ := VmPreserved s_sh s_after_sh) (h := fun hvm_sh => ?_)
    refine sepWP_pull_pure_p (φ := s_after_sh.trace = s_sh.trace) (h := fun htr2 => ?_)
    refine ProofLib.SepWP.transport_budgetPool hvm_sh (hnext := ?_)
    have hx19_2 : s_after_sh.readReg64 .x19 = retAddr := by
      rw [hcsp2.1]; simp only [s_sh, wp_norm, arm64_norm, hx19]
    have hsp2' : s_after_sh.sp = s0.sp - 96#64 := by
      rw [hsp2]; simp only [s_sh, wp_norm, arm64_norm, hsp]
    clear hsp2
    have hal2 : s_after_sh.spAligned = true := sp_sub_96_spAligned hal0 hsp2'
    let _ := hal2
    have htr2' : s_after_sh.trace = s0.trace := by
      rw [htr2]; simp only [s_sh, wp_norm, arm64_norm, htr]
    have hcs2 : SidUpperSaved s0 s_after_sh := hcs_sh.trans_calleeSaved hcsp2
    apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl2
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
    intro hcrl3
    apply bind_sepWP_state_p; intro s_al
    have hal_al : s_al.spAligned = true :=
      sp_sub_96_spAligned hal0 (by simp only [s_al, wp_norm, arm64_norm, hsp2'])
    have hcs_al : SidUpperSaved s0 s_al := by
      rcases hcs2 with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
      simp only [s_al, SidUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *]
    have hlay : RustLayoutOk 14 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
    refine sid_call_lscro_budget ((blkPl_593).base + 188#64) (14, 1, st) halloc hcrl3
      (by simp only [s_al, wp_norm, arm64_norm, *])
      (by simp only [s_al, wp_norm, arm64_norm, *])
      hal_al
      (by simp only [s_al, wp_norm, arm64_norm, *])
      (F := sidMalfRO_p ∗
        ((lsρ sidBundleSym) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        sidSavedRegs s0.sp s0 v24 ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        bytesAt ro fp file ∗
        memRegion retAddr 48)
      ?_ (hnext := ?_)
    · dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack]
      have hpure_al :
          ((s_al.readReg64 .x0).toNat = 14 ∧ (s_al.readReg64 .x1).toNat = 1 ∧
            RustLayoutOk 14 1 ∧ FitsEvents M lim st (rustAllocEvents 14 1) ∧
            LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_al.readReg64 .lr)) = True :=
        eq_true ⟨by simp only [s_al, wp_norm, arm64_norm],
          by simp only [s_al, wp_norm, arm64_norm], hlay, hfit14,
          ⟨593, by decide, 188, by decide, by simp only [s_al, wp_norm, arm64_norm, *]; rfl⟩⟩
      have hsp_eq1 : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, wp_norm, arm64_norm, hsp]
      have hsp_eq2 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, wp_norm, arm64_norm, hsp2']
      rw [hpure_al, pure_true, emp_sepConj, hsp_eq1, hsp_eq2]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after_al hcrl4 hpc4 hrun4 hsp4 hcsp4
      let _ := hcrl4
      dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine sepWP_pull_pure_p (h := fun hp => ?_)
      rcases hp with ⟨hacp_al, hnull, _⟩
      have hx19_4 : s_after_al.readReg64 .x19 = retAddr := by
        rw [hcsp4.1]; simp only [s_al, wp_norm, arm64_norm, hx19_2]
      have hsp4' : s_after_al.sp = s0.sp - 96#64 := by
        rw [hsp4]; simp only [s_al, wp_norm, arm64_norm, hsp2']
      clear hsp4
      have hal4 : s_after_al.spAligned = true := sp_sub_96_spAligned hal0 hsp4'
      let _ := hal4
      have htr4' : s_after_al.trace = s0.trace := by
        rw [hacp_al.2.1]; simp only [s_al, wp_norm, arm64_norm, htr2']
      have hcs4 : SidUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved hcsp4
      set buf := s_after_al.readReg64 .x0 with hbuf_def
      let _ := hbuf_def
      have hptr_ne : buf ≠ 0#64 := hnull
      have hptr_beq : (buf == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
      have hptr_bne : (buf != 0#64) = true := bne_iff_ne.mpr hptr_ne
      have _ := And.intro hptr_beq hptr_bne
      rw [buf14_open_lo buf, ret48_open_err retAddr]
      unfold sidMalfRO_p sidSavedRegs
      cells_unfold
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun w0 =>
        SepWP.exists_elim fun c0 => SepWP.exists_elim fun c1 =>
        SepWP.exists_elim fun c2 => SepWP.exists_elim fun c3 =>
        SepWP.exists_elim fun c4 => SepWP.exists_elim fun c5 =>
        SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
        SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 =>
        SepWP.exists_elim fun u4 => SepWP.exists_elim fun u5 => ?_
      rcases hcs4 with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
      apply sepWP_seq_lscro (mid := (blkPl_593).base + 236#64) hcrl4
      wp_steps_sync_pool ((blkPl_593).base + 236#64)
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      intro _hcrl5
      have _ := hx19_4
      apply sepWP_realign_buf14_p (buf := buf)
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun w1 => ?_
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      apply bind_sepWP_state_p; intro sf
      apply SepWP.done (by simp only [sf, wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      refine hk sf _
        (by simp only [sf, wp_norm, arm64_norm, *])
        (by simp only [sf, wp_norm, arm64_norm, *])
        (by simp only [sf, wp_norm, arm64_norm, *])
        ?_ ?_
      · refine ⟨by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, wp_norm, arm64_norm, *],
          by simp only [sf, calleeSavedVRegs, wp_norm, arm64_norm] at hvregs ⊢; exact hvregs⟩
      · have htrf : sf.trace = s0.trace := by simp only [sf, wp_norm, arm64_norm, htr4']
        have hevs_err : SplitIdEnv file (rustAllocEvents 14 1) := splitIdEnv_alloc14 file
        rw [← sepExists_sepConj_right]
        refine Entails.trans ?_
          (sepConj_mono_right
            (Entails.sepExists_right (rustAllocEvents 14 1)
              (Entails.pure_right ⟨htrf, hevs_err⟩ (Entails.refl _))))
        dsimp only [splitIdResultAt]
        rw [hnone]
        have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, wp_norm, arm64_norm, hsp2']
        have hbuf_pack : ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) =
            (buf ↦ₛ utf8 "malformed file") := buf14_close buf
        have hcells_back :
            (((s0.sp - 96#64) ↦₆₄ c5) ∗ ((s0.sp - 88#64) ↦₆₄ u0) ∗
              ((s0.sp - 80#64) ↦₆₄ u1) ∗ ((s0.sp - 72#64) ↦₆₄ u2) ∗
              ((s0.sp - 64#64) ↦₆₄ (lsρ sidBundleSym)) ∗
              ((s0.sp - 56#64) ↦₆₄ 6#64)) ⊢ cells (s0.sp - 96#64) 6 := by
          apply cells_sub_succ_entails 96 6
          apply cells_sub_succ_entails 88 5
          apply cells_sub_succ_entails 80 4
          apply cells_sub_succ_entails 72 3
          apply cells_sub_succ_entails 64 2
          rw [cells_sub_succ s0.sp 56 1 (by decide) (by decide), Nat.sub_self, cells_zero]
          simp only [sepConj_emp]
          exact Entails.sepExists_right _ (Entails.refl _)
        have hspe_pack :
            ((retAddr ↦₆₄ speWord 1) ∗
              ((retAddr + 8#64) ↦₆₄ 14#64) ∗
              ((retAddr + 16#64) ↦₆₄ buf) ∗
              ((retAddr + 24#64) ↦₆₄ 14#64) ∗
              A.repAlloc.live buf 14 1 ∗
              ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) ∗
              ((retAddr + 32#64) ↦₆₄ (lsρ sidBundleSym)) ∗
              ((retAddr + 40#64) ↦₆₄ 6#64) ∗
              ((lsρ sidBundleSym) ↦ᵣ utf8 "bundle")) ⊢
            speAt A.repAlloc (utf8 "bundle") retAddr .invalidState := by
          rw [hbuf_pack]
          exact speAt_invalidState_intro_p A.repAlloc (lsρ sidBundleSym) retAddr buf hptr_ne
        dsimp only [RustCliAllocBudget.repAlloc_live_norm] at hspe_pack
        have hstk_pack :
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
              (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
                stackAt (s0.sp - 96#64) extHookStack) ∗
              (((s0.sp - 96#64) ↦₆₄ c5) ∗ ((s0.sp - 88#64) ↦₆₄ u0) ∗
                ((s0.sp - 80#64) ↦₆₄ u1) ∗ ((s0.sp - 72#64) ↦₆₄ u2) ∗
                ((s0.sp - 64#64) ↦₆₄ (lsρ sidBundleSym)) ∗
                ((s0.sp - 56#64) ↦₆₄ 6#64)) ∗
              sidSavedRegs s0.sp s0 v24) ⊢
            stackAt s0.sp stk := by
          rw [← stackAt_hook_split (s0.sp - 96#64)]
          exact Entails.trans
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcells_back)))
            (stackAt_sid_pack_cells s0.sp stk s0 v24 hstk hstkle)
        rw [hsp_al0, speWord1_eq]
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hspe_pack
            (sepConj_mono_left
              (Q := sidMalfRO_p ∗ bytesAt ro fp file ∗
                A.pool lim (M.stepEvents (rustAllocEvents 14 1) st) sf)
              hstk_pack)) ?_)
        · unfold sidMalfRO_p sidSavedRegs lsρ
          dsimp only [blkPl_593, sidBundleSym, sidMalfSym]
          simp only [sepConj_assoc]
          exact Entails.of_eq (by sep_ac_rfl)
        · unfold sidMalfRO_p lsρ
          dsimp only [blkPl_593, sidBundleSym, sidMalfSym]
          simp only [sepConj_assoc]
          exact Entails.of_eq (by sep_ac_rfl)

private theorem cells48_open_p (sp0 : BitVec 64) :
    cells (sp0 - 48#64) 6 =
      ∃∗ s48 : BitVec 64, ∃∗ s40 : BitVec 64, ∃∗ s32 : BitVec 64,
      ∃∗ v24 : BitVec 64, ∃∗ s16 : BitVec 64, ∃∗ s8 : BitVec 64,
        ((sp0 - 48#64) ↦₆₄ s48) ∗ ((sp0 - 40#64) ↦₆₄ s40) ∗
        ((sp0 - 32#64) ↦₆₄ s32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ s16) ∗ ((sp0 - 8#64) ↦₆₄ s8) := by
  cells_unfold

private theorem ls_ge4_raw_p {u : BitVec 64} (hu : 4 ≤ u.toNat) :
    ConditionHolds CondCode.LS (AddWithCarry64 u (~~~3#64) true).2 = false := by
  simp only [ConditionHolds, AddWithCarry64]
  bv_bits

private theorem ule_ge4_false_p {u : BitVec 64} (hu : 4 ≤ u.toNat) :
    BitVec.ule u 3#64 = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

private theorem ult_ge4_true_p {u : BitVec 64} (hu : 4 ≤ u.toNat) :
    BitVec.ult 3#64 u = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

set_option linter.unusedSimpArgs false in
private theorem sid_prologue_err_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 : State} {ret fp : BitVec 64} {s48 s40 s32 v24 s16 s8 : BitVec 64}
    {R_frame : SepProp} {post : State → SepProp → Prop}
    (hal0 : s0.spAligned = true)
    (hpc : s0.pc = (blkPl_593).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = fp)
    (hx2 : s0.readReg64 .x2 = 0#64 ∨ s0.readReg64 .x2 = 1#64 ∨
      s0.readReg64 .x2 = 2#64 ∨ s0.readReg64 .x2 = 3#64)
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = (blkPl_593).base + 172#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 96#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = ret →
      SidUpperSaved s0 s1 →
      (P1 ⊢ sidSavedRegs s0.sp s0 v24 ∗ R_frame ∗ A.pool lim st s1) →
      post s1 P1) :
    SepWP (sidProg H)
      ((blkPl_593).base + 172#64) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗ R_frame ∗ A.pool lim st s0)
      post := by
  let _ := hal0
  have _ := And.intro hx0 hx1
  rcases hx2 with hx2 | hx2 | hx2 | hx2 <;>
  · let _ := hx2
    wp_steps_sync_pool ((blkPl_593).base + 172#64)
    apply bind_sepWP_state_p; intro s1
    apply SepWP.done (by simp only [s1, wp_norm, arm64_norm, *]) (by wp_norm_lhs)
    refine hnext s1 _
      (by simp only [s1, wp_norm, arm64_norm, *])
      (by simp only [s1, wp_norm, arm64_norm, *])
      (by simp only [s1, wp_norm, arm64_norm, *])
      (by simp only [s1, wp_norm, arm64_norm, *])
      (by simp only [s1, wp_norm, arm64_norm, *])
      (by simp only [s1, SidUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *])
      ?_
    unfold sidSavedRegs
    simp only [wp_norm, arm64_norm, sepConj_assoc]
    exact Entails.of_eq (by sep_ac_rfl)

set_option linter.unusedSimpArgs false in
private theorem sid_prologue_ok_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 : State} {ret fp : BitVec 64} {n : Nat} {s48 s40 s32 v24 s16 s8 : BitVec 64}
    {R_frame : SepProp} {post : State → SepProp → Prop}
    (hal0 : s0.spAligned = true)
    (hpc : s0.pc = (blkPl_593).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = fp)
    (hn : n + 4 < 2 ^ 64)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 n + 4#64)
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = (blkPl_593).base + 32#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 96#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = ret →
      s1.readReg64 .x1 = fp →
      s1.readReg64 .x2 = BitVec.ofNat 64 n + 4#64 →
      SidUpperSaved s0 s1 →
      (P1 ⊢ sidSavedRegs s0.sp s0 v24 ∗ R_frame ∗ A.pool lim st s1) →
      post s1 P1) :
    SepWP (sidProg H)
      ((blkPl_593).base + 32#64) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗ R_frame ∗ A.pool lim st s0)
      post := by
  let _ := hal0
  have hge4 : 4 ≤ (BitVec.ofNat 64 n + 4#64).toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hls_raw : ConditionHolds CondCode.LS
      (AddWithCarry64 (BitVec.ofNat 64 n + 4#64) (~~~3#64) true).2 = false :=
    ls_ge4_raw_p hge4
  have hls_norm : ConditionHolds CondCode.LS
      (AddWithCarry64 (BitVec.ofNat 64 n + 4#64) (bv% (2 ^ 64 - 4)) true).2 = false :=
    hls_raw
  have hls_ule : BitVec.ule (BitVec.ofNat 64 n + 4#64) 3#64 = false :=
    ule_ge4_false_p hge4
  have hls_ult : BitVec.ult 3#64 (BitVec.ofNat 64 n + 4#64) = true :=
    ult_ge4_true_p hge4
  have _ := And.intro hx0 (And.intro hx1
    (And.intro hx2 (And.intro hls_raw (And.intro hls_norm (And.intro hls_ule hls_ult)))))
  wp_steps_sync_pool ((blkPl_593).base + 32#64)
  apply bind_sepWP_state_p; intro s1
  apply SepWP.done (by simp only [s1, wp_norm, arm64_norm, *]) (by wp_norm_lhs)
  refine hnext s1 _
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, SidUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *])
    ?_
  unfold sidSavedRegs
  simp only [wp_norm, arm64_norm, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

theorem splitId_placed_ok_core [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDrop : subroutine_ok (lsProg_593 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)))
    (hstk : 96 + dropSpeStackX ≤ stk) :
    subroutine_ok (lsProg_593 H) (lsmpl.base 593)
      (splitIdSpecPlaced A lim SplitIdEnv stk) := by
  have hDrop' : subroutine_ok (sidProg H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)) := hDrop
  change subroutine_ok (sidProg H) (blkPl_593).base _
  apply subroutine_ok_of_sepWP
  intro ⟨x, st⟩ R s0 hpc0 hrun0 hpre hal0
  obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [splitIdSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2_nat, hfit0⟩, hpre⟩ := hpre
  have hfit14 : FitsEvents M lim st (rustAllocEvents 14 1) := fitsEvents_14_of_splitIdEnv hfit0
  have hfile_lt64 : x.file.length < 2 ^ 64 := hx2_nat ▸ (s0.readReg64 .x2).isLt
  have hstkle : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (bytesAt x.ro x.fp x.file ∗ memRegion x.ret 48 ∗ A.pool lim st s0 ∗ R) := by
      convert hpre using 1; sep_ac_rfl
    exact stk_le_pow64_of_roLoaded hcrl0.2 hm_stk
  have hpre_ro := sidMalfRO_bundle_intro_p hcrl0.2 hpre
  rw [stackAt_sid_split s0.sp stk hstk hstkle, cells48_open_p s0.sp] at hpre_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s48, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s40, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s32, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨v24, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s16, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s8, hpre_ro⟩ := hpre_ro
  refine ⟨(((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗
      (sidMalfRO_p ∗
        ((lsρ sidBundleSym) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        stackAt (s0.sp - 96#64) dropSpeStackX ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        bytesAt x.ro x.fp x.file ∗
        memRegion x.ret 48) ∗
      A.pool lim st s0,
    R,
    by convert hpre_ro using 1; sep_ac_rfl,
    ?_⟩
  have hclose : ∀ (sf : State) (P_f : SepProp),
      sf.pc = s0.readReg64 Reg.lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ sidMalfRO_p ∗
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SplitIdEnv x.file evs⌝ ∗
            splitIdResultAt A.repAlloc x.ret x.fp x.file ∗
            bytesAt x.ro x.fp x.file ∗
            stackAt s0.sp stk ∗
            A.pool lim (M.stepEvents evs st) sf) →
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (splitIdSpecPlaced A lim SplitIdEnv stk).post (x, st) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f _ _ hspf hcsf hent
    refine ⟨fun hmf => ?_, hspf, hcsf⟩
    dsimp only [splitIdSpecPlaced, withLsCodeRoLoaded]
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepConj_assoc] at hm1
    exact Satisfies.of_sep_right hm1
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 x.file.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx2_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfile_lt64]
  rcases x with ⟨ret, fp, file, ro⟩
  dsimp only at *
  rcases file with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
  · apply sepWP_seq_lscro (mid := (blkPl_593).base + 172#64) hcrl0
    refine sid_prologue_err_p hal0 hpc0 hrun0 hx0 hx1 (Or.inl hx2_bv)
      fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hP1 hcrl1 => ?_
    refine SepWP.weaken_pre ?_
      (step_err_path_p hC hstk hstkle hfit14 ret fp ro [] rfl v24 hal0 hcrl1
        hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hclose)
    exact Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl))
  · apply sepWP_seq_lscro (mid := (blkPl_593).base + 172#64) hcrl0
    refine sid_prologue_err_p hal0 hpc0 hrun0 hx0 hx1 (Or.inr (Or.inl hx2_bv))
      fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hP1 hcrl1 => ?_
    refine SepWP.weaken_pre ?_
      (step_err_path_p hC hstk hstkle hfit14 ret fp ro [b0] rfl v24 hal0 hcrl1
        hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hclose)
    exact Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl))
  · apply sepWP_seq_lscro (mid := (blkPl_593).base + 172#64) hcrl0
    refine sid_prologue_err_p hal0 hpc0 hrun0 hx0 hx1 (Or.inr (Or.inr (Or.inl hx2_bv)))
      fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hP1 hcrl1 => ?_
    refine SepWP.weaken_pre ?_
      (step_err_path_p hC hstk hstkle hfit14 ret fp ro [b0, b1] rfl v24 hal0 hcrl1
        hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hclose)
    exact Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl))
  · apply sepWP_seq_lscro (mid := (blkPl_593).base + 172#64) hcrl0
    refine sid_prologue_err_p hal0 hpc0 hrun0 hx0 hx1 (Or.inr (Or.inr (Or.inr hx2_bv)))
      fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hP1 hcrl1 => ?_
    refine SepWP.weaken_pre ?_
      (step_err_path_p hC hstk hstkle hfit14 ret fp ro [b0, b1, b2] rfl v24 hal0 hcrl1
        hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hclose)
    exact Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl))
  · have hrest64 : rest.length + 4 < 2 ^ 64 := by
      simp only [List.length_cons] at hfile_lt64
      omega
    have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 rest.length + 4#64 := by
      rw [hx2_bv]
      apply BitVec.eq_of_toNat_eq
      simp only [List.length_cons, BitVec.toNat_ofNat, BitVec.toNat_add]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    apply sepWP_seq_lscro (mid := (blkPl_593).base + 32#64) hcrl0
    refine sid_prologue_ok_p hal0 hpc0 hrun0 hx0 hx1 hrest64 hx2
      fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hx1_1 hx2_1 hcs1 hP1 hcrl1 => ?_
    refine SepWP.weaken_pre ?_
      (step_ok_path_p hC hDrop' hstk hstkle hfit14 ret fp ro b0 b1 b2 b3 rest v24 hal0 hcrl1
        hpc1 hrun1 hsp1 htr1 hx19_1 hx1_1 hx2_1 hcs1 hclose)
    exact Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl))

end Helpers

/-- `split_id` (Block `593`) satisfies `splitIdSpecPlaced A lim SplitIdEnv stk` under `[LibsignalPlacement]`. -/
theorem splitId_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDrop : subroutine_ok (lsProg_593 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)))
    (hstk : 0x60 + dropSpeStackX ≤ stk) :
    subroutine_ok (lsProg_593 H) (lsmpl.base 593)
      (splitIdSpecPlaced A lim SplitIdEnv stk) :=
  Helpers.splitId_placed_ok_core hC hDrop hstk

theorem splitId_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat} {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    (hDrop : subroutine_ok (lsProg_593 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)))
    (hstk : 0x60 + dropSpeStackX ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 593)
      (splitIdSpecPlaced A lim SplitIdEnv stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 593)
    (splitId_placed_ok_of_deps hC hDrop hstk) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudget
