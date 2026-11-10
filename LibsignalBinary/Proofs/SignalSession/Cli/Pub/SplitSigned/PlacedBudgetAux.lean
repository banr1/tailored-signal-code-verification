/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget Envelopes and Error Paths for `signal_session::public::split_signed`

Allocator event envelopes (`SplitSignedTailEnv`, `SplitSignedEnv`) and budget-threaded error-branch
lemmas (`step_err_copy_path_p`, `step_short_err_path_p`) for Block `592`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalHooks LibsignalPlacement lsmpl lsρ
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt speWord)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (
  splitId splitIdResultAt splitSigned splitSignedResultAt utf8
)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_592 blkPl_592)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (SepWP.call_lscro)
open CryptoVerification.SignalSession.Cli.SplitSigned.Helpers (
  SsgUpperSaved buf14_close buf14_open_lo buf14_realign cells6_of_words
  half32_pad_entails_cell64 malfHead6 malfHi malfLo memRegion16_open
  ret48_open_err sp_sub_96_spAligned speAt_invalidState_copy_open
  speAt_invalidState_intro_p speVecHeap speWord1_eq splitOkTag_eq ssgBundleSym
  ssgMalfRO_p ssgMalfSym ssgSavedRegs stackAt_hook_split
  stackAt_ssg_pack_cells stackAt_sub_split
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved rustAllocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (
  allocNoOom_lscro_of_cli shim_lscro_of_cli
)

/-- Tail allocator events of `split_signed` after `split_id`: none when `splitId file = none`, a 14-byte allocation when `rest.length < 64`, and a 14-byte allocation plus `FreeOnlyEvs` drop when `64 ≤ rest.length`. -/
def SplitSignedTailEnv (file : List (BitVec 8)) : List AllocEvent → Prop :=
  match splitId file with
  | none => (· = [])
  | some (_, rest) =>
    if rest.length < 64 then (· = rustAllocEvents 14 1)
    else SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs

/-- Full allocator event envelope of `split_signed` parameterized by `split_id`'s `SplitEnv`. -/
def SplitSignedEnv (SplitEnv : List (BitVec 8) → List AllocEvent → Prop)
    (file : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (SplitEnv file) (SplitSignedTailEnv file)

theorem splitSignedTailEnv_alloc14 {file : List (BitVec 8)} {id : BitVec 32}
    {rest : List (BitVec 8)} (hsid : splitId file = some (id, rest)) :
    SplitSignedTailEnv file (rustAllocEvents 14 1) := by
  unfold SplitSignedTailEnv
  rw [hsid]
  dsimp only
  split
  · rfl
  · exact SeqEnv.inl rfl

theorem fitsEvents_14_of_splitSignedTailEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {file : List (BitVec 8)} {id : BitVec 32} {rest : List (BitVec 8)}
    (hsid : splitId file = some (id, rest))
    (hfit : FitsEnv M lim st (SplitSignedTailEnv file)) :
    FitsEvents M lim st (rustAllocEvents 14 1) :=
  hfit _ (splitSignedTailEnv_alloc14 hsid)

theorem splitSignedEnv_none {SplitEnv : List (BitVec 8) → List AllocEvent → Prop}
    {file : List (BitVec 8)} {evs_sp : List AllocEvent}
    (hsp : SplitEnv file evs_sp) :
    SplitSignedEnv SplitEnv file evs_sp :=
  SeqEnv.inl hsp

theorem splitSignedEnv_short {SplitEnv : List (BitVec 8) → List AllocEvent → Prop}
    {file : List (BitVec 8)} {id : BitVec 32} {rest : List (BitVec 8)}
    {evs_sp : List AllocEvent}
    (hsid : splitId file = some (id, rest))
    (hlt64 : rest.length < 64)
    (hsp : SplitEnv file evs_sp) :
    SplitSignedEnv SplitEnv file (evs_sp ++ rustAllocEvents 14 1) := by
  refine SeqEnv.append hsp ?_
  simp only [SplitSignedTailEnv, hsid, hlt64, ↓reduceIte]

theorem splitSignedEnv_ok {SplitEnv : List (BitVec 8) → List AllocEvent → Prop}
    {file : List (BitVec 8)} {id : BitVec 32} {rest : List (BitVec 8)}
    {evs_sp evs_dr : List AllocEvent}
    (hsid : splitId file = some (id, rest))
    (hge64 : 64 ≤ rest.length)
    (hsp : SplitEnv file evs_sp)
    (hdr : FreeOnlyEvs evs_dr) :
    SplitSignedEnv SplitEnv file (evs_sp ++ (rustAllocEvents 14 1 ++ evs_dr)) := by
  refine SeqEnv.append hsp ?_
  have hnot_lt : ¬ rest.length < 64 := by omega
  simp only [SplitSignedTailEnv, hsid, hnot_lt, ↓reduceIte]
  exact SeqEnv.append rfl hdr

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

noncomputable abbrev ssgProg [LibsignalPlacement] (H : LibsignalHooks) : Program :=
  (blkPC_592).rebase (blkPl_592).base H

theorem bind_sepWP_state_p {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

theorem sepWP_pull_pure_p {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {φ : Prop} {Q : State → SepProp → Prop}
    (hf : P = ⌜φ⌝ ∗ F := by sep_focus)
    (h : φ → SepWP prog ret s F Q) :
    SepWP prog ret s P Q := by
  rw [hf]
  exact SepWP.pure_elim h

theorem sepWP_realign_buf14_p {prog : Program} {ret : BitVec 64} {s : State}
    {P F1 F2 : SepProp} {buf : BitVec 64} {Q : State → SepProp → Prop}
    (hf1 : P = (buf ↦₆₄ malfLo) ∗ F1 := by sep_focus)
    (hf2 : F1 = memRegion (buf + 8#64) 6 ∗ F2 := by sep_focus)
    (h : SepWP prog ret s
      ((buf ↦ₛ malfHead6) ∗ (∃∗ w1 : BitVec 64, (buf + 6#64) ↦₆₄ w1) ∗ F2) Q) :
    SepWP prog ret s P Q := by
  rw [hf1, hf2, ← sepConj_assoc]
  exact SepWP.weaken_pre
    (Entails.trans (sepConj_mono_left (buf14_realign buf)) (Entails.of_eq (sepConj_assoc _ _ _))) h

theorem sepWP_pack_w88_p {prog : Program} {ret : BitVec 64} {s : State}
    {P F1 F2 : SepProp} {sp0 : BitVec 64} {id : BitVec 32} {Q : State → SepProp → Prop}
    (hf1 : P = ((sp0 - 88#64) ↦₃₂ id) ∗ F1 := by sep_focus)
    (hf2 : F1 = memRegion (sp0 - 84#64) 4 ∗ F2 := by sep_focus)
    (h : SepWP prog ret s ((∃∗ w88 : BitVec 64, (sp0 - 88#64) ↦₆₄ w88) ∗ F2) Q) :
    SepWP prog ret s P Q := by
  have hw88 : (((sp0 - 88#64) ↦₃₂ id) ∗ memRegion (sp0 - 84#64) 4) ⊢
      ∃∗ w88 : BitVec 64, (sp0 - 88#64) ↦₆₄ w88 := by
    have ha84 : (sp0 - 88#64) + 4#64 = sp0 - 84#64 := by bv_omega
    simpa only [ha84] using half32_pad_entails_cell64 (sp0 - 88#64) id
  rw [hf1, hf2, ← sepConj_assoc]
  exact SepWP.weaken_pre (sepConj_mono_left hw88) h

namespace Simp

@[scoped simp]
theorem ssg_sub_add_p (a k m : BitVec 64) : a - k + m = a - (k - m) := by
  bv_omega

@[scoped simp]
theorem append64_extract_lo_p (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[scoped simp]
theorem append64_extract_hi_p (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[scoped simp]
theorem sp_restore_96_p (sp0 : BitVec 64) :
    sp0 - 96#64 + 96#64 = sp0 := by
  bv_bits

end Simp

open scoped Simp
open Simp (append64_extract_hi_p append64_extract_lo_p sp_restore_96_p ssg_sub_add_p)
attribute [local arm64_norm]
  ssg_sub_add_p append64_extract_lo_p append64_extract_hi_p sp_restore_96_p

theorem cs_lt64_raw_p {u : BitVec 64} (hu : u.toNat < 64) :
    ConditionHolds CondCode.CS (AddWithCarry64 u (~~~64#64) true).2 = false := by
  simp only [ConditionHolds, AddWithCarry64]
  bv_bits

theorem ule_lt64_false_p {u : BitVec 64} (hu : u.toNat < 64) :
    BitVec.ule 64#64 u = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

theorem ult_lt64_true_p {u : BitVec 64} (hu : u.toNat < 64) :
    BitVec.ult u 64#64 = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

theorem ssg_call_lscro_budget [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
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

/-! ## `splitId file = none`: 48-Byte `Err` Copy -/

set_option linter.unusedSimpArgs false in
theorem step_err_copy_path_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SplitEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {subStk stk : Nat} {st : M.σ} {evs_sp : List AllocEvent}
    {post : State → SepProp → Prop}
    (hstk : 96 + subStk ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8))
    (hsp_evs : SplitEnv file evs_sp)
    (hnone : splitId file = none)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hpc : s.pc = (blkPl_592).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hcs : SsgUpperSaved s0 s)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.pc = s0.readReg64 Reg.lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (∃ G : SepProp, P_f ⊢ G ∗
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SplitSignedEnv SplitEnv file evs⌝ ∗
            splitSignedResultAt A.repAlloc retAddr fp file ∗
            bytesAt ro fp file ∗
            stackAt s0.sp stk ∗
            A.pool lim (M.stepEvents evs st) sf) →
      post sf P_f) :
    SepWP (ssgProg H) (s0.readReg64 Reg.lr) s
      (ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        splitIdResultAt A.repAlloc (s0.sp - 96#64) fp file ∗
        ssgSavedRegs s0.sp s0 ∗
        stackAt (s0.sp - 96#64) subStk ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        bytesAt ro fp file ∗
        memRegion retAddr 48 ∗
        A.pool lim (M.stepEvents evs_sp st) s)
      post := by
  have hsigned : splitSigned file = none := by
    simp only [splitSigned, hnone]
  have hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal
  rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
  dsimp only [splitIdResultAt]
  rw [hnone, speAt_invalidState_copy_open A.repAlloc (s0.sp - 96#64), ret48_open_err retAddr]
  unfold ssgSavedRegs
  simp only [pointsTo64_split32 (retAddr + 8#64), BitVec.add_assoc, BitVec.reduceAdd,
    ssg_sub_add_p, BitVec.reduceSub, ← speWord1_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 =>
    SepWP.exists_elim fun u4 => SepWP.exists_elim fun u5 =>
    SepWP.exists_elim fun strPtr => SepWP.exists_elim fun bs =>
    SepWP.exists_elim fun cap => SepWP.exists_elim fun ptr => ?_
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
  · refine ⟨ssgMalfRO_p ∗ ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle"), ?_⟩
    have htrf : sf.trace = s0.trace := by simp only [sf, wp_norm, arm64_norm, htr]
    have hevs : SplitSignedEnv SplitEnv file evs_sp := splitSignedEnv_none hsp_evs
    refine Entails.trans ?_
      (sepConj_mono_right
        (Entails.sepExists_right evs_sp (Entails.pure_right ⟨htrf, hevs⟩ (Entails.refl _))))
    dsimp only [splitSignedResultAt]
    rw [hsigned]
    have hspe_dst :
        ((retAddr ↦₆₄ speWord 1) ∗
          ((retAddr + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((retAddr + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((retAddr + 16#64) ↦₆₄ ptr) ∗
          ((retAddr + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((retAddr + 32#64) ↦₆₄ strPtr) ∗
          ((retAddr + 40#64) ↦₆₄ 6#64) ∗
          speVecHeap A.repAlloc bs cap ptr ∗
          (strPtr ↦ᵣ utf8 "bundle")) ⊢
        speAt A.repAlloc (utf8 "bundle") retAddr .invalidState := by
      rw [speAt_invalidState_copy_open A.repAlloc retAddr]
      exact Entails.sepExists_right strPtr (Entails.sepExists_right bs
        (Entails.sepExists_right cap (Entails.sepExists_right ptr
          (Entails.of_eq (by sep_ac_rfl)))))
    have hcells_src :
        (((s0.sp - 96#64) ↦₆₄ speWord 1) ∗
          ((s0.sp - 88#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s0.sp - 84#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s0.sp - 80#64) ↦₆₄ ptr) ∗
          ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((s0.sp - 64#64) ↦₆₄ strPtr) ∗
          ((s0.sp - 56#64) ↦₆₄ 6#64)) ⊢
        cells (s0.sp - 96#64) 6 := by
      refine Entails.trans ?_
        (cells6_of_words s0.sp (speWord 1) cap ptr (BitVec.ofNat 64 bs.length) strPtr 6#64)
      rw [pointsTo64_split32 (s0.sp - 88#64) cap]
      simp only [ssg_sub_add_p, BitVec.reduceSub]
      exact Entails.of_eq (by sep_ac_rfl)
    have hstk_pack :
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
          stackAt (s0.sp - 96#64) subStk ∗
          (((s0.sp - 96#64) ↦₆₄ speWord 1) ∗
            ((s0.sp - 88#64) ↦₃₂ cap.extractLsb' 0 32) ∗
            ((s0.sp - 84#64) ↦₃₂ cap.extractLsb' 32 32) ∗
            ((s0.sp - 80#64) ↦₆₄ ptr) ∗
            ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ((s0.sp - 64#64) ↦₆₄ strPtr) ∗
            ((s0.sp - 56#64) ↦₆₄ 6#64)) ∗
          ssgSavedRegs s0.sp s0) ⊢
        stackAt s0.sp stk :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcells_src)))
        (stackAt_ssg_pack_cells s0.sp subStk stk s0 hstk hstkle)
    rw [speWord1_eq]
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono hspe_dst
        (sepConj_mono_left
          (Q := ssgMalfRO_p ∗ ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
            bytesAt ro fp file ∗ A.pool lim (M.stepEvents evs_sp st) sf)
          hstk_pack)) ?_)
    · unfold ssgSavedRegs
      simp only [sepConj_assoc]
      exact Entails.of_eq (by sep_ac_rfl)
    · generalize stackAt s0.sp stk = topStk
      exact Entails.of_eq (by sep_ac_rfl)

/-! ## `rest.length < 64`: Construct `"malformed file"` Error -/

set_option linter.unusedSimpArgs false in
theorem step_short_err_path_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SplitEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {subStk stk : Nat} {st : M.σ} {evs_sp : List AllocEvent}
    {post : State → SepProp → Prop}
    (hC : AllocContractsXCliPlaced A lim H)
    (hsub : dropSpeStackX ≤ subStk)
    (hstk : 96 + subStk ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8)) (id : BitVec 32) (rest : List (BitVec 8))
    (hsp_evs : SplitEnv file evs_sp)
    (hfit14 : FitsEvents M lim (M.stepEvents evs_sp st) (rustAllocEvents 14 1))
    (hsid : splitId file = some (id, rest))
    (hlt64 : rest.length < 64)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_592).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hcs : SsgUpperSaved s0 s)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.pc = s0.readReg64 Reg.lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (∃ G : SepProp, P_f ⊢ G ∗
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SplitSignedEnv SplitEnv file evs⌝ ∗
            splitSignedResultAt A.repAlloc retAddr fp file ∗
            bytesAt ro fp file ∗
            stackAt s0.sp stk ∗
            A.pool lim (M.stepEvents evs st) sf) →
      post sf P_f) :
    SepWP (ssgProg H) (s0.readReg64 Reg.lr) s
      (ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        splitIdResultAt A.repAlloc (s0.sp - 96#64) fp file ∗
        ssgSavedRegs s0.sp s0 ∗
        stackAt (s0.sp - 96#64) subStk ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        bytesAt ro fp file ∗
        memRegion retAddr 48 ∗
        A.pool lim (M.stepEvents evs_sp st) s)
      post := by
  let st1 := M.stepEvents evs_sp st
  have hsigned : splitSigned file = none := by
    simp only [splitSigned, hsid, show ¬ (64 ≤ rest.length) by omega, ↓reduceIte]
  have hshim := shim_lscro_of_cli (callerProg := ssgProg H) hC (stk := extHookStack)
  have halloc := allocNoOom_lscro_of_cli (callerProg := ssgProg H) hC
  clear hC
  have hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal
  have hlt_bv : (BitVec.ofNat 64 rest.length).toNat < 64 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hlt64
  have hcs_raw := cs_lt64_raw_p hlt_bv
  have hcs_norm : ConditionHolds CondCode.CS
      (AddWithCarry64 (BitVec.ofNat 64 rest.length) (bv% (2 ^ 64 - 65)) true).2 = false :=
    hcs_raw
  have hule := ule_lt64_false_p hlt_bv
  have hult := ult_lt64_true_p hlt_bv
  have _ := And.intro hcs_raw (And.intro hcs_norm (And.intro hule hult))
  dsimp only [splitIdResultAt]
  rw [hsid, ← splitOkTag_eq, memRegion16_open ((s0.sp - 96#64) + 32#64)]
  simp only [ssg_sub_add_p, BitVec.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWP.exists_elim fun z1 => SepWP.exists_elim fun z0 => ?_
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
  intro hcrl1
  apply bind_sepWP_state_p; intro s_sh
  have hal_sh : s_sh.spAligned = true :=
    sp_sub_96_spAligned hal0 (by simp only [s_sh, wp_norm, arm64_norm, hsp])
  have hcs_sh : SsgUpperSaved s0 s_sh := by
    rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
    simp only [s_sh, SsgUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *]
  refine ssg_call_lscro_budget ((blkPl_592).base + 64#64) () hshim hcrl1
    (by simp only [s_sh, wp_norm, arm64_norm, *])
    (by simp only [s_sh, wp_norm, arm64_norm, *])
    hal_sh
    (by simp only [s_sh, wp_norm, arm64_norm, *])
    (F := ssgMalfRO_p ∗
      ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
      ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
      ((s0.sp - 88#64) ↦₃₂ id) ∗
      memRegion (s0.sp - 84#64) 4 ∗
      ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
      ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      ((s0.sp - 64#64) ↦₆₄ z0) ∗
      ((s0.sp - 56#64) ↦₆₄ z1) ∗
      ssgSavedRegs s0.sp s0 ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
      bytesAt ro fp file ∗
      memRegion retAddr 48 ∗ A.pool lim st1 s_sh)
    ?_ (hnext := ?_)
  · rw [stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega),
      stackAt_hook_split (s0.sp - 96#64)]
    dsimp only [withStack, sessionShimBudgetSpec]
    have hsp_eq : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, wp_norm, arm64_norm, hsp]
    rw [hsp_eq]
    generalize dropSpeStackX = dsz
    generalize extHookStack = hsz
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s_after_sh hcrl2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
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
    have hcs2 : SsgUpperSaved s0 s_after_sh := hcs_sh.trans_calleeSaved hcsp2
    apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl2
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
    intro hcrl3
    apply bind_sepWP_state_p; intro s_al
    have hal_al : s_al.spAligned = true :=
      sp_sub_96_spAligned hal0 (by simp only [s_al, wp_norm, arm64_norm, hsp2'])
    have hcs_al : SsgUpperSaved s0 s_al := by
      rcases hcs2 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
      simp only [s_al, SsgUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *]
    have hlay : RustLayoutOk 14 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
    refine ssg_call_lscro_budget ((blkPl_592).base + 76#64) (14, 1, st1) halloc hcrl3
      (by simp only [s_al, wp_norm, arm64_norm, *])
      (by simp only [s_al, wp_norm, arm64_norm, *])
      hal_al
      (by simp only [s_al, wp_norm, arm64_norm, *])
      (F := ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
        ((s0.sp - 88#64) ↦₃₂ id) ∗
        memRegion (s0.sp - 84#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
        ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
        ((s0.sp - 64#64) ↦₆₄ z0) ∗
        ((s0.sp - 56#64) ↦₆₄ z1) ∗
        ssgSavedRegs s0.sp s0 ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        bytesAt ro fp file ∗
        memRegion retAddr 48)
      ?_ (hnext := ?_)
    · dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack]
      have hpure_al :
          ((s_al.readReg64 .x0).toNat = 14 ∧ (s_al.readReg64 .x1).toNat = 1 ∧
            RustLayoutOk 14 1 ∧ FitsEvents M lim st1 (rustAllocEvents 14 1) ∧
            LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_al.readReg64 .lr)) = True :=
        eq_true ⟨by simp only [s_al, wp_norm, arm64_norm],
          by simp only [s_al, wp_norm, arm64_norm], hlay, hfit14,
          ⟨592, by decide, 76, by decide, by simp only [s_al, wp_norm, arm64_norm]; rfl⟩⟩
      have hsp_eq1 : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, wp_norm, arm64_norm, hsp]
      have hsp_eq2 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, wp_norm, arm64_norm, hsp2']
      have hdsz : s0.sp - 96#64 - BitVec.ofNat 64 dropSpeStackX = s0.sp - 16512#64 := by
        simp only [dropSpeStackX, extHookStack]; bv_omega
      rw [hpure_al, pure_true, emp_sepConj, hsp_eq1, hsp_eq2, hdsz]
      generalize dropSpeStackX = dsz
      generalize extHookStack = hsz
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after_al hcrl4 hpc4 hrun4 hsp4 hcsp4
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
      have hcs4 : SsgUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved hcsp4
      set buf := s_after_al.readReg64 .x0 with hbuf_def
      let _ := hbuf_def
      have hptr_ne : buf ≠ 0#64 := hnull
      have hptr_beq : (buf == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
      have hptr_bne : (buf != 0#64) = true := bne_iff_ne.mpr hptr_ne
      have _ := And.intro hptr_beq hptr_bne
      apply sepWP_pack_w88_p (sp0 := s0.sp) (id := id)
      rw [buf14_open_lo buf, ret48_open_err retAddr]
      unfold ssgMalfRO_p ssgSavedRegs
      dsimp only [st1]
      rw [← M.stepEvents_append]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun w88 => SepWP.exists_elim fun w0 =>
        SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
        SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 =>
        SepWP.exists_elim fun u4 => SepWP.exists_elim fun u5 => ?_
      rcases hcs4 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
      apply sepWP_seq_lscro (mid := (blkPl_592).base + 116#64) hcrl4
      wp_steps_sync_pool ((blkPl_592).base + 116#64)
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      intro _
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
      · refine ⟨ssgMalfRO_p, ?_⟩
        have htrf : sf.trace = s0.trace := by simp only [sf, wp_norm, arm64_norm, htr4']
        have hevs : SplitSignedEnv SplitEnv file (evs_sp ++ rustAllocEvents 14 1) :=
          splitSignedEnv_short hsid hlt64 hsp_evs
        refine Entails.trans ?_
          (sepConj_mono_right
            (Entails.sepExists_right (evs_sp ++ rustAllocEvents 14 1)
              (Entails.pure_right ⟨htrf, hevs⟩ (Entails.refl _))))
        dsimp only [splitSignedResultAt]
        rw [hsigned]
        have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, wp_norm, arm64_norm, hsp2']
        have hbuf_pack : ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) =
            (buf ↦ₛ utf8 "malformed file") := buf14_close buf
        have hcells_back :
            (((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗ ((s0.sp - 88#64) ↦₆₄ u5) ∗
              ((s0.sp - 80#64) ↦₆₄ buf) ∗ ((s0.sp - 72#64) ↦₆₄ 14#64) ∗
              ((s0.sp - 64#64) ↦₆₄ (lsρ ssgBundleSym)) ∗
              ((s0.sp - 56#64) ↦₆₄ 6#64)) ⊢ cells (s0.sp - 96#64) 6 :=
          cells6_of_words s0.sp (bv% (2 ^ 64 - 2)) u5 buf 14#64
            (lsρ ssgBundleSym) 6#64
        have hspe_pack :
            ((retAddr ↦₆₄ speWord 1) ∗
              ((retAddr + 8#64) ↦₆₄ 14#64) ∗
              ((retAddr + 16#64) ↦₆₄ buf) ∗
              ((retAddr + 24#64) ↦₆₄ 14#64) ∗
              A.repAlloc.live buf 14 1 ∗
              ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) ∗
              ((retAddr + 32#64) ↦₆₄ (lsρ ssgBundleSym)) ∗
              ((retAddr + 40#64) ↦₆₄ 6#64) ∗
              ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle")) ⊢
            speAt A.repAlloc (utf8 "bundle") retAddr .invalidState := by
          rw [hbuf_pack]
          exact speAt_invalidState_intro_p A.repAlloc (lsρ ssgBundleSym) retAddr buf hptr_ne
        dsimp only [RustCliAllocBudget.repAlloc_live_norm] at hspe_pack
        have hstk_pack :
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
              (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
                  stackAt (s0.sp - 96#64) extHookStack)) ∗
              (((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗ ((s0.sp - 88#64) ↦₆₄ u5) ∗
                ((s0.sp - 80#64) ↦₆₄ buf) ∗ ((s0.sp - 72#64) ↦₆₄ 14#64) ∗
                ((s0.sp - 64#64) ↦₆₄ (lsρ ssgBundleSym)) ∗
                ((s0.sp - 56#64) ↦₆₄ 6#64)) ∗
              ssgSavedRegs s0.sp s0) ⊢
            stackAt s0.sp stk := by
          rw [← stackAt_hook_split (s0.sp - 96#64),
            ← stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega)]
          exact Entails.trans
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcells_back)))
            (stackAt_ssg_pack_cells s0.sp subStk stk s0 hstk hstkle)
        rw [hsp_al0, speWord1_eq]
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hspe_pack
            (sepConj_mono_left
              (Q := ssgMalfRO_p ∗ bytesAt ro fp file ∗
                A.pool lim (M.stepEvents (evs_sp ++ rustAllocEvents 14 1) st) sf)
              hstk_pack)) ?_)
        · unfold ssgMalfRO_p ssgSavedRegs lsρ
          dsimp only [buf, Reg.x0, blkPl_592, ssgBundleSym, ssgMalfSym]
          have hdsz : s0.sp - 96#64 - BitVec.ofNat 64 dropSpeStackX = s0.sp - 16512#64 := by
            simp only [dropSpeStackX, extHookStack]; bv_omega
          rw [hdsz]
          simp only [sepConj_assoc]
          generalize dropSpeStackX = dsz
          generalize extHookStack = hsz
          exact Entails.of_eq (by sep_ac_rfl)
        · unfold ssgMalfRO_p lsρ
          dsimp only [blkPl_592, ssgBundleSym, ssgMalfSym]
          simp only [sepConj_assoc]
          generalize stackAt s0.sp stk = topStk
          exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetAux
