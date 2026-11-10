/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.BV

/-!
# `Ok`-Branch `fs`-Preserving Relocatable `signal_session::public::split_signed` (Block `592`)

Strengthens `splitSignedSpecPlaced` on Block `592` with
`(splitSigned x.file).isSome = true → sf.fs = s0.fs` (`splitSignedSpecPlacedOkFs`) under
`AllocContractsFsPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd

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
open CryptoVerification.SignalSession.Cli (
  SplitGhost splitId splitIdResultAt splitSigned splitSignedResultAt utf8
)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_592 lsProg_592)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (
  ls_transfer_lscro stk_le_pow64_of_roLoaded
)
open CryptoVerification.SignalSession.Cli.SplitSigned.Helpers (
  SsgUpperSaved buf14_close buf14_open_lo cells48_open malfHead6 malfHi memRegion16_open
  ret48_open_signed_ok sp_sub_96_spAligned speAt_invalidState_intro_p speWord1_eq
  splitOkTag_eq ssgBundleSym ssgMalfRO_bundle_intro_p ssgMalfRO_p ssgMalfSym ssgSavedRegs
  stackAt_hook_split stackAt_ssg_pack_region stackAt_ssg_split stackAt_sub_split
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudgetFd (
  cliDropSpe_placed_caller_ok_x_fs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudget (SplitIdEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd (
  fs_eq_of_splitId_eq_some splitIdSpecPlacedOkFs splitId_placed_caller_ok_of_allocFs_fd
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsFsPlaced AllocContractsXCliPlaced splitSignedSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (
  AllocContractsFsPlaced.toAllocContractsX allocNoOom_lscro_of_cli
)
open scoped LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetAux.Simp
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetAux.Simp (
  append64_extract_hi_p append64_extract_lo_p sp_restore_96_p ssg_sub_add_p
)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetAux (
  SplitSignedEnv SplitSignedTailEnv bind_sepWP_state_p fitsEvents_14_of_splitSignedTailEnv
  sepWP_pack_w88_p sepWP_pull_pure_p sepWP_realign_buf14_p splitSignedEnv_ok ssgProg
  ssg_call_lscro_budget step_err_copy_path_p step_short_err_path_p
)

/-! ## `Ok`-Branch `fs`-Preserving Specification -/

/-- Strengthens `splitSignedSpecPlaced` with `(splitSigned x.file).isSome = true → sf.fs = s0.fs` in the postcondition, matching callers that branch on `splitSigned file` over the 48-byte `sret` buffer at `x.ret`. -/
def splitSignedSpecPlacedOkFs [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (SplitEnv : List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) : Spec (SplitGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.fp ∧
          (s.readReg64 .x2).toNat = x.file.length ∧
          FitsEnv M lim st (SplitEnv x.file)⌝ ∗
          bytesAt x.ro x.fp x.file ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ⌜(splitSigned x.file).isSome = true → sf.fs = s0.fs⌝ ∗
          ∃∗ evs : List AllocEvent,
            ⌜sf.trace = s0.trace ∧ SplitEnv x.file evs⌝ ∗
              splitSignedResultAt A.repAlloc x.ret x.fp x.file ∗
              bytesAt x.ro x.fp x.file ∗
              stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

theorem fs_eq_of_splitSigned_eq_some {file : List (BitVec 8)} {id : BitVec 32}
    {key sig : List (BitVec 8)} {s0 sf : State}
    (h : (splitSigned file).isSome = true → sf.fs = s0.fs)
    (hsome : splitSigned file = some (id, key, sig)) :
    sf.fs = s0.fs :=
  h (by simp [hsome])

theorem subroutine_ok_splitSignedSpecPlaced_of_okFs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SplitEnv : List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (splitSignedSpecPlacedOkFs A lim SplitEnv stk)) :
    subroutine_ok prog entry (splitSignedSpecPlaced A lim SplitEnv stk) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [splitSignedSpecPlacedOkFs, splitSignedSpecPlaced, withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

/-! ## Block `592` Proof -/

namespace Helpers

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  ssg_sub_add_p append64_extract_lo_p append64_extract_hi_p sp_restore_96_p

private theorem shim_fs_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsFsPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec stk).keepsFs) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.shim stk h1 h2) hi

@[local simp, local arm64_norm]
private theorem add64_sub64_64_p (a : BitVec 64) :
    (a + 64#64) - 64#64 = a := by
  bv_omega

@[local simp, local arm64_norm]
private theorem awc_sub64_fst_p (a : BitVec 64) :
    (AddWithCarry64 (a + 64#64) (~~~64#64) true).1 = a := by
  simp only [AddWithCarry64]
  bv_bits

@[local simp, local arm64_norm]
private theorem add64_add_neg64_p (a : BitVec 64) :
    (a + 64#64) + bv% (2 ^ 64 - 64) = a := by
  bv_omega

@[local simp, local arm64_norm]
private theorem zext32_trunc32_p (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

private theorem cs_ge64_raw_p {u : BitVec 64} (hu : 64 ≤ u.toNat) :
    ConditionHolds CondCode.CS (AddWithCarry64 u (~~~64#64) true).2 = true := by
  simp only [ConditionHolds, AddWithCarry64]
  bv_bits

private theorem ule_ge64_true_p {u : BitVec 64} (hu : 64 ≤ u.toNat) :
    BitVec.ule 64#64 u = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

private theorem ult_ge64_false_p {u : BitVec 64} (hu : 64 ≤ u.toNat) :
    BitVec.ult u 64#64 = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

set_option linter.unusedSimpArgs false in
theorem step_ok_signed_path_p_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SplitEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {subStk stk : Nat} {st : M.σ} {evs_sp : List AllocEvent}
    {post : State → SepProp → Prop}
    (hC : AllocContractsFsPlaced A lim H)
    (hDrop : subroutine_ok (ssgProg H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim).keepsFs))
    (hsub : dropSpeStackX ≤ subStk)
    (hstk : 96 + subStk ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8)) (id : BitVec 32) (rest : List (BitVec 8))
    (hsp_evs : SplitEnv file evs_sp)
    (hfit14 : FitsEvents M lim (M.stepEvents evs_sp st) (rustAllocEvents 14 1))
    (hsid : splitId file = some (id, rest))
    (hrest_lt64 : rest.length < 2 ^ 64)
    (hge64 : 64 ≤ rest.length)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_592).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hfs : s.fs = s0.fs)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hcs : SsgUpperSaved s0 s)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.pc = s0.readReg64 Reg.lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (∃ G : SepProp, P_f ⊢ G ∗
        ⌜(splitSigned file).isSome = true → sf.fs = s0.fs⌝ ∗
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
  have hsigned : splitSigned file =
      some (id, rest.take (rest.length - 64), rest.drop (rest.length - 64)) := by
    simp only [splitSigned, hsid, hge64, ↓reduceIte]
  have hkey_len : (rest.take (rest.length - 64)).length = rest.length - 64 := by
    rw [List.length_take]
    omega
  have hrest_bv : BitVec.ofNat 64 rest.length = BitVec.ofNat 64 (rest.length - 64) + 64#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hge_bv : 64 ≤ (BitVec.ofNat 64 (rest.length - 64) + 64#64).toNat := by
    rw [← hrest_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrest_lt64]
    exact hge64
  have hcs_raw := cs_ge64_raw_p hge_bv
  have hcs_norm : ConditionHolds CondCode.CS
      (AddWithCarry64 (BitVec.ofNat 64 (rest.length - 64) + 64#64) (bv% (2 ^ 64 - 65)) true).2 = true :=
    hcs_raw
  have hule := ule_ge64_true_p hge_bv
  have hult := ult_ge64_false_p hge_bv
  have _ := And.intro hcs_raw (And.intro hcs_norm (And.intro hule hult))
  have hshim := shim_fs_lscro_of_cli (callerProg := ssgProg H) hC (stk := extHookStack)
  have halloc := allocNoOom_lscro_of_cli (callerProg := ssgProg H) (AllocContractsFsPlaced.toAllocContractsX hC)
  clear hC
  have hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal
  dsimp only [splitIdResultAt]
  rw [hsid]
  dsimp only
  rw [← splitOkTag_eq, hrest_bv, memRegion16_open ((s0.sp - 96#64) + 32#64)]
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
  refine ssg_call_lscro_budget ((blkPl_592).base + 220#64) () hshim hcrl1
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
      ((s0.sp - 72#64) ↦₆₄ (BitVec.ofNat 64 (rest.length - 64) + 64#64)) ∗
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
    dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec]
    have hsp_eq : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, wp_norm, arm64_norm, hsp]
    rw [hsp_eq]
    generalize dropSpeStackX = dsz
    generalize extHookStack = hsz
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s_after_sh hcrl2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    refine sepWP_pull_pure_p (φ := s_after_sh.fs = s_sh.fs) (h := fun hfs2 => ?_)
    refine sepWP_pull_pure_p (φ := VmPreserved s_sh s_after_sh) (h := fun hvm_sh => ?_)
    refine sepWP_pull_pure_p (φ := s_after_sh.trace = s_sh.trace) (h := fun htr2 => ?_)
    refine ProofLib.SepWP.transport_budgetPool hvm_sh (hnext := ?_)
    have hx19_2 : s_after_sh.readReg64 .x19 = retAddr := by
      rw [hcsp2.1]; simp only [s_sh, wp_norm, arm64_norm, hx19]
    have hx20_2 : s_after_sh.readReg64 .x20 = id.zeroExtend 64 := by
      rw [hcsp2.2.1]; simp only [s_sh, wp_norm, arm64_norm]
    have hx21_2 : s_after_sh.readReg64 .x21 = fp + 4#64 := by
      rw [hcsp2.2.2.1]; simp only [s_sh, wp_norm, arm64_norm]
    have hx22_2 : s_after_sh.readReg64 .x22 = BitVec.ofNat 64 (rest.length - 64) := by
      rw [hcsp2.2.2.2.1]; simp only [s_sh, wp_norm, arm64_norm]
    have hsp2' : s_after_sh.sp = s0.sp - 96#64 := by
      rw [hsp2]; simp only [s_sh, wp_norm, arm64_norm, hsp]
    clear hsp2
    have hal2 : s_after_sh.spAligned = true := sp_sub_96_spAligned hal0 hsp2'
    let _ := hal2
    have htr2' : s_after_sh.trace = s0.trace := by
      rw [htr2]; simp only [s_sh, wp_norm, arm64_norm, htr]
    have hfs2' : s_after_sh.fs = s0.fs := by
      rw [hfs2]; simp only [s_sh, wp_norm, arm64_norm, hfs]
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
    refine ssg_call_lscro_budget ((blkPl_592).base + 232#64) (14, 1, st1) halloc hcrl3
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
        ((s0.sp - 72#64) ↦₆₄ (BitVec.ofNat 64 (rest.length - 64) + 64#64)) ∗
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
            LsRetAddr624 (s_al.readReg64 .lr)) = True :=
        eq_true ⟨by simp only [s_al, wp_norm, arm64_norm],
          by simp only [s_al, wp_norm, arm64_norm], hlay, hfit14,
          ⟨592, by decide, 232, by decide, by simp only [s_al, wp_norm, arm64_norm, *]; rfl⟩⟩
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
      have hx20_4 : s_after_al.readReg64 .x20 = id.zeroExtend 64 := by
        rw [hcsp4.2.1]; simp only [s_al, wp_norm, arm64_norm, hx20_2]
      have hx21_4 : s_after_al.readReg64 .x21 = fp + 4#64 := by
        rw [hcsp4.2.2.1]; simp only [s_al, wp_norm, arm64_norm, hx21_2]
      have hx22_4 : s_after_al.readReg64 .x22 = BitVec.ofNat 64 (rest.length - 64) := by
        rw [hcsp4.2.2.2.1]; simp only [s_al, wp_norm, arm64_norm, hx22_2]
      have hsp4' : s_after_al.sp = s0.sp - 96#64 := by
        rw [hsp4]; simp only [s_al, wp_norm, arm64_norm, hsp2']
      clear hsp4
      have hal4 : s_after_al.spAligned = true := sp_sub_96_spAligned hal0 hsp4'
      let _ := hal4
      have htr4' : s_after_al.trace = s0.trace := by
        rw [hacp_al.2.1]; simp only [s_al, wp_norm, arm64_norm, htr2']
      have hfs4' : s_after_al.fs = s0.fs := by
        rw [hacp_al.1]; simp only [s_al, wp_norm, arm64_norm, hfs2']
      have hcs4 : SsgUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved hcsp4
      set buf := s_after_al.readReg64 .x0 with hbuf_def
      let _ := hbuf_def
      have hptr_ne : buf ≠ 0#64 := hnull
      have hptr_beq : (buf == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
      have hptr_bne : (buf != 0#64) = true := bne_iff_ne.mpr hptr_ne
      have _ := And.intro hptr_beq hptr_bne
      apply sepWP_pack_w88_p (sp0 := s0.sp) (id := id)
      rw [buf14_open_lo buf]
      conv =>
        arg 4
        unfold ssgMalfRO_p
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun w88 => SepWP.exists_elim fun w0 => ?_
      apply sepWP_seq_lscro (mid := (blkPl_592).base + 256#64) hcrl4
      wp_steps_sync_pool ((blkPl_592).base + 256#64)
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
      have hal_dr : s_dr.spAligned = true :=
        sp_sub_96_spAligned hal0 (by simp only [s_dr, wp_norm, arm64_norm, hsp4'])
      have hcs_dr : SsgUpperSaved s0 s_dr := by
        rcases hcs4 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
        simp only [s_dr, SsgUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm, *]
      let st_al := M.stepEvents (rustAllocEvents 14 1) st1
      refine ssg_call_lscro_budget ((blkPl_592).base + 300#64)
        (⟨s0.sp - 96#64, utf8 "bundle", .invalidState⟩, st_al) hDrop hcrl6
        (by simp only [s_dr, wp_norm, arm64_norm, *])
        (by simp only [s_dr, wp_norm, arm64_norm, *])
        hal_dr
        (by simp only [s_dr, wp_norm, arm64_norm, *])
        (F := ssgMalfRO_p ∗
          ssgSavedRegs s0.sp s0 ∗
          memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
          bytesAt ro fp file ∗
          memRegion retAddr 48)
        ?_ (hnext := ?_)
      · dsimp only [Spec.keepsFs, dropSpeSpecX]
        have hx0_dr :
            (s_dr.readReg64 .x0 = s0.sp - 96#64 ∧
              LsRetAddr624 (s_dr.readReg64 .x30)) = True :=
          eq_true ⟨by simp only [s_dr, wp_norm, arm64_norm, *],
            ⟨592, by decide, 300, by decide, by simp only [s_dr, wp_norm, arm64_norm, *]; rfl⟩⟩
        have hsp_dr : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, wp_norm, arm64_norm, hsp4']
        have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, wp_norm, arm64_norm, hsp2']
        rw [hx0_dr, pure_true, emp_sepConj, hsp_dr, stackAt_hook_split (s0.sp - 96#64), hsp_al0]
        unfold ssgMalfRO_p
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
              (((s0.sp - 96#64) + 32#64) ↦₆₄ (lsρ ssgBundleSym)) ∗
              (((s0.sp - 96#64) + 40#64) ↦₆₄ 6#64) ∗
              ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle")) ⊢
            speAt A.repAlloc (utf8 "bundle") (s0.sp - 96#64) .invalidState := by
          rw [hbuf_pack]
          exact speAt_invalidState_intro_p A.repAlloc (lsρ ssgBundleSym) (s0.sp - 96#64) buf hptr_ne
        dsimp only [RustCliAllocBudget.repAlloc_live_norm] at hspe_pack
        have hdsz : s0.sp - 96#64 - BitVec.ofNat 64 dropSpeStackX = s0.sp - 16512#64 := by
          simp only [dropSpeStackX, extHookStack]; bv_omega
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q :=
            A.pool lim st_al s_dr ∗
              memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
              stackAt (s0.sp - 96#64) extHookStack ∗
              ssgMalfRO_p ∗
              ssgSavedRegs s0.sp s0 ∗
              memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
              bytesAt ro fp file ∗
              memRegion retAddr 48) hspe_pack) ?_)
        · unfold ssgMalfRO_p lsρ
          dsimp only [buf, Reg.x0, blkPl_592, ssgBundleSym, ssgMalfSym, st_al, st1]
          rw [hdsz]
          simp only [ssg_sub_add_p, BitVec.reduceSub, sepConj_assoc]
          generalize dropSpeStackX = dsz
          generalize extHookStack = hsz
          exact Entails.of_eq (by sep_ac_rfl)
        · unfold ssgMalfRO_p lsρ
          dsimp only [blkPl_592, ssgBundleSym, ssgMalfSym, st_al, st1]
          rw [hdsz]
          simp only [sepConj_assoc]
          generalize dropSpeStackX = dsz
          generalize extHookStack = hsz
          exact Entails.of_eq (by sep_ac_rfl)
      ·
        intro s_ep hcrl7 hpc7 hrun7 hsp7 hcsp7
        let _ := hcrl7
        dsimp only [Spec.keepsFs, dropSpeSpecX]
        refine sepWP_pull_pure_p (φ := s_ep.fs = s_dr.fs) (h := fun hfs7 => ?_)
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWP.exists_elim fun evs_dr => ?_
        refine sepWP_pull_pure_p (φ := s_ep.trace = s_dr.trace) (h := fun htr7 => ?_)
        refine sepWP_pull_pure_p (φ := FreeOnlyEvs evs_dr) (h := fun hfree_dr => ?_)
        have hx19_7 : s_ep.readReg64 .x19 = retAddr := by
          rw [hcsp7.1]; simp only [s_dr, wp_norm, arm64_norm, hx19_4]
        have hx20_7 : s_ep.readReg64 .x20 = id.zeroExtend 64 := by
          rw [hcsp7.2.1]; simp only [s_dr, wp_norm, arm64_norm, hx20_4]
        have hx21_7 : s_ep.readReg64 .x21 = fp + 4#64 := by
          rw [hcsp7.2.2.1]; simp only [s_dr, wp_norm, arm64_norm, hx21_4]
        have hx22_7 : s_ep.readReg64 .x22 = BitVec.ofNat 64 (rest.length - 64) := by
          rw [hcsp7.2.2.2.1]; simp only [s_dr, wp_norm, arm64_norm, hx22_4]
        have hsp7' : s_ep.sp = s0.sp - 96#64 := by
          rw [hsp7]; simp only [s_dr, wp_norm, arm64_norm, hsp4']
        clear hsp7
        have hal7 : s_ep.spAligned = true := sp_sub_96_spAligned hal0 hsp7'
        let _ := hal7
        have htr7' : s_ep.trace = s0.trace := by
          rw [htr7]; simp only [s_dr, wp_norm, arm64_norm, htr4']
        have hfs7' : s_ep.fs = s0.fs := by
          rw [hfs7]; simp only [s_dr, wp_norm, arm64_norm, hfs4']
        have hcs7 : SsgUpperSaved s0 s_ep := hcs_dr.trans_calleeSaved hcsp7
        rcases hcs7 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
        have hsdr_sp : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, wp_norm, arm64_norm, hsp4']
        dsimp only [st_al, st1]
        rw [← M.stepEvents_append, ← M.stepEvents_append]
        rw [hsdr_sp, ret48_open_signed_ok retAddr]
        unfold ssgSavedRegs
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWP.exists_elim fun r40 => SepWP.exists_elim fun r32 =>
          SepWP.exists_elim fun r24 => SepWP.exists_elim fun r16 =>
          SepWP.exists_elim fun r8 => SepWP.exists_elim fun r0 => ?_
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
          have htrf : sf.trace = s0.trace := by simp only [sf, wp_norm, arm64_norm, htr7']
          have hfsf : sf.fs = s0.fs := by simp only [sf, wp_norm, arm64_norm, hfs7']
          have hfs_ok : (splitSigned file).isSome = true → sf.fs = s0.fs := fun _ => hfsf
          have hevs : SplitSignedEnv SplitEnv file (evs_sp ++ (rustAllocEvents 14 1 ++ evs_dr)) :=
            splitSignedEnv_ok hsid hge64 hsp_evs hfree_dr
          try simp only [← sepExists_sepConj_right]
          refine Entails.trans ?_
            (sepConj_mono_right
              (Entails.pure_right hfs_ok
                (Entails.sepExists_right (evs_sp ++ (rustAllocEvents 14 1 ++ evs_dr))
                  (Entails.pure_right ⟨htrf, hevs⟩ (Entails.refl _)))))
          have hstk_pack :
              (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
                (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                  stackAt (s0.sp - 96#64) dropSpeStackX) ∗
                memRegion (s0.sp - 96#64) 48 ∗
                ssgSavedRegs s0.sp s0) ⊢
              stackAt s0.sp stk := by
            rw [← stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega)]
            exact stackAt_ssg_pack_region s0.sp subStk stk s0 hstk hstkle
          refine Entails.trans (Q :=
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
              (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                stackAt (s0.sp - 96#64) dropSpeStackX) ∗
              memRegion (s0.sp - 96#64) 48 ∗
              ssgSavedRegs s0.sp s0) ∗
            (ssgMalfRO_p ∗
              splitSignedResultAt A.repAlloc retAddr fp file ∗
              bytesAt ro fp file ∗
              A.pool lim (M.stepEvents (evs_sp ++ (rustAllocEvents 14 1 ++ evs_dr)) st) sf)) ?_
            (Entails.trans (sepConj_mono_left hstk_pack) ?_)
          · dsimp only [splitSignedResultAt]
            rw [hsigned]
            dsimp only
            rw [← splitOkTag_eq, hkey_len]
            unfold ssgSavedRegs
            simp only [sepConj_assoc]
            generalize dropSpeStackX = dsz
            exact Entails.of_eq (by sep_ac_rfl)
          · exact Entails.of_eq (by sep_ac_rfl)

set_option linter.unusedSimpArgs false in
private theorem ssg_prologue_p_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 : State} {ret fp : BitVec 64} {s48 s40 s32 s24 s16 s8 : BitVec 64}
    {R_frame : SepProp} {post : State → SepProp → Prop}
    (hal0 : s0.spAligned = true)
    (hpc : s0.pc = (blkPl_592).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = fp)
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = lsmpl.base 593 →
      s1.status = .Running →
      s1.sp = s0.sp - 96#64 →
      s1.trace = s0.trace →
      s1.fs = s0.fs →
      s1.readReg64 Reg.lr = (blkPl_592).base + 32#64 →
      s1.readReg64 .x0 = s0.sp - 96#64 →
      s1.readReg64 .x1 = fp →
      s1.readReg64 .x2 = s0.readReg64 .x2 →
      s1.readReg64 .x19 = ret →
      SsgUpperSaved s0 s1 →
      (P1 ⊢ ssgSavedRegs s0.sp s0 ∗ R_frame ∗ A.pool lim st s1) →
      post s1 P1) :
    SepWP (ssgProg H)
      (lsmpl.base 593) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ s24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗ R_frame ∗ A.pool lim st s0)
      post := by
  let _ := hal0
  have _ := And.intro hx0 hx1
  wp_steps_sync_pool (lsmpl.base 593)
  apply bind_sepWP_state_p; intro s1
  apply SepWP.done (by simp only [s1, wp_norm, arm64_norm, *]) (by wp_norm_lhs)
  refine hnext s1 _
    (by simp only [s1, wp_norm, arm64_norm])
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, wp_norm, arm64_norm])
    (by simp only [s1, wp_norm, arm64_norm])
    (by simp only [s1, wp_norm, arm64_norm])
    (by simp only [s1, wp_norm, arm64_norm])
    (by simp only [s1, wp_norm, arm64_norm])
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, wp_norm, arm64_norm])
    (by simp only [s1, wp_norm, arm64_norm, *])
    (by simp only [s1, SsgUpperSaved, calleeSavedVRegs, wp_norm, arm64_norm])
    ?_
  unfold ssgSavedRegs
  simp only [wp_norm, arm64_norm, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

theorem splitSigned_placed_ok_core_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SplitEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {splitStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hSplit : subroutine_ok (lsProg_592 H) (lsmpl.base 593)
      (splitIdSpecPlacedOkFs A lim SplitEnv splitStk))
    (hDrop : subroutine_ok (lsProg_592 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim).keepsFs))
    (hstk : 96 + max splitStk dropSpeStackX ≤ stk) :
    subroutine_ok (lsProg_592 H) (lsmpl.base 592)
      (splitSignedSpecPlacedOkFs A lim (SplitSignedEnv SplitEnv) stk) := by
  set subStk := max splitStk dropSpeStackX
  have hsub_sp : splitStk ≤ subStk := Nat.le_max_left _ _
  have hsub_dr : dropSpeStackX ≤ subStk := Nat.le_max_right _ _
  have hSplit' : subroutine_ok (ssgProg H) (lsmpl.base 593)
      (splitIdSpecPlacedOkFs A lim SplitEnv splitStk) := hSplit
  have hDrop' : subroutine_ok (ssgProg H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim).keepsFs) := hDrop
  have hCX : AllocContractsXCliPlaced A lim H := (AllocContractsFsPlaced.toAllocContractsX hC)
  change subroutine_ok (ssgProg H) (blkPl_592).base _
  apply subroutine_ok_of_sepWP
  intro ⟨x, st⟩ R s0 hpc0 hrun0 hpre hal0
  obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [splitSignedSpecPlacedOkFs] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2_nat, hfit0⟩, hpre⟩ := hpre
  have hfit_sp : FitsEnv M lim st (SplitEnv x.file) := hfit0.seq_left
  have hfile_lt64 : x.file.length < 2 ^ 64 := hx2_nat ▸ (s0.readReg64 .x2).isLt
  have hstkle : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (bytesAt x.ro x.fp x.file ∗ memRegion x.ret 48 ∗ A.pool lim st s0 ∗ R) := by
      convert hpre using 1; sep_ac_rfl
    exact stk_le_pow64_of_roLoaded hcrl0.2 hm_stk
  have hpre_ro := ssgMalfRO_bundle_intro_p hcrl0.2 hpre
  rw [stackAt_ssg_split s0.sp subStk stk hstk hstkle, cells48_open s0.sp] at hpre_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s48, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s40, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s32, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s24, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s16, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s8, hpre_ro⟩ := hpre_ro
  refine ⟨(((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ s24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗
      (ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        memRegion (s0.sp - 96#64) 48 ∗
        stackAt (s0.sp - 96#64) subStk ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        bytesAt x.ro x.fp x.file ∗
        memRegion x.ret 48) ∗
      A.pool lim st s0,
    R,
    by convert hpre_ro using 1; sep_ac_rfl,
    ?_⟩
  have hclose_ok : ∀ (sf : State) (P_f : SepProp),
      sf.pc = s0.readReg64 Reg.lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (∃ G : SepProp, P_f ⊢ G ∗
        ⌜(splitSigned x.file).isSome = true → sf.fs = s0.fs⌝ ∗
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SplitSignedEnv SplitEnv x.file evs⌝ ∗
            splitSignedResultAt A.repAlloc x.ret x.fp x.file ∗
            bytesAt x.ro x.fp x.file ∗
            stackAt s0.sp stk ∗
            A.pool lim (M.stepEvents evs st) sf) →
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (splitSignedSpecPlacedOkFs A lim (SplitSignedEnv SplitEnv) stk).post
          (x, st) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f _ _ hspf hcsf ⟨G, hent⟩
    refine ⟨fun hmf => ?_, hspf, hcsf⟩
    dsimp only [splitSignedSpecPlacedOkFs, withLsCodeRoLoaded]
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepConj_assoc] at hm1
    exact Satisfies.of_sep_right hm1
  have hclose_err : splitSigned x.file = none →
      ∀ (sf : State) (P_f : SepProp),
      sf.pc = s0.readReg64 Reg.lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (∃ G : SepProp, P_f ⊢ G ∗
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ SplitSignedEnv SplitEnv x.file evs⌝ ∗
            splitSignedResultAt A.repAlloc x.ret x.fp x.file ∗
            bytesAt x.ro x.fp x.file ∗
            stackAt s0.sp stk ∗
            A.pool lim (M.stepEvents evs st) sf) →
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (splitSignedSpecPlacedOkFs A lim (SplitSignedEnv SplitEnv) stk).post
          (x, st) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro hnone sf P_f hpcm hrunm hspf hcsf ⟨G, hent⟩
    refine hclose_ok sf P_f hpcm hrunm hspf hcsf ⟨G, ?_⟩
    exact Entails.trans hent
      (sepConj_mono_right
        (Entails.pure_right (by simp [hnone]) (Entails.refl _)))
  rcases x with ⟨ret, fp, file, ro⟩
  dsimp only at *
  apply sepWP_seq_lscro (mid := lsmpl.base 593) hcrl0
  refine ssg_prologue_p_fd hal0 hpc0 hrun0 hx0 hx1
    fun s1 P1 hpc1 hrun1 hsp1 htr1 hfs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hcs1 hP1 hcrl1 => ?_
  refine SepWP.weaken_pre hP1 ?_
  have hal1 : s1.spAligned = true := sp_sub_96_spAligned hal0 hsp1
  refine ssg_call_lscro_budget ((blkPl_592).base + 32#64) (⟨s0.sp - 96#64, fp, file, ro⟩, st)
    hSplit' hcrl1 hpc1 hrun1 hal1 hlr1
    (F := ssgSavedRegs s0.sp s0 ∗
      ssgMalfRO_p ∗
      ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - splitStk) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
      memRegion ret 48)
    ?_ (hnext := ?_)
  · rw [stackAt_sub_split (s0.sp - 96#64) splitStk subStk hsub_sp (by omega)]
    have hpure_sp :
        (s1.readReg64 .x0 = s0.sp - 96#64 ∧ s1.readReg64 .x1 = fp ∧
          (s1.readReg64 .x2).toNat = file.length ∧
          FitsEnv M lim st (SplitEnv file)) = True :=
      eq_true ⟨hx0_1, hx1_1, hx2_1 ▸ hx2_nat, hfit_sp⟩
    dsimp only
    rw [hpure_sp, pure_true, emp_sepConj, hsp1]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s2 hcrl2 hpc2 hrun2 hsp2 hcsp2
    dsimp only
    refine sepWP_pull_pure_p (φ := (splitId file).isSome = true → s2.fs = s1.fs)
      (h := fun hfseq_sp => ?_)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWP.exists_elim fun evs_sp => ?_
    refine sepWP_pull_pure_p (h := fun hp => ?_)
    rcases hp with ⟨htr2, hsp_evs⟩
    have hfit_tail : FitsEnv M lim (M.stepEvents evs_sp st) (SplitSignedTailEnv file) :=
      hfit0.seq_right hsp_evs
    have hx19_2 : s2.readReg64 .x19 = ret := hcsp2.1.trans hx19_1
    have hsp2' : s2.sp = s0.sp - 96#64 := hsp2.trans hsp1
    have htr2' : s2.trace = s0.trace := htr2.trans htr1
    have hcs2 : SsgUpperSaved s0 s2 := hcs1.trans_calleeSaved hcsp2
    have hpre2 :
        (splitIdResultAt A.repAlloc (s0.sp - 96#64) fp file ∗
          bytesAt ro fp file ∗
          stackAt s1.sp splitStk ∗
          A.pool lim (M.stepEvents evs_sp st) s2 ∗
          ssgSavedRegs s0.sp s0 ∗
          ssgMalfRO_p ∗
          ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
          memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - splitStk) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
          memRegion ret 48) ⊢
        (ssgMalfRO_p ∗
          ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
          splitIdResultAt A.repAlloc (s0.sp - 96#64) fp file ∗
          ssgSavedRegs s0.sp s0 ∗
          stackAt (s0.sp - 96#64) subStk ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
          bytesAt ro fp file ∗
          memRegion ret 48 ∗
          A.pool lim (M.stepEvents evs_sp st) s2) := by
      rw [hsp1, stackAt_sub_split (s0.sp - 96#64) splitStk subStk hsub_sp (by omega)]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWP.weaken_pre hpre2 ?_
    cases hsid : splitId file with
    | none =>
      have hnone_sg : splitSigned file = none := by
        simp only [splitSigned, hsid]
      exact step_err_copy_path_p hstk hstkle ret fp ro file hsp_evs hsid hal0
        hpc2 hrun2 hsp2' htr2' hx19_2 hcs2 (hclose_err hnone_sg)
    | some p =>
      rcases p with ⟨id, rest⟩
      have hfit14 : FitsEvents M lim (M.stepEvents evs_sp st) (rustAllocEvents 14 1) :=
        fitsEvents_14_of_splitSignedTailEnv hsid hfit_tail
      have hrest_lt : rest.length < 2 ^ 64 := by
        rcases file with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, tl⟩⟩⟩⟩ <;>
          simp [splitId] at hsid
        obtain ⟨_, rfl⟩ := hsid
        simp only [List.length_cons] at hfile_lt64
        omega
      by_cases hge64 : 64 ≤ rest.length
      · have hfs2' : s2.fs = s0.fs :=
          (fs_eq_of_splitId_eq_some hfseq_sp hsid).trans hfs1
        exact step_ok_signed_path_p_fd hC hDrop' hsub_dr hstk hstkle
          ret fp ro file id rest hsp_evs hfit14 hsid hrest_lt hge64 hal0 hcrl2
          hpc2 hrun2 hsp2' htr2' hfs2' hx19_2 hcs2 hclose_ok
      · have hlt64 : rest.length < 64 := by omega
        have hnone_sg : splitSigned file = none := by
          simp only [splitSigned, hsid, hge64, ↓reduceIte]
        exact step_short_err_path_p hCX hsub_dr hstk hstkle
          ret fp ro file id rest hsp_evs hfit14 hsid hlt64 hal0 hcrl2
          hpc2 hrun2 hsp2' htr2' hx19_2 hcs2 (hclose_err hnone_sg)

end Helpers

/-- `split_signed` (Block `592`) satisfies `splitSignedSpecPlacedOkFs` from `AllocContractsFsPlaced`, `splitIdSpecPlacedOkFs`, and `(dropSpeSpecX M A lim).keepsFs`. -/
theorem splitSigned_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SplitEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {splitStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hSplit : subroutine_ok (lsProg_592 H) (lsmpl.base 593)
      (splitIdSpecPlacedOkFs A lim SplitEnv splitStk))
    (hDrop : subroutine_ok (lsProg_592 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim).keepsFs))
    (hstk : 96 + max splitStk dropSpeStackX ≤ stk) :
    subroutine_ok (lsProg_592 H) (lsmpl.base 592)
      (splitSignedSpecPlacedOkFs A lim (SplitSignedEnv SplitEnv) stk) :=
  Helpers.splitSigned_placed_ok_core_fd hC hSplit hDrop hstk

theorem splitSigned_placed_caller_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SplitEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {splitStk stk : Nat} {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    (hC : AllocContractsFsPlaced A lim H)
    (hSplit : subroutine_ok (lsProg_592 H) (lsmpl.base 593)
      (splitIdSpecPlacedOkFs A lim SplitEnv splitStk))
    (hDrop : subroutine_ok (lsProg_592 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim).keepsFs))
    (hstk : 96 + max splitStk dropSpeStackX ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 592)
      (splitSignedSpecPlacedOkFs A lim (SplitSignedEnv SplitEnv) stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 592)
    (splitSigned_placed_ok_of_deps_fd hC hSplit hDrop hstk) hi

/-- `split_signed` (Block `592`) satisfies `splitSignedSpecPlacedOkFs` from `AllocContractsFsPlaced` alone. -/
theorem splitSigned_placed_ok_of_allocFs_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {splitStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hsplitStk : 96 + dropSpeStackX ≤ splitStk := by decide)
    (hstk : 96 + max splitStk dropSpeStackX ≤ stk) :
    subroutine_ok (lsProg_592 H) (lsmpl.base 592)
      (splitSignedSpecPlacedOkFs A lim (SplitSignedEnv SplitIdEnv) stk) :=
  splitSigned_placed_ok_of_deps_fd hC
    (splitId_placed_caller_ok_of_allocFs_fd
      (callerProg := lsProg_592 H) (i := 592) hC hsplitStk (by decide))
    (cliDropSpe_placed_caller_ok_x_fs
      (callerProg := lsProg_592 H) (i := 592) hC (by decide))
    hstk

theorem splitSigned_placed_caller_ok_of_allocFs_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {splitStk stk : Nat} {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    (hC : AllocContractsFsPlaced A lim H)
    (hsplitStk : 96 + dropSpeStackX ≤ splitStk := by decide)
    (hstk : 96 + max splitStk dropSpeStackX ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 592)
      (splitSignedSpecPlacedOkFs A lim (SplitSignedEnv SplitIdEnv) stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 592)
    (splitSigned_placed_ok_of_allocFs_fd hC hsplitStk hstk) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd
