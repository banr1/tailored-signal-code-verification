/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3ExactPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ErrK2PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopPeel
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Closed `VerNeTightTopRawEnv` Stage-P3/P4 Version-Mismatch Body

Proves `cliVerNe1e04_full_placed_ok_raw` under `[LibsignalFullPlacement]`, sequencing
`overVerNe_1e04_to_1e78_frozen_placed_at` (`VerNeS1Env`), the 1-element `previous_sessions` loop
(`SeqEnv (VerNeSessionCancelRawEnv enc) FreeOnlyEvs` on block `518`, `+0x1e78 → +0x2cfc`), and
`over_ver_ne_tail_2cfc_cro_placed_at` (`VerNeTailEnv`) into
`OverVerNe1e04CliAtFrozenPlacedBody A lim OverPrevEncOK VerNeTightTopRawEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  libsignalFrozen_of_keepsFrozen lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym
  lsRustNoAllocShimSym lsRustReallocSym ls_hook_ok_ultra_of_mem lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (OverPrevEncOK)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (OverPrevEncOKAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (
  overDecScratchPost overDecScratchPre overDecStackX overPrevElemAt
  overPrevPeel_ok_ext overScratch pqLogLevelCellPlaced prevVecAt
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 instIsLsBlockProg_518 lsProg_518)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved decryptPrekeySavedRegsAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_shim
)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtFrozenPlacedBody
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3ExactPlacedBudget (
  c3x_chainMerge5ExactCroPlacedOkExt_cli
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudget (
  b518x_ChainMerge5ExactCroPlacedOkExt' b518x_OverPrevDecodeExactCroPlacedAt
  b518x_VerNeSessionCancelRawEnv b518x_overPrevDecode_exact_cro_placed_of_hooks_chain5'
  b518x_overPrevDecode_rawEnv_cro_placed_of_exact
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  overPrevElemAtBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlacedBudget (
  stageP3ErrPostPrevEmptyPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ErrK2PlacedBudget (
  overK2Seg_cli_placed_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (
  bind_sepWP_fr_frame_budget lscro_of_frozen overPrevErr_frozen_placed_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (
  VerNeS1Env overVerNe_1e04_to_1e78_frozen_placed_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudget (
  over_ver_ne_tail_2cfc_cro_placed_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (
  VerNeTailEnv bind_sepWP_cro_frame_tail bind_sepWPp_nopanic_tail weaken_frame_tail
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (
  decScratchPost_join_930_top_pl fits_seq_left fits_seq_right
  hookSat_noAllocShimBudget_of_rustAllocShimVm hookSat_verNeMemcpy_of_frameless
  loopScratch_to_decPre_top_pl mem920_16_fold_top_pl mem920_16_split_top_pl
  overDecScratchPre_eq_prevDec_pl overPrevElemAt_eq_exists_prevDecBudget_pl
  overPrevLoop_head_cli_placed_budget_wp overPrevMoves_cli_placed_budget_ok
  prevDecBudget_elemAt_entails_overPrevElemAt_pl prevDec_scratchPostBudget_eq_pl
  prevVecAt_open_eq_top_pl slot3e0_344_fold_top_pl stackAt_sub_eq_top_pl stack_bottom_join_top_pl
  verNeMemcpyStackSpec
)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (
  VerNeSessionCancelRawEnv VerNeTightTopRawEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget (
  cliDropSessionStructure4_placed_ok_at cliGrowOneSpe_518_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_realloc_budget_sat
  cliExternsPlaced_sessionMemmove_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec growOneSpeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf)

local elab "erase_hkdf_arm64_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_arm64_norm

/-! ## 1. `VerNeTightTopRawEnv` Loop Decomposition & `FitsEnv` Stepping -/

private abbrev rawbody_VerNeLoopRawEnv (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (VerNeSessionCancelRawEnv enc) FreeOnlyEvs

private theorem rawbody_verNeLoopRawEnv_of_parts {enc : List (BitVec 8)}
    {evs_dec evs_err : List AllocEvent}
    (hd : b518x_VerNeSessionCancelRawEnv enc evs_dec) (he : FreeOnlyEvs evs_err) :
    rawbody_VerNeLoopRawEnv enc (evs_dec ++ evs_err) :=
  Or.inr ⟨evs_dec, evs_err, rfl, hd, he⟩

private theorem rawbody_verNeTightTopRawEnv_of_parts {enc : List (BitVec 8)}
    {evs1 evs2 evs3 : List AllocEvent}
    (h1 : VerNeS1Env evs1) (h2 : rawbody_VerNeLoopRawEnv enc evs2) (h3 : VerNeTailEnv evs3) :
    VerNeTightTopRawEnv enc (evs1 ++ evs2 ++ evs3) := by
  rw [List.append_assoc]
  exact Or.inr ⟨evs1, evs2 ++ evs3, rfl, h1, Or.inr ⟨evs2, evs3, rfl, h2, h3⟩⟩

private theorem rawbody_fitsS1_of_fitsTop {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} (h : FitsEnv M lim st0 (VerNeTightTopRawEnv enc)) :
    FitsEnv M lim st0 VerNeS1Env :=
  fits_seq_left h

private theorem rawbody_fitsLoop_of_fitsTop {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} {evs1 : List AllocEvent}
    (h : FitsEnv M lim st0 (VerNeTightTopRawEnv enc)) (h1 : VerNeS1Env evs1) :
    FitsEnv M lim (M.stepEvents evs1 st0) (rawbody_VerNeLoopRawEnv enc) :=
  fits_seq_left (fits_seq_right h h1)

private theorem rawbody_fitsDec_of_fitsLoop {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} (h : FitsEnv M lim st0 (rawbody_VerNeLoopRawEnv enc)) :
    FitsEnv M lim st0 (b518x_VerNeSessionCancelRawEnv enc) :=
  fits_seq_left h

private theorem rawbody_fitsTail_of_fitsTop {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} {evs1 evs2 : List AllocEvent}
    (h : FitsEnv M lim st0 (VerNeTightTopRawEnv enc))
    (h1 : VerNeS1Env evs1) (h2 : rawbody_VerNeLoopRawEnv enc evs2) :
    FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st0)) VerNeTailEnv :=
  fits_seq_right (fits_seq_right h h1) h2

/-! ## 2. Block-`518` Exact `VerNeSessionCancelRawEnv` Loop (`+0x1e78 → +0x2cfc`) -/

private theorem rawbody_sepWPp_strengthen_frozen [LibsignalPlacement] {prog : Program}
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hwp : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P
      (fun sf P_f => Q sf P_f ∧ LibsignalFrozen lsmpl sf.mem) Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | hpan⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ,
      libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

set_option maxHeartbeats 600000 in
private theorem rawbody_overPrevDecode_cro_placed_of_exact [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    {ext : String → Option (State → State)}
    (hExact : b518x_OverPrevDecodeExactCroPlacedAt A lim ext)
    (st0 : M.σ) (s0 s : State) (prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (sess : Session (List (BitVec 8)))
    (henc : enc = CryptoVerification.E2E.Record.encSession sess)
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩)
    (hver4 : sess.state.sessionVersion = 4#32)
    (hpp : sess.pendingPreKey = none)
    (hkpk : sess.pendingKyberPreKey = none)
    (hfit : FitsEnv M lim st0 (b518x_VerNeSessionCancelRawEnv enc))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hCL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ee8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = s.sp + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64) (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 .x27 = prevPtr) (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overPrevElemAt A.repAlloc prevCap prevPtr enc ∗ overDecScratchPre s.sp ∗
       A.pool lim st0 s ∗ stackAt s.sp overDecStackX)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, b518x_VerNeSessionCancelRawEnv enc evs ∧
          (P_f ⊢
            prostSSGQAt A.repAlloc (s.sp + 0x930#64) (ssgqOf sess) ∗
            overDecScratchPost s.sp ∗ overPrevElemAt A.repAlloc prevCap prevPtr enc ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp overDecStackX)) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.sp + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x27 = prevPtr ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem)
      Qp := by
  conv =>
    arg 4
    rw [overPrevElemAt_eq_exists_prevDecBudget_pl, overDecScratchPre_eq_prevDec_pl]
    simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun encCap => SepWPp.exists_elim fun encPtr => ?_
  have hpre_eq :
      overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overDecScratchPre s.sp ∗
        A.pool lim st0 s ∗ stackAt s.sp overDecStackX =
      overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overDecScratchPre s.sp ∗
        stackAt s.sp CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overDecStackX ∗
        A.pool lim st0 s := by
    dsimp only [overDecStackX,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overDecStackX]
    sep_ac_rfl
  rw [hpre_eq]
  have hwp := b518x_overPrevDecode_rawEnv_cro_placed_of_exact hExact st0 s0 s
    prevCap prevPtr encCap encPtr enc sess ⟨henc, hQ, hver4, hpp, hkpk⟩ hfit
    hcro hCL hpc hrun hsp_align htr hx21 hx24 hx25 hx27 hx29
  intro R hm hL
  rcases hwp R hm hL with
    ⟨sf, hsteps,
     ⟨hpc', hrun', P_f, hmf, ⟨evs, hevs, hent_f⟩,
      hsp', htr', hcrof, hCLf, hx19', hx20', hx21', hx24', hx25', _hx26', hx27', hx29_c70,
      hvregs'⟩ |
     ⟨_, _, _, hfalse⟩ | ⟨_, hoom⟩⟩
  · have hent1 : P_f ⊢ anyHeap ∗
        (prostSSGQAt A.repAlloc (s.sp + 0x930#64) (ssgqOf sess) ∗
         overDecScratchPost s.sp ∗ overPrevElemAt A.repAlloc prevCap prevPtr enc ∗
         A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp overDecStackX) := by
      refine Entails.trans hent_f ?_
      rw [prevDec_scratchPostBudget_eq_pl]
      refine Entails.trans
        (sepConj_mono_left
          (prevDecBudget_elemAt_entails_overPrevElemAt_pl A prevCap prevPtr encCap encPtr enc)) ?_
      dsimp only [overDecStackX,
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overDecStackX]
      exact Entails.of_eq (by sep_ac_rfl)
    have hmf1 : sf.mem ⊨ anyHeap ∗
        ((prostSSGQAt A.repAlloc (s.sp + 0x930#64) (ssgqOf sess) ∗
          overDecScratchPost s.sp ∗ overPrevElemAt A.repAlloc prevCap prevPtr enc ∗
          A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp overDecStackX) ∗ R) := by
      have h0 := Satisfies.mono (sepConj_mono_left hent1) hmf
      rwa [sepConj_assoc] at h0
    exact ⟨sf, hsteps, Or.inl ⟨hpc', hrun',
      prostSSGQAt A.repAlloc (s.sp + 0x930#64) (ssgqOf sess) ∗
        overDecScratchPost s.sp ∗ overPrevElemAt A.repAlloc prevCap prevPtr enc ∗
        A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp overDecStackX,
      Satisfies.of_sep_right hmf1,
      ⟨evs, hevs, Entails.refl _⟩,
      hsp', htr', hx19', hx20', hx21', hx24', hx25', hx27',
      hx29_c70.trans hx29.symm, hvregs', hcrof, hCLf⟩⟩
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 800000 in
private theorem rawbody_overPrevLoop_part1_cro_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    {ext : String → Option (State → State)}
    (hExact : b518x_OverPrevDecodeExactCroPlacedAt A lim ext)
    (st0 : M.σ) (s0 s : State) (coroPtr prevCap prevPtr wd0 u3e0 : BitVec 64)
    (enc : List (BitVec 8)) (sess : Session (List (BitVec 8)))
    (hcap : prevCap ≠ 0#64)
    (henc : enc = CryptoVerification.E2E.Record.encSession sess)
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩)
    (hver4 : sess.state.sessionVersion = 4#32)
    (hpp : sess.pendingPreKey = none)
    (hkpk : sess.pendingKyberPreKey = none)
    (hfit : FitsEnv M lim st0 (b518x_VerNeSessionCancelRawEnv enc))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hCL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1e78#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗
       memRegion (s.sp + 0x538#64) 1016 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ memRegion (s.sp + 0x990#64) 256 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (s.sp + 0xbe8#64) 136 ∗
       A.pool lim st0 s ∗ stackAt s.sp overDecStackX)
      (fun s2 P_f =>
        (∃ evs_dec : List AllocEvent, b518x_VerNeSessionCancelRawEnv enc evs_dec ∧
          (P_f ⊢
            prostSSGQAt A.repAlloc (s.sp + 0x930#64) (ssgqOf sess) ∗ overDecScratchPost s.sp ∗
            memRegion (s.sp + 0x538#64) 40 ∗ memRegion (s.sp + 0x560#64) 320 ∗
            memRegion (s.sp + 0x6a0#64) 320 ∗ memRegion (s.sp + 0x7e0#64) 320 ∗
            prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
            ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            A.pool lim (M.stepEvents evs_dec st0) s2 ∗ stackAt s.sp overDecStackX)) ∧
        s2.sp = s.sp ∧ s2.trace = s0.trace ∧
        s2.readReg64 .x19 = coroPtr ∧ s2.readReg64 .x21 = s.sp + 0x930#64 ∧
        s2.readReg64 .x27 = prevPtr ∧ s2.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl s2.mem ∧ (lsProg_518 ext).CodeLoaded s2.mem)
      Qp := by
  refine weaken_frame_tail
    (Entails.of_eq (prevVecAt_open_eq_top_pl A.repAlloc coroPtr prevCap prevPtr enc hcap))
    (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (loopScratch_to_decPre_top_pl s.sp)) (by sep_focus) ?_
  refine bind_sepWP_cro_frame_tail hcro hCL
    (overPrevLoop_head_cli_placed_budget_wp A lim ext st0 s coroPtr prevCap prevPtr u3e0 wd0
      hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 hCL1
      ⟨hsp1, htr1, hx19_1, _, hx21_1, hx24_1, hx25_1, _, hx27_1, hx29_1, hvregs1⟩ => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  have htr1_0 : s1.trace = s0.trace := htr1.trans htr
  have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x930#64 := by rw [hx21_1, hsp1]
  have hx29_1' : s1.readReg64 .x29 = s1.sp + 0xc70#64 := by rw [hx29_1, hx29, hsp1]
  have hdec := rawbody_overPrevDecode_cro_placed_of_exact (Qp := fun _ _ => False)
    hExact st0 s0 s1 prevCap prevPtr enc sess
    henc hQ hver4 hpp hkpk hfit hcro1 hCL1 hpc1 hrun1 hsp1_align htr1_0
    hx21_1' hx24_1 hx25_1 hx27_1 hx29_1'
  rw [hsp1] at hdec
  refine bind_sepWPp_nopanic_tail hdec (by sep_focus)
    fun s2 P_m2 hpc2 hrun2
      ⟨⟨evs_dec, hevs_dec, hP2⟩,
       hsp2_1, htr2, hx19_2, _, hx21_2, _, _, hx27_2, hx29_2, hvregs_2_1, hcro2, hCL2⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP2) ?_
  refine weaken_frame_tail
    (Entails.of_eq (prevVecAt_open_eq_top_pl A.repAlloc coroPtr prevCap prevPtr enc hcap).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpc2 hrun2 ?_
  refine ⟨⟨evs_dec, hevs_dec, Entails.of_eq (by sep_ac_rfl)⟩,
    hsp2_1, htr2, hx19_2.trans hx19_1, hx21_2, hx27_2,
    hx29_2.trans (hx29_1.trans hx29), hvregs_2_1.trans hvregs1, hcro2, hCL2⟩

set_option maxHeartbeats 800000 in
private theorem rawbody_overPrevLoop_part2_frozen_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (verNeMemcpyStackSpec allocHookStack))
    (st0 : M.σ) (s0 s s2 : State) (coroPtr prevPtr errsPtr : BitVec 64)
    (msgVer : BitVec 32) (sess : Session (List (BitVec 8)))
    (hver_ne : msgVer ≠ 4#32)
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩)
    (hver4 : sess.state.sessionVersion = 4#32)
    (hkpk : sess.pendingKyberPreKey = none)
    (hfr2 : LibsignalFrozen lsmpl s2.mem)
    (hCL2 : (lsProg_518 ext).CodeLoaded s2.mem)
    (hpc2 : s2.pc = (blkPl_518).base + 0x2620#64) (hrun2 : s2.status = .Running)
    (hs2_sp : s2.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr2 : s2.trace = s0.trace)
    (hx19_2 : s2.readReg64 .x19 = coroPtr) (hx21_2 : s2.readReg64 .x21 = s.sp + 0x930#64)
    (hx27_2 : s2.readReg64 .x27 = prevPtr) (hx29_2 : s2.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s2
      (prostSSGQAt A.repAlloc (s.sp + 0x930#64) (ssgqOf sess) ∗ overDecScratchPost s.sp ∗
       memRegion (s.sp + 0x538#64) 40 ∗ memRegion (s.sp + 0x560#64) 320 ∗
       memRegion (s.sp + 0x6a0#64) 320 ∗ memRegion (s.sp + 0x7e0#64) 320 ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (errsPtr + 48#64) 144 ∗
       pqLogLevelCellPlaced ∗ A.pool lim st0 s2 ∗ stackAt s.sp overDecStackX)
      (fun sf P_f =>
        (∃ evs_err : List AllocEvent, FreeOnlyEvs evs_err ∧
          (P_f ⊢
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ memRegion (errsPtr + 60#64) 36 ∗
            memRegion (errsPtr + 96#64) 96 ∗ memRegion (s.sp + 0x538#64) 1016 ∗
            memRegion (s.sp + 0x930#64) 48 ∗ memRegion (s.sp + 0x960#64) 48 ∗
            memRegion (s.sp + 0x990#64) 256 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
            memRegion (s.sp + 0xbe8#64) 136 ∗ pqLogLevelCellPlaced ∗
            A.pool lim (M.stepEvents evs_err st0) sf ∗ stackAt s.sp overDecStackX)) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s2 ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem)
      Qp := by
  dsimp only [overDecScratchPost]
  refine weaken_frame_tail
    (overPrevPeel_ok_ext A.repAlloc sess hQ hver4 hkpk (s.sp + 0x930#64))
    (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun H => ?_
  refine SepWPp.pure_elim fun ⟨hw0, hr1, hr2, hdropFromMoves⟩ => ?_
  refine weaken_frame_tail (Entails.of_eq (mem920_16_split_top_pl s.sp)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u920 => ?_
  have hstk_alloc := stackAt_sub_eq_top_pl s.sp overDecStackX allocHookStack
  refine weaken_frame_tail (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
  have hx21_2' : s2.readReg64 .x21 = s2.sp + 0x930#64 := by rw [hx21_2, hs2_sp]
  have hmv := overPrevMoves_cli_placed_budget_ok A lim ext hmemcpy st0 s2 w0 w1 w2 u920 r1 r2
    hw0 hr1 hr2 hpc2 hrun2 hsp2_align hx21_2'
  rw [hs2_sp] at hmv
  refine bind_sepWP_fr_frame_budget hCL2 hfr2 hmv (by sep_focus)
    fun s3 hpc3 hrun3 hCL3 hfr3
      ⟨hsp3_2, htr3_2, hx8_3, hx19_3, _, hx27_3, hx29_3, hvregs3⟩ => ?_
  refine weaken_frame_tail (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine weaken_frame_tail (mem920_16_fold_top_pl s.sp (s2.readReg64 .x26)) (by sep_focus) ?_
  refine weaken_frame_tail hdropFromMoves (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun G => SepWPp.exists_elim fun st_prev => ?_
  refine SepWPp.pure_elim fun _ => ?_
  have hstk_grow := stackAt_sub_eq_top_pl s.sp overDecStackX growOneSpeStack
  refine weaken_frame_tail (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
  have htr3 : s3.trace = s0.trace := htr3_2.trans htr2
  have hx19_3' : s3.readReg64 .x19 = coroPtr := hx19_3.trans hx19_2
  have hx27_3' : s3.readReg64 .x27 = prevPtr := hx27_3.trans hx27_2
  have hx29_3' : s3.readReg64 .x29 = s.sp + 0xc70#64 := hx29_3.trans hx29_2
  have herr := overPrevErr_frozen_placed_at (Qp := fun _ _ => False)
    ext hDropSS3 st0 s0 s3 prevPtr errsPtr msgVer G st_prev
    hver_ne hfr3 hCL3 hpc3 hrun3 hsp3_align htr3 hx8_3 hx27_3'
  rw [hsp3] at herr
  refine bind_sepWPp_nopanic_tail herr (by sep_focus)
    fun sf P_mf hpcf hrunf ⟨hPf, hspf_3, htrf, hx19_f, _, hx29_f, hvregsf, hcrof, hCLf⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hPf) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_err => ?_
  refine weaken_frame_tail
    (T := ⌜FreeOnlyEvs evs_err⌝) (T' := ⌜FreeOnlyEvs evs_err⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hfree_err => ?_
  refine weaken_frame_tail (Entails.of_eq hstk_grow.symm) (by sep_focus) ?_
  have hfold_post :
      memRegion (s.sp + 0x920#64) 16 ∗ memRegion (s.sp + 0xa88#64) 8 ∗
      memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (s.sp + 0xbe8#64) 136 ∗
      memRegion (s.sp + 0x930#64) 344 = overDecScratchPre s.sp := by
    simpa only [overDecScratchPost, sepConj_assoc] using decScratchPost_join_930_top_pl s.sp
  refine weaken_frame_tail (Entails.of_eq hfold_post) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (loopScratch_to_decPre_top_pl s.sp).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨evs_err, hfree_err, Entails.of_eq (by sep_ac_rfl)⟩,
    hspf_3, htrf, hx19_f.trans hx19_3', hx29_f.trans hx29_3',
    hvregsf.trans hvregs3, hcrof, hCLf⟩

set_option maxHeartbeats 600000 in
private theorem rawbody_overPrevLoop_frozen_placed_at [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hExact : b518x_OverPrevDecodeExactCroPlacedAt A lim ext)
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (verNeMemcpyStackSpec allocHookStack))
    {enc : List (BitVec 8)}
    (st0 : M.σ) (hfit : FitsEnv M lim st0 (rawbody_VerNeLoopRawEnv enc))
    (s0 s : State) (coroPtr prevCap prevPtr errsPtr wd0 u3e0 : BitVec 64)
    (err0_w0 : BitVec 64) (msgVer : BitVec 32)
    (hcap : prevCap ≠ 0#64) (hver_ne : msgVer ≠ 4#32) (hEnc : OverPrevEncOK enc)
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hCL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1e78#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
      (prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗
       (errsPtr ↦₆₄ err0_w0) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗ memRegion (errsPtr + 48#64) 144 ∗
       memRegion (s.sp + 0x538#64) 1016 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ memRegion (s.sp + 0x990#64) 256 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (s.sp + 0xbe8#64) 136 ∗
       pqLogLevelCellPlaced ∗ A.pool lim st0 s ∗ stackAt s.sp overDecStackX)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, rawbody_VerNeLoopRawEnv enc evs ∧
          (P_f ⊢
            prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            (errsPtr ↦₆₄ err0_w0) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 12#64) 36 ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ memRegion (errsPtr + 60#64) 36 ∗
            memRegion (errsPtr + 96#64) 96 ∗ memRegion (s.sp + 0x538#64) 1016 ∗
            memRegion (s.sp + 0x930#64) 48 ∗ memRegion (s.sp + 0x960#64) 48 ∗
            memRegion (s.sp + 0x990#64) 256 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
            memRegion (s.sp + 0xbe8#64) 136 ∗ pqLogLevelCellPlaced ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp overDecStackX)) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem)
      Qp := by
  obtain ⟨sess, henc, hQ, hver4, hpp, hkpk⟩ := hEnc
  have hpart1 := rawbody_overPrevLoop_part1_cro_placed_ok (Qp := fun _ _ => False)
    hExact st0 s0 s coroPtr prevCap prevPtr wd0 u3e0 enc sess
    hcap henc hQ hver4 hpp hkpk (rawbody_fitsDec_of_fitsLoop hfit)
    (lscro_of_frozen hfr) hCL hpc hrun hsp_align htr hx19 hx29
  refine bind_sepWPp_nopanic_tail (rawbody_sepWPp_strengthen_frozen hfr hpart1) (by sep_focus)
    fun s2 P_m2 hpc2 hrun2
      ⟨⟨⟨evs_dec, hevs_dec, hP2⟩,
       hs2_sp, htr2, hx19_2, hx21_2, hx27_2, hx29_2, hvregs2, _hcro2, hCL2⟩, hfr2⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP2) ?_
  have hpart2 := rawbody_overPrevLoop_part2_frozen_placed_ok (Qp := fun _ _ => False)
    ext hDropSS3 hmemcpy
    (M.stepEvents evs_dec st0) s0 s s2 coroPtr prevPtr errsPtr msgVer sess
    hver_ne hQ hver4 hkpk hfr2 hCL2 hpc2 hrun2 hs2_sp hsp_align htr2
    hx19_2 hx21_2 hx27_2 hx29_2
  refine bind_sepWPp_nopanic_tail hpart2 (by sep_focus)
    fun sf P_mf hpcf hrunf
      ⟨⟨evs_err, hfree_err, hPf⟩, hspf, htrf, hx19f, hx29f, hvregsf, hcrof, hCLf⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨evs_dec ++ evs_err, rawbody_verNeLoopRawEnv_of_parts hevs_dec hfree_err, ?_⟩,
    hspf, htrf, hx19f, hx29f, hvregsf.trans hvregs2, hcrof, hCLf⟩
  rw [M.stepEvents_append]
  exact Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. Stage-P3/P4 `VerNeTightTopRawEnv` Composition (`+0x1e04 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 800000 in
private theorem rawbody_overVerNe_1e04_frozen_placed_at_cl [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (verNeMemcpyStackSpec allocHookStack))
    (hExact : b518x_OverPrevDecodeExactCroPlacedAt A lim ext)
    (st_init : M.σ) (s0 s s1 : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap : prevCap ≠ 0#64)
    (msgVer : BitVec 32) (hver_ne : msgVer ≠ 4#32)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)) (hEnc : OverPrevEncOK enc)
    (hfits : FitsEnv M lim st_init (VerNeTightTopRawEnv enc))
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hF1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st_init s1 ∗ stackAt s.sp rootStack)
      (fun sf P_f =>
        (∃ (wd0 : BitVec 64) (evs : List AllocEvent),
          VerNeTightTopRawEnv enc evs ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
            memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
            stageP3ErrPostPrevEmptyPlaced A lim (M.stepEvents evs st_init) s0 s sf coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed))) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      Qp := by
  have hstk_dec := stackAt_sub_eq_top_pl s.sp rootStack overDecStackX
  have hstk_grow := stackAt_sub_eq_top_pl s.sp overDecStackX growOneSpeStack
  refine weaken_frame_tail (Entails.of_eq hstk_dec) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have hs1 := overVerNe_1e04_to_1e78_frozen_placed_at (Qp := fun _ _ => False)
    ext hGrow hDropSS3 st_init (rawbody_fitsS1_of_fitsTop hfits)
    s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
    hfr1 hF1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1
  refine bind_sepWPp_nopanic_tail (rawbody_sepWPp_strengthen_frozen hfr1 hs1) (by sep_focus)
    fun s6b P_6b hpc6b hrun6b
      ⟨⟨⟨errsPtr, evs1, hevs1, hP6b⟩, hs6b_sp, htr6b, hx19_6b, hx29_6b, hvregs_6b, _hcro6b, hF6b⟩, hfr6b⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP6b) ?_
  refine weaken_frame_tail (Entails.of_eq hstk_grow.symm) (by sep_focus) ?_
  dsimp only [overScratch]
  have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hs6b_sp]; exact hsp_align
  have hx29_6b' : s6b.readReg64 .x29 = s6b.sp + 0xc70#64 := by rw [hx29_6b, hs6b_sp]
  have hloop := rawbody_overPrevLoop_frozen_placed_at (Qp := fun _ _ => False)
    ext hExact hDropSS3 hmemcpy
    (M.stepEvents evs1 st_init) (rawbody_fitsLoop_of_fitsTop hfits hevs1)
    s0 s6b coroPtr prevCap prevPtr errsPtr ud0
    0x8000000000000006#64 0x8000000000000006#64 msgVer hcap hver_ne hEnc
    hfr6b hF6b hpc6b hrun6b hsp6b_align htr6b hx19_6b hx29_6b'
  rw [hs6b_sp] at hloop
  refine bind_sepWPp_nopanic_tail hloop (by sep_focus)
    fun s7 P_7 hpc7 hrun7
      ⟨⟨evs2, hevs2, hP7⟩, hs7_sp, htr7, hx19_7, _, hvregs_7_6b, hcro7, hF7⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP7) ?_
  refine weaken_frame_tail (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have htail := over_ver_ne_tail_2cfc_cro_placed_at (Qp := fun _ _ => False)
    ext hshim halloc hdealloc hDropSS3
    (overK2Seg_cli_placed_at A lim ext hdealloc)
    (M.stepEvents evs2 (M.stepEvents evs1 st_init))
    (rawbody_fitsTail_of_fitsTop hfits hevs1 hevs2)
    s0 s s7 coroPtr ctxPtr outPtr errsPtr prevCap prevPtr msgVer msgVer b_2c0 enc recG st
    hcro7 hF7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7
  refine bind_sepWPp_nopanic_tail htail (by sep_focus)
    fun sf P_mf hpcf hrunf ⟨⟨evs3, hevs3, hPf⟩, hspf, htrf, hcc, hcrof, hFf, hvregs_f_7⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hPf) ?_
  refine weaken_frame_tail
    (slot3e0_344_fold_top_pl s.sp 0xffffffffffffffff#64) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (stack_bottom_join_top_pl s.sp)) (by sep_focus) ?_
  have herrs_ex :
      ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ⊢
      ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64
      (Entails.sepExists_right errsPtr (Entails.sepExists_right 2#64 (Entails.refl _)))
  refine weaken_frame_tail herrs_ex (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨prevPtr + 24#64, evs1 ++ evs2 ++ evs3,
      rawbody_verNeTightTopRawEnv_of_parts hevs1 hevs2 hevs3, ?_⟩,
    hspf, htrf, hcc, hcrof, hFf, hvregs_f_7.trans (hvregs_7_6b.trans hvregs_6b)⟩
  dsimp only [stageP3ErrPostPrevEmptyPlaced, overScratch, SessionState.recordError]
  rw [M.stepEvents_append (evs1 ++ evs2) evs3 st_init, M.stepEvents_append evs1 evs2 st_init]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 4. Hook Discharge & Closed `cliVerNe1e04_full_placed_ok_raw` -/

private theorem rawbody_sepWPp_weaken_post_false {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun _ _ => False))
    (himp : ∀ sf P_f, Q sf P_f → Q' sf P_f) :
    SepWPp prog ret s P Q' (fun _ _ => False) := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | ⟨_, _, _, hf⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, himp sf P_f hQ⟩⟩
  · exact hf.elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem rawbody_hookNoop_rustAllocShimVm_hookOk :
    HookOk hookNoop rustAllocShimVmSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  dsimp only [rustAllocShimVmSpec, hookNoop, retHook, id_eq] at hpre ⊢
  rw [emp_sepConj] at hpre
  rw [satisfies_pure_sepConj]
  exact ⟨⟨⟨by cases s0; rfl, by cases s0; rfl, by cases s0; rfl, by cases s0; rfl,
    by cases s0; rfl, by cases s0; rfl, by cases s0; rfl⟩,
    ⟨⟨by cases s0; rfl, by cases s0; rfl, by cases s0; rfl⟩,
     by cases s0; rfl, fun _ => by cases s0; rfl, fun _ _ _ => by cases s0; rfl⟩⟩, hpre⟩

private theorem rawbody_cli_rustAllocShimVm_sat (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (hShim : gh.shim = hookNoop) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      rustAllocShimVmSpec :=
  (show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
    ⟨hookNoop, (cliGhostExterns_shim gh (cliExternsPlaced mmpl W)).trans (congrArg some hShim),
      rawbody_hookNoop_rustAllocShimVm_hookOk⟩

private theorem rawbody_cli_framelessMemcpy_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (hG : CliGhostAllocHooks M A lim gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMemcpySym
      framelessMemcpyBudgetSpec := by
  rcases cliExternsPlaced_framelessMemcpy_budget_sat mmpl gh W hG with ⟨f, hf, hok⟩
  refine (show ("memcpy" : String) = lsMemcpySym by decide) ▸ ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

/-- Discharges `OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK VerNeTightTopRawEnv ext`
from its callee contracts, `HookSat`, and `b518x_ChainMerge5ExactCroPlacedOkExt'`. -/
theorem overVerNe1e04CliAtFrozenPlacedBody_raw_of_hooks_chain5 [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hEncImp : ∀ enc, PrevEncOK enc → OverPrevEncOK enc)
    (ext : LibsignalHooks)
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hshim_sat : HookSat ext lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc_sat : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hmemmove_sat : HookSat ext "memmove" (sessionMemmoveBudgetSpec extHookStack))
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked)
    (hChain5 : b518x_ChainMerge5ExactCroPlacedOkExt' A lim ext) :
    OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK VerNeTightTopRawEnv ext :=
  OverVerNe1e04CliAtFrozenPlacedBody.mono_prevEncOK hEncImp
    (fun st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
        hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
        _hver4 _hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
        hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 =>
      fun R hm hF1 =>
        rawbody_sepWPp_weaken_post_false
          (rawbody_overVerNe_1e04_frozen_placed_at_cl ext hGrow hDropSS3
            (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518) hshim_sat)
            (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518) halloc_sat)
            (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518) hdealloc_sat)
            (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518)
              (hookSat_verNeMemcpy_of_frameless allocHookStack hmc_sat))
            (b518x_overPrevDecode_exact_cro_placed_of_hooks_chain5'
              (hookSat_noAllocShimBudget_of_rustAllocShimVm hshim_sat)
              halloc_sat hrealloc_sat hdealloc_sat hmc_sat hmemmove_sat hpanic_raw hChain5)
            st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
            hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
            hfr1 hF1 hpc1 hrun1 hs1_sp hsp_align htr1
            hx9_1 hx19_1 hx24_1 hx27_1 hx29_1)
          (fun _ _ ⟨hpost, hsp, htr, hcc, hcro, _, hvregs⟩ =>
            ⟨hpost, hsp, htr, hcc, hcro, hvregs⟩)
          R hm hF1)

/-- Discharges `OverVerNe1e04CliAtFrozenPlacedBody` at `VerNeTightTopRawEnv` on
`cliGhostExterns gh (cliExternsPlaced mmpl W)` under `[LibsignalFullPlacement]`. -/
theorem cliVerNe1e04_full_placed_ok_raw [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    OverVerNe1e04CliAtFrozenPlacedBody A lim OverPrevEncOK VerNeTightTopRawEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  overVerNe1e04CliAtFrozenPlacedBody_raw_of_hooks_chain5 (fun _ h => h)
    (cliGhostExterns gh (cliExternsPlaced mmpl W))
    (cliGrowOneSpe_518_placed_ok mmpl gh W hG)
    (cliDropSessionStructure4_placed_ok_at
      (callerProg := lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (i := 518) mmpl gh W hG (by decide))
    (rawbody_cli_rustAllocShimVm_sat mmpl gh W hG.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
    (rawbody_cli_framelessMemcpy_sat mmpl gh W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack))
    (cliGhostExterns_panic_handle_error mmpl gh W)
    (c3x_chainMerge5ExactCroPlacedOkExt_cli mmpl gh W hG)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget
