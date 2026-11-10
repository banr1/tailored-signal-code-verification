/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTight
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `{A}`-Generic Block-`427` (`spqr::send::<Coins>`) Guarded-Tight Seam (`ElfSlicesPqOomH2KSlot464Send`)

**Checked by Lean.**

Generalizes the Block-`427` (`spqr::send::<Coins>`) producer at `w1t_SendGuardedEnv W.C.F W.Q.K`
to an arbitrary `A : RustCliAllocBudget M` (such as `AllocWithFds.withFds A0`), taking `hHmac`
directly as a parameter.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464Send

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib ls_blockPlacement_base lsmpl)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (ls_subroutine_ok_of_blockProgram_cro spqrCoinsAfterPlaced spqrCoinsAtPlaced
   statesFromPbJumpTablePlacedAt)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalSpqrV1
  (MlKem States spqrAuthApi spqrDecodeState spqrHkdfWith spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded SendCall keys_ls_subroutine_ok_of_block_cro withLsCodeRoLoaded)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SpqrV1.Alloc (spqrMemmoveSym)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.States.FromPb
  (resultChunkedStatesAt statesFromPbStackX v1StatePtsBound)
open CryptoVerification.SpqrV1.States.Leaves
  (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv)
open CryptoVerification.SpqrV1.Top.DecodeState
  (canonicalV1InnerHeap decodeStateResultAt decodeStateStackX
   optProtoInnerStateAt_canonical_eq_drop)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
  (drop_chain_epoch_slice_local1_placed_ok_x drop_proto_spqr_chain_placed_ok_x
   ls_subroutine_ok_of_blockProgram_plain)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (CoinsFillPlacedOkX SpqrSendPlacedContractsOfEnv spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (decodeStatePlacedSpecXOfEnv spqrSendCoinsPlacedSpecOfEnv spqrSendCoinsPlacedSpecTOfEnv
   statesFromPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_DecodeStateGuardedEnv tlb_DecodeStateTightEnv
   tlb_decodeStateGuardedEnv_sub_tight_of_spqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (SpqrStateTight640)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
  (cliSpqrSend_chainFromPb_ok cliSpqrSend_chainFromVn_ok cliSpqrSend_chainIntoPb_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliAuthMacHdr_placed_ok cliAuthUpdate_placed_ok cliChainAddEpoch_placed_ok
   cliChainSendKey_placed_ok cliEncodeBytesPlacedOkX cliEncodeVarint_placed_ok
   cliExternsPlaced_sessionMemmove_allocVm_sat cliHkdfToVec_placed_ok cliPolyNextChunkPlacedOkX
   cliRecvCt2PlacedAllocExt cliSpqrSendAllocContractsPlaced cliSpqrSend_coinsFill_ok_cli
   cliStatesPlacedSeams spqrSendExtraContractsPlaced_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget
  (cliStatesIntoPb_sendCoins_exact_ok)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTight
  (w1t_DecGuardedBytes w1t_SendGuardedEnv w1t_SendTightBytesEnv
   w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv
   w1t_s427_cliSpqrSend_messageSerialize_exact_on w1t_s427_not_fitsEnv_of_univ
   w1t_s427_spqrSendCoins_placed_ok_of_contracts_tight)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (chainSendKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedTightBudgetR
  (e2b_StatesFromPbExactEnv e2b_statesFromPbExactEnv_sub_tight
   e2b_statesFromPbTightDom_of_spqrStateTight640 e2b_states_from_pb_ok_x_placed_exact)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStatePlacedOkOfEnv spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget (MessageSerializeEnv)

private theorem seqEnv_mono_left
    {P P' Q : List AllocEvent → Prop} {evs : List AllocEvent}
    (hP : ∀ e, P e → P' e) (h : SeqEnv P Q evs) :
    SeqEnv P' Q evs :=
  h.imp (hP evs) fun ⟨e1, e2, heq, h1, h2⟩ => ⟨e1, e2, heq, hP e1 h1, h2⟩

private theorem hExt_withPanics_id
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym _
  exact congrFun (withPanics_cliGhostExterns mmpl gh W) sym

private theorem cliGhostExterns_isPanic
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
  intro sym hsym
  have h := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at h
  exact h.symm

private theorem cliSpqrSend_chainAddEpoch_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 368)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainAddEpoch_placed_ok mmpl gh W hA (hExt_withPanics_id mmpl gh W)))

private theorem cliSpqrSend_chainSendKey_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 367)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainSendKey_placed_ok mmpl gh W hA (hExt_withPanics_id mmpl gh W)))

private theorem cliSpqrSend_coinsFill_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    CoinsFillPlacedOkX (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  ls_subroutine_ok_of_blockProgram_plain (cliSpqrSend_coinsFill_ok_cli mmpl gh W hA)

private theorem cliSpqrSend_encodeVarint_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliEncodeVarint_placed_ok mmpl gh W hA (fun _ _ => rfl))

private theorem hookSat_allocMemcpyVm_of_framelessAcp
    {hooks : String → Option (State → State)} {name : String}
    (h : HookSat hooks name
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec) :
    HookSat hooks name LibsignalBinary.Heap.allocMemcpyVmSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  have hx2 : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre' : s0.mem ⊨
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec.pre
        (dst, src, bs) s0 ∗ R := by
    dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hsat (dst, src, bs) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

private theorem cliSpqrSend_decodeState_guarded_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h325 : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv canonicalV1InnerHeap M A lim
          (fun g => w1t_DecGuardedBytes W.C.F W.Q.K g.st.bytes))) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hblk : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics H))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := by
    have h0 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics H))
        (blkPl_325).base
        (withLsCodeRoLoaded lsmpl
          (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := h325
    rwa [IsLsBlockProg.eq_blockProgram
          (prog := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics H)),
        ls_blockPlacement_base (i := 325)] at h0
  have hok : subroutine_ok (spqrSendPlacedProg H) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) :=
    ls_subroutine_ok_of_blockProgram_cro hblk
  exact subroutine_ok_mono hok
    (fun (g, stB) R s0 hpre => by
      dsimp only [withLsCodeRoLoaded, spqrDecodeStatePlacedSpecOfEnv,
        decodeStatePlacedSpecXOfEnv] at hpre ⊢
      have hpre' : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.outPtr ∧ s0.readReg64 .x0 = g.st.v ∧
            g.st.bytes.length < 2 ^ 32 ∧
            FitsEnv M lim stB (w1t_DecGuardedBytes W.C.F W.Q.K g.st.bytes)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗ memRegion g.outPtr 352 ∗
              A.pool lim stB s0 ∗ stackAt s0.sp decodeStateStackX ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      rw [satisfies_pure_sepConj] at hpre'
      rcases hpre' with ⟨⟨hx8, hx0, hlen, hfit⟩, hrest⟩
      have hgoal : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.outPtr ∧ s0.readReg64 .x0 = g.st.v ∧
            g.st.bytes.length < 2 ^ 32 ∧
            FitsEnv M lim stB (tlb_DecodeStateGuardedEnv W.C.F W.Q.K g)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗ memRegion g.outPtr 352 ∗
              A.pool lim stB s0 ∗ stackAt s0.sp decodeStateStackX ∗ R)) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx8, hx0, hlen, hfit⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun (g, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded, spqrDecodeStatePlacedSpecOfEnv,
        decodeStatePlacedSpecXOfEnv] at hpost ⊢
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ tlb_DecodeStateGuardedEnv W.C.F W.Q.K g evs⌝ ∗
          (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗
            decodeStateResultAt canonicalV1InnerHeap A.repAlloc g.outPtr
              (spqrDecodeState g.st.bytes) ∗
            A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp decodeStateStackX ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨⟨htr, hevs⟩, hrest⟩
      have hgoal : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ w1t_DecGuardedBytes W.C.F W.Q.K g.st.bytes evs⌝ ∗
          (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗
            decodeStateResultAt canonicalV1InnerHeap A.repAlloc g.outPtr
              (spqrDecodeState g.st.bytes) ∗
            A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp decodeStateStackX ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨htr, hevs⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun _ _ _ _ hp => hp)

private theorem cliSpqrSend_statesFromPb_exact_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (statesFromPbPlacedSpecXOfEnv M A lim W.C.F
          (fun g => e2b_StatesFromPbExactEnv W.C.F g.pb))) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hRecv := cliRecvCt2PlacedAllocExt mmpl gh W hA (fun _ _ => rfl)
  have hFromPbHooks : FromPbAllocHooksBudget M A lim H :=
    {
      panic_ok := hRecv.handleError
      shim := hRecv.shim
      alloc := hRecv.alloc
      dealloc := hRecv.dealloc
      memcpy := hookSat_allocMemcpyVm_of_framelessAcp hRecv.memcpy
    }
  have hmemmove0 : HookSat (Rust.withPanics H) spqrMemmoveSym
      (withAllocVmPreserved (CryptoVerification.LibsignalTripleRatchet.sessionMemmoveSpec 0)) :=
    hookSat_of_eq (hExt_withPanics_id mmpl gh W _ (by decide))
      (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W)
  have hok333 := e2b_states_from_pb_ok_x_placed_exact (F := W.C.F) hFromPbHooks hmemmove0
  have hok : subroutine_ok (spqrSendPlacedProg H) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesFromPbPlacedSpecXOfEnv
          M A lim W.C.F (e2b_StatesFromPbExactEnv W.C.F))) :=
    ls_subroutine_ok_of_blockProgram_cro hok333
  have hjt_eq :
      CryptoVerification.SpqrV1.States.FromPb.statesFromPbJumpTablePlacedAt =
        statesFromPbJumpTablePlacedAt := rfl
  exact subroutine_ok_mono hok
    (fun (g, stB) R s0 hpre => by
      dsimp only [withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesFromPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv,
        statesFromPbPlacedSpecXOfEnv] at hpre ⊢
      rw [hjt_eq]
      have hpre' : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.out ∧ s0.readReg64 .x0 = g.pbA ∧
            v1StatePtsBound g.pb ∧
            FitsEnv M lim stB (e2b_StatesFromPbExactEnv W.C.F g.pb)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (memRegion g.out chunkedStatesSize ∗
              optProtoInnerStateAt A.repAlloc g.pbA g.pb.innerState ∗
              statesFromPbJumpTablePlacedAt ∗ A.pool lim stB s0 ∗
              stackAt s0.sp statesFromPbStackX ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre')
    (fun (g, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesFromPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv,
        statesFromPbPlacedSpecXOfEnv] at hpost ⊢
      rw [hjt_eq] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ e2b_StatesFromPbExactEnv W.C.F g.pb evs⌝ ∗
          (resultChunkedStatesAt A.repAlloc (F := W.C.F) g.out
              (States.from_pb spqrPolyApi (spqrAuthApi W.C.F) g.pb) ∗
            memRegion g.pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs stB) sf ∗
            stackAt s0.sp statesFromPbStackX ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost')
    (fun _ _ _ _ hp => hp)

private theorem spqrSendPlacedContracts_tight_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h325 : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrSendPlacedContractsOfEnv M canonicalV1InnerHeap A lim 0#64 W.C W.Q.K
      (fun g => w1t_DecGuardedBytes W.C.F W.Q.K g.st.bytes)
      (fun g => e2b_StatesFromPbExactEnv W.C.F g.pb)
      StatesIntoPbExactEnv
      (MessageSerializeEnv spqrPolyApi)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget.PolyNextChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.HeaderSentSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1ReceivedSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.EkReceivedCt1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct2SampledSendCt2ChunkEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hAlloc := cliSpqrSendAllocContractsPlaced mmpl gh W hA.toCliGhostAllocHooks
  have hS := cliStatesPlacedSeams mmpl gh W hA hHmac
  exact
    {
      h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A.repAlloc
      alloc := hAlloc
      coinsFill_ok := cliSpqrSend_coinsFill_on mmpl gh W hA.toCliGhostAllocHooks
      decodeState_ok := cliSpqrSend_decodeState_guarded_on mmpl gh W h325
      statesFromPb_ok := cliSpqrSend_statesFromPb_exact_on mmpl gh W hA
      statesIntoPb_ok := cliStatesIntoPb_sendCoins_exact_ok mmpl gh W hA.toCliGhostAllocHooks
      chainFromPb_ok := cliSpqrSend_chainFromPb_ok mmpl gh W hA.toCliGhostAllocHooks
      chainFromVn_ok := cliSpqrSend_chainFromVn_ok mmpl gh W hA.toCliGhostAllocHooks
      chainAddEpoch_ok := cliSpqrSend_chainAddEpoch_on mmpl gh W hA.toCliGhostAllocHooks
      chainSendKey_ok := cliSpqrSend_chainSendKey_on mmpl gh W hA.toCliGhostAllocHooks
      chainIntoPb_ok := cliSpqrSend_chainIntoPb_ok mmpl gh W hA.toCliGhostAllocHooks
      messageSerialize_ok := w1t_s427_cliSpqrSend_messageSerialize_exact_on mmpl gh W hA
      encodeVarint_ok := cliSpqrSend_encodeVarint_on mmpl gh W hA
      authMacHdr_ok := cliAuthMacHdr_placed_ok mmpl gh W hA hHmac
      authUpdate_ok := cliAuthUpdate_placed_ok mmpl gh W hA
      hkdfToVec_ok := cliHkdfToVec_placed_ok mmpl gh W hA
      encodeBytes_ok := cliEncodeBytesPlacedOkX mmpl gh W hA.toCliGhostAllocHooks
      polyNextChunk_ok := cliPolyNextChunkPlacedOkX mmpl gh W hA.toCliGhostAllocHooks
      headerSentSendEkChunk_ok := hS.headerSentSendEkChunk_on
      ct1ReceivedSendEkChunk_ok := hS.ct1ReceivedSendEkChunk_on
      ct1SampledSendCt1Chunk_ok := hS.ct1SampledSendCt1Chunk_on
      ekReceivedCt1SampledSendCt1Chunk_ok := hS.ekReceivedCt1SampledSendCt1Chunk_on
      ct2SampledSendCt2Chunk_ok := hS.ct2SampledSendCt2Chunk_on
      dropProtoChain_ok := drop_proto_spqr_chain_placed_ok_x hAlloc
      dropChainEpochSlice_ok := drop_chain_epoch_slice_local1_placed_ok_x hAlloc
    }

private theorem sendOfDecodeFromPb_sub_tight
    {F : ShaCompress} {K : MlKem} {x : SendCall} {evs : List AllocEvent}
    (hG : SpqrStateTight640 F K x.st.bytes)
    (hevs : w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv F K
      (w1t_DecGuardedBytes F K) (e2b_StatesFromPbExactEnv F) x evs) :
    w1t_SendTightBytesEnv F K x.st.bytes x.rest evs := by
  have hDec : ∀ e, w1t_DecGuardedBytes F K x.st.bytes e → tlb_DecodeStateTightEnv e :=
    fun _ he => tlb_decodeStateGuardedEnv_sub_tight_of_spqrStateTight640 hG he
  have hFromPb : ∀ pq v1 e,
      spqrDecodeState x.st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      e2b_StatesFromPbExactEnv F v1 e → StatesFromPbTightEnv e :=
    fun _ _ _ hdec hinner he =>
      e2b_statesFromPbExactEnv_sub_tight
        (e2b_statesFromPbTightDom_of_spqrStateTight640 hG hdec hinner) he
  dsimp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_SendTightBytesEnv,
    w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv] at hevs ⊢
  cases hdec : spqrDecodeState x.st.bytes with
  | error _ =>
    rw [hdec] at hevs
    exact hDec evs hevs
  | ok pq =>
    rw [hdec] at hevs
    dsimp only at hevs ⊢
    cases hinner : pq.inner with
    | none =>
      rw [hinner] at hevs
      exact seqEnv_mono_left hDec hevs
    | some inner =>
      cases inner with
      | v1 v1 =>
        rw [hinner] at hevs
        dsimp only at hevs ⊢
        rcases hevs with h1 | ⟨e1, e2, rfl, h1, h2⟩
        · exact Or.inl (hDec evs h1)
        · refine SeqEnv.append (hDec e1 h1) ?_
          cases hfpb : States.from_pb spqrPolyApi (spqrAuthApi F) v1 with
          | error err =>
            cases err with
            | panic _ =>
              rw [hfpb] at h2
              exact hFromPb pq v1 e2 hdec hinner h2
            | err _ =>
              rw [hfpb] at h2
              exact seqEnv_mono_left (hFromPb pq v1 · hdec hinner) h2
          | ok st_states =>
            rw [hfpb] at h2
            exact seqEnv_mono_left (hFromPb pq v1 · hdec hinner) h2

/-- `{M} {A}`-generic Block-`427` (`spqr::send::<Coins>`) producer at
`w1t_SendGuardedEnv W.C.F W.Q.K`. -/
theorem spqrSendCoins_placed_ok_guarded_of_decodeState_at [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hGSpqr : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (h325 : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv
          M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_SendGuardedEnv W.C.F W.Q.K))) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hraw := w1t_s427_spqrSendCoins_placed_ok_of_contracts_tight
    (cliSpqrSendAllocContractsPlaced mmpl gh W hGSpqr.toCliGhostAllocHooks)
    (spqrSendPlacedContracts_tight_cli mmpl gh W h325 hGSpqr hHmac)
    (spqrSendExtraContractsPlaced_of_cli mmpl gh W hGSpqr hHmac)
  have hblk_wp : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 427 (Rust.withPanics H))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K
            (w1t_DecGuardedBytes W.C.F W.Q.K) (e2b_StatesFromPbExactEnv W.C.F)))) := by
    rwa [← IsLsBlockProg.eq_blockProgram (prog := spqrSendPlacedProg H)]
  have hwp_eq : Rust.withPanics H = H := by
    funext sym; unfold Rust.withPanics; split
    · next hp => exact (cliGhostExterns_isPanic mmpl gh W sym hp).symm
    · rfl
  have hblk_ext : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 427 H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K
            (w1t_DecGuardedBytes W.C.F W.Q.K) (e2b_StatesFromPbExactEnv W.C.F)))) := by
    simpa only [hwp_eq] using hblk_wp
  have hok0 : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K
            (w1t_DecGuardedBytes W.C.F W.Q.K) (e2b_StatesFromPbExactEnv W.C.F)))) :=
    ls_subroutine_ok_of_blockProgram_cro
      (callerProg := (blkPC_427).rebase (blkPl_427).base H) hblk_ext (by decide)
  have heq_cro (m : Memory) :
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl m =
        LibsignalCodeRoLoaded lsmpl m :=
    propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  have hmod : pqxdhSpqrModel ⟨W.C, W.Q⟩ = spqrV1 W.C.F W.Q.K := rfl
  rw [hmod]
  have hcoinsAt : spqrCoinsAtPlaced = cliTapeAt := rfl
  have hcoinsAfter : spqrCoinsAfterPlaced = cliTapeAfter := rfl
  exact subroutine_ok_mono hok0
    (fun (sc, stB) _ s hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded, spqrSendCoinsPlacedSpecTOfEnv, spqrSendCoinsPlacedSpecOfEnv]
        at hpre ⊢
      rw [heq_cro s.mem] at hpre
      rw [hcoinsAt]
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left ?_
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, h2, hfit⟩ => by
        by_cases hG : SpqrStateTight640 W.C.F W.Q.K sc.st.bytes
        · exact ⟨h1, h2, hfit.mono fun evs hevs =>
            fun _ => sendOfDecodeFromPb_sub_tight hG hevs⟩
        · exact False.elim
            (w1t_s427_not_fitsEnv_of_univ (fun _ hp => False.elim (hG hp)) hfit))
    (fun (sc, stB) _ _ _ hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded, spqrSendCoinsPlacedSpecTOfEnv, spqrSendCoinsPlacedSpecOfEnv]
        at hpost ⊢
      rw [hcoinsAfter] at hpost
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine Entails.sepExists_mono fun evs => ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨hd, htr, hnp, hevs⟩ =>
        ⟨fun hG => sendOfDecodeFromPb_sub_tight hG hevs, hd, htr, hnp⟩)
    (fun _ _ _ _ hp => hp)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464Send
