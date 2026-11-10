/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Relocatable Arm `R0` Proof

Defines the Arm `R0` allocation-event envelope `PreEnv` and proves `run_hop_pre_placed_ok` and
`run_hop_pre_of_slots_placed_ok` on Block `579` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost noneCap okTagVec protocolAddressAt speAt speWord uuidTryParse vecResultAt)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.SignalSession.Cli (DirGetGhost StoresGhost dirAt getResultAt pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV LsCodeInv RunCall addrParse callAt cliIo cliWrOk coinsInstalledPlaced
   fromUtf8AsciiSpec inputOf ownedBytes runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtRunEntryPlaced Bytes InRunPlaced MeAtDispatch PanicK RunHistOk RunNeeds
   RunSem addrNameHeap addrUpperAt dispatchCells dispatchMeHeap protocolAddressAt_eq_parts
   rejectMem runFiles runFsp runLocalBytes runLocals runOom runPcPlaced_eq runPcPlaced_zero
   runProgPlaced runSaved
   stackAt_run_split)
open CryptoVerification.SignalSession.Cli.RunDrop (speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   SeqEnv rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (AddressEnv addressEvents addressSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
  (AllocContractsFsPlaced.dealloc_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget
  (RunHopPrePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAux
  (r0_addrSym_rp r0_addrUpperAt_close_rp r0_addrUpperAt_open_rp r0_apply_head_rp
   r0_callAt_peek_w0_rp r0_call_lscro_steps_rp r0_call_rocl_steps_rp r0_constFrame_rp
   r0_decResultOk_eq_words_rp r0_files_eq_of_trace_eq_rp r0_four_words_entails_32_rp
   r0_frame3_rejoin_rp r0_frame3_rejoin_some_rp r0_frame3_split_rp r0_frame_seq_rp r0_gaps_rp
   r0_meRegs_rp r0_memRegion_8_24_rp r0_memRegion_saved_open_rp r0_memRegion_two_words_rp
   r0_ownSem_rp r0_own_wrOk_rp r0_ownedBytes_free_rp r0_ownedBytes_split_rp r0_ownedRest_rp
   r0_probes_rejoin_rp r0_probes_split_rp r0_sepWPp_drop_left_rp r0_sepWPp_exists_all_rp
   r0_sepWPp_exists_left_rp r0_sepWPp_intro_address_rp r0_sepWPp_pure_left_rp r0_spAligned_rp
   r0_speInvalidState_eq_words_rp r0_step_dealloc_pre_rp r0_step_dispatch_tail_rp
   r0_step_err_pre_drop_rp r0_step_ok_pre_addr_rp r0_step_ok_pre_utf8_rp
   r0_step_post_none_nz_rp r0_step_post_none_zero_rp r0_step_post_some_nz_rp
   r0_step_post_some_zero_rp r0_step_prologue_rp r0_storesAt_eq_rp r0_storesRest_rp
   r0_subStack_split_rp r0_three_words_entails_24_rp r0_utf8_address_rp)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (callAt_atState dispatchMemPlaced runEntryMemPlaced runNeed_bounds_placed storesAt_opened_atState)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock dropSpeOwnedSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced fromUtf8_placed_ok runAddress_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget (dropSpeOwnedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (dirGetSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

/-! ## Allocation-Event Envelopes (`PreAfterGetEnv`, `PreEnv`) -/

/-- Post-`Dir::get("address")` allocation-event envelope of Arm `R0` (`FreeOnlyEvs` on `Err`, or `addressEvents uuidTryParse ownB` plus optional buffer deallocation on `Ok`). -/
def PreAfterGetEnv (g : RunCall) (evs : List AllocEvent) : Prop :=
  match StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") with
  | .error () => FreeOnlyEvs evs
  | .ok ownB => SeqEnv (· = addressEvents uuidTryParse ownB) FreeOnlyEvs evs

/-- Full Arm `R0` allocation-event envelope from `AtRunEntryPlaced` (`R+0x0`) to `AtDispatchPlaced` (`R+0x214`) or `AtRejectPlaced` (`R+0x124`). -/
def PreEnv (cEnvs : RunCalleesEnvs) (g : RunCall) (evs : List AllocEvent) : Prop :=
  SeqEnv (cEnvs.dirGet (runFiles g.i) StoresGhost.opened.identity.own (utf8 "address"))
    (PreAfterGetEnv g) evs

/-! ## Post-Address and Dispatch Composition Lemmas -/

private theorem r0_dispatch_tail_rp [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {S : RunSem} {g : RunCall} {me : MeAtDispatch}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (he : AtRunEntryPlaced CodeOk S g s0) (hbase : InRunPlaced CodeOk s0 s 0x1f8)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx23 : s.readReg64 (.gpr 23#5) = g.inp)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call) (hmeRegs : r0_meRegs_rp me s)
    (hownSem : r0_ownSem_rp g me)
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hnext : ∀ (s' : State) (me' : MeAtDispatch), AtDispatchPlaced CodeOk g me' s0 s' →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (dispatchMemPlaced A lim st g me' s0 s' resStack) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur
  have hpeek := r0_callAt_peek_w0_rp he A.repAlloc
  dsimp only [dispatchMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced]
  refine SepWPp.weaken_pre (Entails.trans (sepConj_mono_right (sepConj_mono_left hpeek))
    (Entails.of_eq (by simp only [sepExists_sepConj_left, sepExists_sepConj_right]; sep_ac_rfl))) ?_
  apply r0_sepWPp_exists_all_rp; intro w; apply r0_sepWPp_pure_left_rp; intro htag
  let callRest : SepProp :=
    ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗
      ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6) ∗
      CryptoVerification.SignalSession.Cli.MainHops.callHeap A.repAlloc w g.c
  let dispRest : SepProp :=
    memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
      CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      lsLogOff ∗
      dispatchMeHeap A.repAlloc me ∗ runSaved s0 ∗
      runLocals (runFsp s0) (dispatchCells (runFsp s0) me) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s
  refine r0_frame_seq_rp hbase.inv (F := callRest ∗ dispRest)
    (Entails.of_eq (by dsimp only [callRest, dispRest, RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]; sep_ac_rfl))
    (r0_step_dispatch_tail_rp (A := A) (lim := lim) (st := st)
      hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx25 htag) ?_
  rintro s1 hinv1 hpc1 hrun1
    ⟨hsp1, hfp1, hv1, htr1, hfs1, hpool1, hx8_1, hx19_1, hx20_1, hx21_1,
     hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
  have hpack : (g.call ↦₆₄ w.w0) ∗ (callRest ∗ dispRest) ⊢
      dispatchMemPlaced A lim st g me s0 s1 resStack := by
    dsimp only [dispatchMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
      callAt, callRest, dispRest, RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
    rw [hpool1]
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right w (Entails.refl _))))
  refine SepWPp.weaken_pre hpack (hnext s1 me ?_); clear hpack callRest dispRest
  rcases hownSem with ⟨ownB, hget_o, hp_o⟩
  exact { base := ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩,
          x8 := hx8_1, x19 := hx19_1.trans hx19, x20 := hx20_1.trans hx20,
          x23 := hx23_1.trans hx23, x24 := hx24_1.trans hx24, x25 := hx25_1,
          x26 := hx26_1, x27 := hx27_1,
          meRegs := by
            clear hp_o; dsimp only [r0_meRegs_rp] at hmeRegs
            cases me with
            | none => exact hx21_1.trans hmeRegs
            | some meV meG => exact ⟨hx21_1.trans hmeRegs.1, hx28_1.trans hmeRegs.2.1, hmeRegs.2.2⟩,
          ownSem := ⟨ownB, hget_o, by cases me <;> exact hp_o⟩,
          trace := htr1 ▸ htr, fs := (congrArg FsState.files hfs1).trans hfs, stdout := htr1 ▸ hout }

private theorem r0_dealloc_own_buf_rp [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {S : RunSem} {g : RunCall} {me : MeAtDispatch} {cap ptr : BitVec 64}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hsub_ext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (he : AtRunEntryPlaced CodeOk S g s0) (hbase : InRunPlaced CodeOk s0 s 0x1e8)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx23 : s.readReg64 (.gpr 23#5) = g.inp)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap)
    (hmeRegs : r0_meRegs_rp me s) (hownSem : r0_ownSem_rp g me) (htr : s0.trace <+: s.trace)
    (hfs : s.fs.files = runFiles g.i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) (hlay : LayoutOk cap.toNat 1)
    (hnext : ∀ (s' : State) (evs_free : List AllocEvent) (me' : MeAtDispatch),
      FreeOnlyEvs evs_free →
      AtDispatchPlaced CodeOk g me' s0 s' →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (dispatchMemPlaced A lim (M.stepEvents evs_free st) g me' s0 s' resStack) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
        dispatchMemPlaced A lim st g me s0 s resStack) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur
  refine r0_frame_seq_rp hbase.inv
    (F := (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
      dispatchMemPlaced A lim st g me s0 s resStack)
    (Entails.of_eq (by rw [emp_sepConj]))
    (r0_step_dealloc_pre_rp (A := A) (lim := lim) (st := st)
      hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx26 hx27) ?_
  rintro s1 hinv1 hpc1 hrun1
    ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hpool1, hx0_1, hx1_1, hx2_1,
     hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx28_1⟩
  refine r0_call_rocl_steps_rp (s0 := s0) (Q := Q) (Qp := Qp)
    (ptr, cap.toNat, 1, st) (AllocContractsFsPlaced.dealloc_rocl hh.allocFs (prog := runProgPlaced H) (i := 579))
    hinv1 hpc1 hrun1 (r0_spAligned_rp hbase.spAligned hsp1) hlr1
    (F := r0_constFrame_rp A.repAlloc g s0 ∗ dispatchMeHeap A.repAlloc me ∗
      runLocals (runFsp s0) (dispatchCells (runFsp s0) me) ∗
      memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
        ((resStack - runFrame) - extHookStack))
    (hP := ?_) (hnext := ?_)
  · rw [emp_sepConj]
    have hme_at : dispatchMeHeap (A.atState lim st s) me = dispatchMeHeap A.repAlloc me := by
      cases me <;> rfl
    dsimp only [dispatchMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced]
    rw [callAt_atState, storesAt_opened_atState, hme_at]
    dsimp only [r0_constFrame_rp, Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
    rw [hsp1, ← hpool1, r0_subStack_split_rp (runFsp s0) hsub_ext hsub64]
    conv => rhs; rw [sepConj_assoc]
    have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, by decide⟩
    exact Entails.pure_right ⟨hx0_1, hx1_1 ▸ rfl, by rw [hx2_1]; rfl, hrlay,
      by rw [hlr1, runPcPlaced_eq]; exact lsRetAddr624_blockPlacement_base_add 579 504#64 (by decide) (by decide)⟩
      (Entails.of_eq (by sep_ac_rfl))
  intro s2 _ hinv2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, _, hx28_2, hfp2, hv2⟩
  have hme_at2 :
      dispatchMeHeap (A.atState lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) s2) me =
        dispatchMeHeap A.repAlloc me := by
    cases me <;> rfl
  refine SepWPp.weaken_pre
    (P' := ⌜s2.fs = s1.fs ∧ s2.trace = s1.trace⌝ ∗
      dispatchMemPlaced A lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) g me s0 s2 resStack)
    (by dsimp only [dispatchMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced]
        rw [callAt_atState, storesAt_opened_atState, hme_at2]
        dsimp only [r0_constFrame_rp, Spec.keepsFs, rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
          RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
        rw [hsp1, r0_subStack_split_rp (runFsp s0) hsub_ext hsub64]
        simp only [← sepConj_assoc, pure_sepConj_pure]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨hfs2, htr2⟩
  exact r0_dispatch_tail_rp he
    ⟨hpc2, hrun2, hsp2.trans hsp1, hfp2.trans hfp1, hinv2, hv2.trans hv1, hbase.spAligned⟩
    (hx19_2.trans (hx19_1.trans hx19)) (hx20_2.trans (hx20_1.trans hx20))
    (hx23_2.trans (hx23_1.trans hx23)) (hx24_2.trans (hx24_1.trans hx24))
    (hx25_2.trans (hx25_1.trans hx25))
    (by dsimp only [r0_meRegs_rp] at hmeRegs ⊢
        cases me with
        | none => rwa [hx21_2, hx21_1]
        | some meV meG => rwa [hx21_2, hx21_1, hx28_2, hx28_1])
    hownSem ((htr2.trans htr1) ▸ htr)
    ((congrArg FsState.files (hfs2.trans hfs1)).trans hfs) ((htr2.trans htr1) ▸ hout)
    (fun s' me' hd => hnext s' (rustDeallocEvents cap.toNat 1) me' (FreeOnlyEvs.singleton 1 cap.toNat) hd)

private theorem r0_pack_dispatch_none_rp [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (g : RunCall)
    (s0 s : State) (resStack : Nat) :
    (((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗ memRegion (runFsp s0 + 0x1758#64) 24) ∗
      r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
      memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗
      r0_constFrame_rp A.repAlloc g s0 ⊢
    dispatchMemPlaced A lim st g .none s0 s resStack := by
  have hslot32 : ((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗ memRegion (runFsp s0 + 0x1758#64) 24 ⊢
      memRegion (runFsp s0 + 0x1750#64) 32 := by
    rw [show (32 : Nat) = 8 + 24 from rfl, r0_memRegion_8_24_rp (runFsp s0 + 0x1750#64),
      show runFsp s0 + 0x1750#64 + 8#64 = runFsp s0 + 0x1758#64 by bv_omega]
    exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
  dsimp only [dispatchMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
    r0_constFrame_rp, dispatchMeHeap, dispatchCells,
    RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
  rw [← r0_frame3_rejoin_rp (runFsp s0)]
  exact Entails.trans (sepConj_mono_left hslot32) (Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 800000 in
private theorem r0_pack_dispatch_some_rp [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (g : RunCall)
    (meV : AddrV) (meG : AddrGhost) (w1 : BitVec 64) (s0 s : State) (resStack : Nat)
    (hw1 : w1.setWidth 8 = meG.device) :
    ((runFsp s0 + 0x1750#64) ↦₆₄ meG.name.cap) ∗ ((runFsp s0 + 0x1758#64) ↦₆₄ meG.name.ptr) ∗
      ((runFsp s0 + 0x1760#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
      ((runFsp s0 + 0x1768#64) ↦₆₄ w1) ∗
      ((runFsp s0 + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
      ((runFsp s0 + 0x1d8#64) ↦₆₄ w1) ∗ addrNameHeap A.repAlloc meG ∗ r0_gaps_rp (runFsp s0) ∗
      memRegion (runFsp s0 + 0x4d0#64) 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
      A.pool lim st s ∗ r0_constFrame_rp A.repAlloc g s0 ⊢
    dispatchMemPlaced A lim st g (.some meV meG) s0 s resStack := by
  have hslot32 :
      ((runFsp s0 + 0x1750#64) ↦₆₄ meG.name.cap) ∗ ((runFsp s0 + 0x1758#64) ↦₆₄ meG.name.ptr) ∗
        ((runFsp s0 + 0x1760#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((runFsp s0 + 0x1768#64) ↦₆₄ w1) ⊢ memRegion (runFsp s0 + 0x1750#64) 32 := by
    rw [show runFsp s0 + 0x1758#64 = (runFsp s0 + 0x1750#64) + 8#64 by bv_omega,
      show runFsp s0 + 0x1760#64 = (runFsp s0 + 0x1750#64) + 16#64 by bv_omega,
      show runFsp s0 + 0x1768#64 = (runFsp s0 + 0x1750#64) + 24#64 by bv_omega]
    exact r0_four_words_entails_32_rp _ _ _ _ _
  have hup1d0 :
      ((runFsp s0 + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((runFsp s0 + 0x1d8#64) ↦₆₄ w1) ⊢ addrUpperAt (runFsp s0 + 0x1d0#64) meG := by
    rw [show runFsp s0 + 0x1d8#64 = (runFsp s0 + 0x1d0#64) + 8#64 by bv_omega]
    exact r0_addrUpperAt_close_rp _ w1 meG hw1
  dsimp only [dispatchMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
    dispatchMeHeap, dispatchCells, RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
  refine Entails.trans (r0_apply_head_rp (sepConj_mono hslot32 hup1d0)
    (F := addrNameHeap A.repAlloc meG ∗ r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ r0_constFrame_rp A.repAlloc g s0)
    (by sep_ac_rfl)) ?_
  refine Entails.trans (r0_apply_head_rp (r0_frame3_rejoin_some_rp (runFsp s0) meG)
    (F := addrNameHeap A.repAlloc meG ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
      A.pool lim st s ∗ r0_constFrame_rp A.repAlloc g s0) (by sep_ac_rfl)) ?_
  dsimp only [r0_constFrame_rp, RustCliAllocBudget.repAlloc]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem r0_post_address_rp [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {S : RunSem} {g : RunCall} {ownB : Bytes}
    {cap ptr : BitVec 64} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hsub_ext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64) (he : AtRunEntryPlaced CodeOk S g s0)
    (hbase : InRunPlaced CodeOk s0 s 0x1cc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx23 : s.readReg64 (.gpr 23#5) = g.inp)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap)
    (hget : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB)
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hnext : ∀ (s' : State) (evs_free : List AllocEvent) (me' : MeAtDispatch),
      FreeOnlyEvs evs_free →
      AtDispatchPlaced CodeOk g me' s0 s' →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (dispatchMemPlaced A lim (M.stepEvents evs_free st) g me' s0 s' resStack) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((match addrParse uuidTryParse ownB with
        | none => ((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗ memRegion (runFsp s0 + 0x1758#64) 24
        | some a => ∃∗ meG : AddrGhost,
            ⌜meG.name.bytes = a.name ∧ meG.name.cap = BitVec.ofNat 64 a.name.length ∧ meG.device = a.device⌝ ∗
              protocolAddressAt A.repAlloc meG (runFsp s0 + 0x1750#64)) ∗
        ((ptr ↦ₛ ownB) ∗ r0_ownedRest_rp A.repAlloc cap ptr ownB) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗
        r0_constFrame_rp A.repAlloc g s0) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur
  let tail4 (sCur : State) : SepProp :=
    r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sCur ∗ r0_constFrame_rp A.repAlloc g s0
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (r0_ownedBytes_free_rp A.repAlloc cap ptr ownB))) ?_
  cases hparse_own : addrParse uuidTryParse ownB with
  | none =>
    by_cases hcap0 : cap = 0
    · subst hcap0; simp only [↓reduceIte]
      refine r0_frame_seq_rp hbase.inv (F := memRegion (runFsp s0 + 0x1758#64) 24 ∗ tail4 s)
        (Entails.of_eq (by dsimp only [tail4]; simp only [emp_sepConj]; sep_ac_rfl))
        (r0_step_post_none_zero_rp (A := A) (lim := lim) (st := st)
          hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx27) ?_
      rintro s1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hpool1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1⟩
      refine SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by dsimp only [tail4]; rw [← hpool1]; sep_ac_rfl))
          (r0_pack_dispatch_none_rp A lim st g s0 s1 resStack))
        (r0_dispatch_tail_rp he ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩
          (hx19_1.trans hx19) (hx20_1.trans hx20) (hx23_1.trans hx23) (hx24_1.trans hx24)
          (hx25_1.trans hx25) hx21_1 ⟨ownB, hget, hparse_own⟩ (htr1 ▸ htr)
          ((congrArg FsState.files hfs1).trans hfs) (htr1 ▸ hout)
          (fun s' me' hd => hnext s' [] me' FreeOnlyEvs.nil hd))
    · simp only [hcap0, ↓reduceIte]
      refine SepWPp.weaken_pre (P' := ⌜LayoutOk cap.toNat 1⌝ ∗ (((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗
          (memRegion (runFsp s0 + 0x1758#64) 24 ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
            tail4 s)))
        (Entails.of_eq (by dsimp only [tail4, RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      apply r0_sepWPp_pure_left_rp; intro hlay
      refine r0_frame_seq_rp hbase.inv
        (F := memRegion (runFsp s0 + 0x1758#64) 24 ∗
          (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ tail4 s)
        (Entails.refl _)
        (r0_step_post_none_nz_rp (A := A) (lim := lim) (st := st)
          hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx26 hx27 hcap0) ?_
      rintro s1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hpool1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1⟩
      exact SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by dsimp only [tail4]; rw [← hpool1]; sep_ac_rfl))
          (sepConj_mono_right (r0_pack_dispatch_none_rp A lim st g s0 s1 resStack)))
        (r0_dealloc_own_buf_rp hh hsub_ext hsub64 he ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩
          (hx19_1.trans hx19) (hx20_1.trans hx20) (hx23_1.trans hx23) (hx24_1.trans hx24)
          (hx25_1.trans hx25) hx26_1 hx27_1 hx21_1 ⟨ownB, hget, hparse_own⟩ (htr1 ▸ htr)
          ((congrArg FsState.files hfs1).trans hfs) (htr1 ▸ hout) hlay hnext)
  | some meV =>
    let freeOpt : SepProp :=
      if cap = 0 then emp
      else ⌜LayoutOk cap.toNat 1⌝ ∗ A.repAlloc.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat
    let tailSome (sCur : State) : SepProp :=
      r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sCur ∗ r0_constFrame_rp A.repAlloc g s0
    apply r0_sepWPp_exists_left_rp; intro meG
    refine SepWPp.weaken_pre
      (P' := ⌜meG.name.bytes = meV.name ∧ meG.name.cap = BitVec.ofNat 64 meV.name.length ∧ meG.device = meV.device⌝ ∗
        (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x1750#64) ∗
          memRegion (runFsp s0 + 0x1d0#64) 16 ∗ freeOpt ∗ tailSome s))
      (Entails.of_eq (by dsimp only [freeOpt, tailSome]; sep_ac_rfl)) ?_
    apply r0_sepWPp_pure_left_rp; rintro ⟨hme_bytes, hme_cap, hme_dev⟩
    have hheap_pure : addrNameHeap A.repAlloc meG ⊢
        ⌜meG.name.bytes.length ≤ meG.name.cap.toNat ∧ meG.name.cap.toNat < 2 ^ 63 ∧ meG.name.ptr ≠ 0⌝ ∗
          addrNameHeap A.repAlloc meG := by
      unfold addrNameHeap; apply Entails.pure_left; intro hp
      exact Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))
    rw [protocolAddressAt_eq_parts A.repAlloc meG (runFsp s0 + 0x1750#64),
      show (runFsp s0 + 0x1750#64) + 8#64 = runFsp s0 + 0x1758#64 by bv_omega,
      show (runFsp s0 + 0x1750#64) + 16#64 = runFsp s0 + 0x1760#64 by bv_omega,
      r0_memRegion_two_words_rp (runFsp s0 + 0x1d0#64)]
    refine SepWPp.weaken_pre
      (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (r0_addrUpperAt_open_rp (runFsp s0 + 0x1760#64) meG) hheap_pure))))
        (Entails.of_eq (by
          simp only [sepExists_sepConj_left, sepExists_sepConj_right,
            show (runFsp s0 + 0x1760#64) + 8#64 = runFsp s0 + 0x1768#64 by bv_omega,
            show (runFsp s0 + 0x1d0#64) + 8#64 = runFsp s0 + 0x1d8#64 by bv_omega]
          sep_ac_rfl))) ?_
    apply r0_sepWPp_exists_all_rp; intro u1; apply r0_sepWPp_exists_all_rp; intro u0
    apply r0_sepWPp_exists_all_rp; intro w1
    let words6 (x0 x1 : BitVec 64) : SepProp :=
      ((runFsp s0 + 0x1750#64) ↦₆₄ meG.name.cap) ∗ ((runFsp s0 + 0x1758#64) ↦₆₄ meG.name.ptr) ∗
        ((runFsp s0 + 0x1760#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((runFsp s0 + 0x1768#64) ↦₆₄ w1) ∗ ((runFsp s0 + 0x1d0#64) ↦₆₄ x0) ∗
        ((runFsp s0 + 0x1d8#64) ↦₆₄ x1)
    refine SepWPp.weaken_pre (P' := ⌜w1.setWidth 8 = meG.device⌝ ∗
        (⌜meG.name.bytes.length ≤ meG.name.cap.toNat ∧ meG.name.cap.toNat < 2 ^ 63 ∧ meG.name.ptr ≠ 0⌝ ∗
          (words6 u0 u1 ∗ addrNameHeap A.repAlloc meG ∗ freeOpt ∗ tailSome s)))
      (Entails.of_eq (by dsimp only [words6]; sep_ac_rfl)) ?_
    apply r0_sepWPp_pure_left_rp; intro hw1_dev; apply r0_sepWPp_pure_left_rp; rintro ⟨_, hme_lt, _⟩
    dsimp only [freeOpt, tailSome, words6]
    by_cases hcap0 : cap = 0
    · subst hcap0; simp only [↓reduceIte]
      refine r0_frame_seq_rp hbase.inv (F := addrNameHeap A.repAlloc meG ∗ tailSome s)
        (Entails.of_eq (by dsimp only [tailSome]; simp only [emp_sepConj]; sep_ac_rfl))
        (r0_step_post_some_zero_rp (A := A) (lim := lim) (st := st)
          hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx27 hme_lt) ?_
      rintro s1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hpool1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx28_1⟩
      exact SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by dsimp only [tailSome]; rw [← hpool1]; sep_ac_rfl))
          (r0_pack_dispatch_some_rp A lim st g meV meG w1 s0 s1 resStack hw1_dev))
        (r0_dispatch_tail_rp he ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩
          (hx19_1.trans hx19) (hx20_1.trans hx20) (hx23_1.trans hx23) (hx24_1.trans hx24)
          (hx25_1.trans hx25) ⟨hx21_1, hx28_1, hme_bytes, hme_cap, hme_dev⟩ ⟨ownB, hget, hparse_own⟩
          (htr1 ▸ htr) ((congrArg FsState.files hfs1).trans hfs) (htr1 ▸ hout)
          (fun s' me' hd => hnext s' [] me' FreeOnlyEvs.nil hd))
    · simp only [hcap0, ↓reduceIte]
      refine SepWPp.weaken_pre
        (P' := ⌜LayoutOk cap.toNat 1⌝ ∗
          (words6 u0 u1 ∗ (addrNameHeap A.repAlloc meG ∗
            (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ tailSome s)))
        (Entails.of_eq (by dsimp only [words6, tailSome, RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      apply r0_sepWPp_pure_left_rp; intro hlay
      refine r0_frame_seq_rp hbase.inv
        (F := addrNameHeap A.repAlloc meG ∗
          (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ tailSome s)
        (Entails.refl _)
        (r0_step_post_some_nz_rp (A := A) (lim := lim) (st := st)
          hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs hx26 hx27 hcap0 hme_lt) ?_
      rintro s1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hpool1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1,
         hx26_1, hx27_1, hx28_1⟩
      exact SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by dsimp only [words6, tailSome]; rw [← hpool1]; sep_ac_rfl))
          (sepConj_mono_right (r0_pack_dispatch_some_rp A lim st g meV meG w1 s0 s1 resStack hw1_dev)))
        (r0_dealloc_own_buf_rp hh hsub_ext hsub64 he ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hbase.spAligned⟩
          (hx19_1.trans hx19) (hx20_1.trans hx20) (hx23_1.trans hx23) (hx24_1.trans hx24)
          (hx25_1.trans hx25) hx26_1 hx27_1 ⟨hx21_1, hx28_1, hme_bytes, hme_cap, hme_dev⟩
          ⟨ownB, hget, hparse_own⟩ (htr1 ▸ htr) ((congrArg FsState.files hfs1).trans hfs) (htr1 ▸ hout)
          hlay hnext)

/-! ## Top-Level `run_hop_pre_placed_ok` -/

set_option maxHeartbeats 800000 in
private theorem r0_ok_utf8_address_rp [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {S : RunSem} {g : RunCall} {ownB : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hsub_ext : extHookStack ≤ resStack - runFrame)
    (hsub_addr : 0xB0 + extHookStack ≤ resStack - runFrame)
    (hsub63 : resStack - runFrame ≤ 2 ^ 63) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (he : AtRunEntryPlaced CodeOk S g s0) (hbase : InRunPlaced CodeOk s0 s 0x60)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx23 : s.readReg64 (.gpr 23#5) = g.inp)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (hget : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB)
    (hfit_post : FitsEnv M lim st (SeqEnv (· = addressEvents uuidTryParse ownB) FreeOnlyEvs))
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hnext : ∀ (s' : State) (evs_post : List AllocEvent) (me' : MeAtDispatch),
      SeqEnv (· = addressEvents uuidTryParse ownB) FreeOnlyEvs evs_post →
      AtDispatchPlaced CodeOk g me' s0 s' →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (dispatchMemPlaced A lim (M.stepEvents evs_post st) g me' s0 s' resStack) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (vecResultAt A.repAlloc (runFsp s0 + 0x4d0#64) (.ok ownB) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗
        r0_constFrame_rp A.repAlloc g s0) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur
  have hascii : ∀ b ∈ ownB, b.toNat < 128 := he.bounds_pre.2 ownB hget
  have hutf8 := fromUtf8_placed_ok (callerProg := runProgPlaced H) (i := 579) hh extHookStack
  have haddr := runAddress_placed_ok (callerProg := runProgPlaced H) (i := 579)
    hh (resStack - runFrame) hsub_addr hsub63
  let slotsNoStack (sCur : State) : SepProp :=
    r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
      memRegion (runFsp s0 + 0x1750#64) 32 ∗ A.pool lim st sCur ∗ r0_constFrame_rp A.repAlloc g s0
  let restTail (sCur : State) : SepProp := stackAt (runFsp s0) (resStack - runFrame) ∗ slotsNoStack sCur
  rw [r0_decResultOk_eq_words_rp A.repAlloc (runFsp s0 + 0x4d0#64) ownB]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply r0_sepWPp_exists_left_rp; intro ptr; apply r0_sepWPp_exists_left_rp; intro cap
  refine SepWPp.weaken_pre
    (P' := ⌜BitVec.ofNat 64 ownB.length = BitVec.ofNat 64 ownB.length⌝ ∗
      ((((runFsp s0 + 0x4d0#64) ↦₆₄ okTagVec) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ cap) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ ptr) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length)) ∗
        (memRegion (runFsp s0 + 0x4f0#64) 16 ∗ (ptr ↦ₛ ownB) ∗
          r0_ownedRest_rp A.repAlloc cap ptr ownB ∗ restTail s)))
    (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (r0_ownedBytes_split_rp A.repAlloc cap ptr (BitVec.ofNat 64 ownB.length) ownB))))
      (Entails.of_eq (by dsimp only [restTail, slotsNoStack]; sep_ac_rfl))) ?_
  apply r0_sepWPp_pure_left_rp; intro _
  refine r0_frame_seq_rp hbase.inv
    (F := memRegion (runFsp s0 + 0x4f0#64) 16 ∗ (ptr ↦ₛ ownB) ∗
      r0_ownedRest_rp A.repAlloc cap ptr ownB ∗ restTail s)
    (Entails.refl _)
    (r0_step_ok_pre_utf8_rp (A := A) (lim := lim) (st := st)
      hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs) ?_
  rintro s1 hinv1 hpc1 hrun1
    ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hpool1, hx0_1, hx1_1, hx8_1,
     hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1⟩
  refine r0_call_lscro_steps_rp (s0 := s0) (Q := Q) (Qp := Qp) (runFsp s0 + 0x4d0#64, ptr, ownB)
    hutf8 hinv1 hpc1 hrun1 (r0_spAligned_rp hbase.spAligned hsp1) hlr1
    (F := ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗ memRegion (runFsp s0 + 0x4f0#64) 16 ∗
      r0_ownedRest_rp A.repAlloc cap ptr ownB ∗
      memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame)) ((resStack - runFrame) - extHookStack) ∗
      slotsNoStack s1)
    (hP := ?_) (hnext := ?_)
  · have h24 : ((runFsp s0 + 0x4d0#64) ↦₆₄ okTagVec) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ cap) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ ptr) ⊢ memRegion (runFsp s0 + 0x4d0#64) 24 := by
      rw [show runFsp s0 + 0x4d8#64 = (runFsp s0 + 0x4d0#64) + 8#64 by bv_omega,
        show runFsp s0 + 0x4e0#64 = (runFsp s0 + 0x4d0#64) + 16#64 by bv_omega]
      exact r0_three_words_entails_24_rp _ _ _ _
    dsimp only [restTail, slotsNoStack, withVmPreserved, fromUtf8AsciiSpec]
    rw [hsp1, ← hpool1, r0_subStack_split_rp (runFsp s0) hsub_ext hsub64]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right ⟨hx0_1, hx1_1, hx8_1, hascii⟩ ?_
    refine Entails.trans (r0_apply_head_rp h24
      (F := (ptr ↦ₛ ownB) ∗ stackAt (runFsp s0) extHookStack ∗
        (((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗ memRegion (runFsp s0 + 0x4f0#64) 16 ∗
          r0_ownedRest_rp A.repAlloc cap ptr ownB ∗
          memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - extHookStack) ∗
          (r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
            memRegion (runFsp s0 + 0x1750#64) 32 ∗ A.pool lim st s1 ∗ r0_constFrame_rp A.repAlloc g s0)))
      (by sep_ac_rfl)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  intro s2 _ hinv2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, _, hfp2, hv2⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc]
  apply r0_sepWPp_pure_left_rp; intro hvm2
  let postUtf8Rest (sCur : State) : SepProp :=
    ((runFsp s0 + 0x4d8#64) ↦₆₄ ptr) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗
      ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗ memRegion (runFsp s0 + 0x4f0#64) 16 ∗
      (ptr ↦ₛ ownB) ∗ r0_ownedRest_rp A.repAlloc cap ptr ownB ∗ restTail sCur
  refine SepWPp.weaken_pre
    (P' := ⌜s2.trace = s1.trace ∧ s2.fs = s1.fs⌝ ∗ (((runFsp s0 + 0x4d0#64) ↦₆₄ 0#64) ∗ postUtf8Rest s2))
    (by dsimp only [postUtf8Rest, restTail, slotsNoStack, fromUtf8AsciiSpec]
        rw [hsp1, ← A.pool_transport lim st s1 s2 hvm2, r0_subStack_split_rp (runFsp s0) hsub_ext hsub64]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨htr2, hfs2⟩
  have hsp2' : s2.sp = runFsp s0 := hsp2.trans hsp1
  refine r0_frame_seq_rp hinv2 (F := postUtf8Rest s2) (Entails.refl _)
    (r0_step_ok_pre_addr_rp (A := A) (lim := lim) (st := st)
      hpc2 hrun2 hsp2' (r0_spAligned_rp hbase.spAligned hsp2')
      (hfp2.trans hfp1) (hv2.trans hv1) (hx21_2.trans hx21_1)
      (hx26_2.trans hx26_1) (hx27_2.trans hx27_1)) ?_
  rintro s3 hinv3 hpc3 hrun3
    ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3, hpool3, hx0_3, hx1_3, hx2_3,
     hx19_3, hx20_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3⟩
  have htr_s3 : s0.trace <+: s3.trace := (htr3.trans (htr2.trans htr1)) ▸ htr
  have hfit_addr : FitsEnv M lim st (AddressEnv uuidTryParse ⟨runFsp s0 + 0x1750#64, ptr, ownB⟩) :=
    hfit_post.seq_left
  refine r0_call_lscro_steps_rp (s0 := s0) (Q := Q) (Qp := Qp)
    (⟨runFsp s0 + 0x1750#64, ptr, ownB⟩, st)
    haddr hinv3 hpc3 hrun3 (r0_spAligned_rp hbase.spAligned hsp3) hlr3
    (F := r0_ownedRest_rp A.repAlloc cap ptr ownB ∗ r0_gaps_rp (runFsp s0) ∗
      memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      r0_constFrame_rp A.repAlloc g s0)
    (hP := ?_) (hnext := ?_)
  · have h48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ 0#64) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ ptr) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗
        ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗ memRegion (runFsp s0 + 0x4f0#64) 16 ⊢
        memRegion (runFsp s0 + 0x4d0#64) 48 := by
      have h32 : ((runFsp s0 + 0x4d0#64) ↦₆₄ 0#64) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ ptr) ∗
          ((runFsp s0 + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ∗
          ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 ownB.length) ⊢ memRegion (runFsp s0 + 0x4d0#64) 32 := by
        rw [show runFsp s0 + 0x4d8#64 = (runFsp s0 + 0x4d0#64) + 8#64 by bv_omega,
          show runFsp s0 + 0x4e0#64 = (runFsp s0 + 0x4d0#64) + 16#64 by bv_omega,
          show runFsp s0 + 0x4e8#64 = (runFsp s0 + 0x4d0#64) + 24#64 by bv_omega]
        exact r0_four_words_entails_32_rp _ _ _ _ _
      rw [show (48 : Nat) = 32 + 16 from rfl,
        ProofLib.memRegion_split (runFsp s0 + 0x4d0#64) 32 16 (by decide),
        show (runFsp s0 + 0x4d0#64) + 32#64 = runFsp s0 + 0x4f0#64 by bv_omega]
      exact r0_apply_head_rp h32 (by sep_ac_rfl)
    dsimp only [postUtf8Rest, restTail, slotsNoStack, addressSpec]
    rw [hsp3, ← hpool3]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right ⟨hx0_3, hx1_3, hx2_3, hfit_addr⟩ ?_
    refine Entails.trans (r0_apply_head_rp h48
      (F := (ptr ↦ₛ ownB) ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗ A.pool lim st s3 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ r0_ownedRest_rp A.repAlloc cap ptr ownB ∗
        r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗ r0_constFrame_rp A.repAlloc g s0)
      (by sep_ac_rfl)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  intro s4 _ hinv4 hpc4 hrun4 hsp4 hcs4
  rcases hcs4 with ⟨hx19_4, hx20_4, _, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, _, hfp4, hv4⟩
  dsimp only [addressSpec]
  apply r0_sepWPp_exists_left_rp; intro evs_a
  refine SepWPp.weaken_pre (P' := ⌜s4.trace = s3.trace ∧ s4.fs = s3.fs ∧
      AddressEnv uuidTryParse ⟨runFsp s0 + 0x1750#64, ptr, ownB⟩ evs_a⌝ ∗
      ((match addrParse uuidTryParse ownB with
        | none => ((runFsp s0 + 0x1750#64) ↦₆₄ noneCap) ∗ memRegion (runFsp s0 + 0x1758#64) 24
        | some a => ∃∗ meG : AddrGhost,
            ⌜meG.name.bytes = a.name ∧ meG.name.cap = BitVec.ofNat 64 a.name.length ∧ meG.device = a.device⌝ ∗
              protocolAddressAt A.repAlloc meG (runFsp s0 + 0x1750#64)) ∗
        ((ptr ↦ₛ ownB) ∗ r0_ownedRest_rp A.repAlloc cap ptr ownB) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_a st) s4 ∗
        r0_constFrame_rp A.repAlloc g s0))
    (by rw [hsp3]
        have ha58 : (runFsp s0 + 0x1750#64) + 8#64 = runFsp s0 + 0x1758#64 := by bv_omega
        cases addrParse uuidTryParse ownB with
        | none => rw [ha58]; exact Entails.of_eq (by dsimp [noneCap]; sep_ac_rfl)
        | some a => dsimp only; exact Entails.of_eq (by sep_ac_rfl)) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨htr4, hfs4, ha_ev⟩
  exact r0_post_address_rp hh hsub_ext hsub64 he
    ⟨hpc4, hrun4, hsp4.trans hsp3, hfp4.trans hfp3, hinv4, hv4.trans hv3, hbase.spAligned⟩
    (hx19_4.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19))))
    (hx20_4.trans (hx20_3.trans (hx20_2.trans (hx20_1.trans hx20))))
    (hx23_4.trans (hx23_3.trans (hx23_2.trans (hx23_1.trans hx23))))
    (hx24_4.trans (hx24_3.trans (hx24_2.trans (hx24_1.trans hx24))))
    (hx25_4.trans (hx25_3.trans (hx25_2.trans (hx25_1.trans hx25))))
    (hx26_4.trans hx26_3) (hx27_4.trans hx27_3) hget (htr4 ▸ htr_s3)
    ((congrArg FsState.files (hfs4.trans (hfs3.trans (hfs2.trans hfs1)))).trans hfs)
    ((htr4.trans (htr3.trans (htr2.trans htr1))) ▸ hout)
    (fun s' evs_free me' hfo hd => by
      have hseq : SeqEnv (· = addressEvents uuidTryParse ownB) FreeOnlyEvs (evs_a ++ evs_free) :=
        SeqEnv.append ha_ev hfo
      have hm := hnext s' (evs_a ++ evs_free) me' hseq hd
      rwa [M.stepEvents_append] at hm)

set_option maxHeartbeats 800000 in
private theorem r0_err_to_reject_rp [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 st1 : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {g : RunCall} {evs_get : List AllocEvent}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hsub_drop : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hbase : InRunPlaced CodeOk s0 s 0x60) (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (hst1 : st1 = M.stepEvents evs_get st0)
    (hget_ev : cEnvs.dirGet (runFiles g.i) StoresGhost.opened.identity.own (utf8 "address") evs_get)
    (herr : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .error ())
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some none)
    (hrej : RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, PreEnv cEnvs g evs ∧ st' = M.stepEvents evs st0)
      g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (speAt A.repAlloc (utf8 "read") (runFsp s0 + 0x4d0#64) .invalidState ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st1 s ∗
        r0_constFrame_rp A.repAlloc g s0) Q Qp (runOom s0) := by
  have hal : s.spAligned = true := hbase.spAligned_cur
  have hdrop_call : subroutine_ok (runProgPlaced H) (blkPl_553).base
      (withLsCodeRoLoaded lsmpl (dropSpeOwnedSpec A lim (resStack - runFrame))) :=
    hdrop (resStack - runFrame) hsub_drop hsub64
  rw [r0_speInvalidState_eq_words_rp A.repAlloc (utf8 "read") (runFsp s0 + 0x4d0#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply r0_sepWPp_exists_left_rp; intro fnPtr; apply r0_sepWPp_exists_left_rp; intro bs
  apply r0_sepWPp_exists_left_rp; intro ptr; apply r0_sepWPp_exists_left_rp; intro cap
  refine r0_frame_seq_rp hbase.inv
    (F := (fnPtr ↦ᵣ utf8 "read") ∗ ownedBytes A.repAlloc cap ptr (BitVec.ofNat 64 bs.length) bs ∗
      r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st1 s ∗ r0_constFrame_rp A.repAlloc g s0)
    (Entails.of_eq (by sep_ac_rfl))
    (r0_step_err_pre_drop_rp (A := A) (lim := lim) (st := st1)
      hbase.pc hbase.run hbase.sp hal hbase.fp hbase.vregs) ?_
  rintro s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hpool1, hx0_1, hx19_1, hx20_1, hx25_1⟩
  refine r0_call_lscro_steps_rp (s0 := s0) (Q := Q) (Qp := Qp)
    (⟨runFsp s0 + 0x4d0#64, .proto (utf8 "read") .invalidState⟩, st1)
    hdrop_call hinv1 hpc1 hrun1 (r0_spAligned_rp hbase.spAligned hsp1) hlr1
    (F := r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
      memRegion (runFsp s0 + 0x1750#64) 32 ∗ r0_constFrame_rp A.repAlloc g s0)
    (hP := ?_) (hnext := ?_)
  · have hspe : ((runFsp s0 + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ cap) ∗
        ((runFsp s0 + 0x4e0#64) ↦₆₄ ptr) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((runFsp s0 + 0x4f0#64) ↦₆₄ fnPtr) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") ∗ ownedBytes A.repAlloc cap ptr (BitVec.ofNat 64 bs.length) bs ⊢
        speOwnedAt A.repAlloc (runFsp s0 + 0x4d0#64) (.proto (utf8 "read") .invalidState) := by
      dsimp only [speOwnedAt]; rw [r0_speInvalidState_eq_words_rp A.repAlloc (utf8 "read") (runFsp s0 + 0x4d0#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.sepExists_right fnPtr (Entails.sepExists_right bs
        (Entails.sepExists_right ptr (Entails.sepExists_right cap (Entails.refl _))))
    dsimp only [dropSpeOwnedSpec]; rw [hsp1, ← hpool1]; conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right ⟨hx0_1,
      by rw [hlr1, runPcPlaced_eq]; exact lsRetAddr624_blockPlacement_base_add 579 292#64 (by decide) (by decide)⟩
      (Entails.trans (r0_apply_head_rp hspe
      (F := A.pool lim st1 s1 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
        r0_constFrame_rp A.repAlloc g s0) (by sep_ac_rfl)) (Entails.of_eq (by sep_ac_rfl)))
  intro s2 hsteps2 hinv2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, hx25_2, _, _, _, hfp2, hv2⟩
  dsimp only [dropSpeOwnedSpec]
  apply r0_sepWPp_exists_left_rp; intro evs_drop
  refine SepWPp.weaken_pre (P' := ⌜s2.trace = s1.trace ∧ FreeOnlyEvs evs_drop⌝ ∗
      rejectMem (A.atState lim (M.stepEvents evs_drop st1) s2) g StoresGhost.opened .preDispatch s0 resStack)
    (by dsimp only [rejectMem, r0_constFrame_rp, RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
        rw [hsp1, ← r0_frame3_rejoin_rp (runFsp s0)]
        have hany :
            coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
              CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
              lsLogOff ⊢ anyHeap := entails_anyHeap _
        exact Entails.trans (r0_apply_head_rp hany (F := ⌜s2.trace = s1.trace ∧ FreeOnlyEvs evs_drop⌝ ∗
          memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_drop st1) s2)
          (by sep_ac_rfl)) (Entails.of_eq (by sep_ac_rfl))) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨htr2, hfo_drop⟩
  have hfs2_eq : s2.fs.files = s.fs.files :=
    (r0_files_eq_of_trace_eq_rp (hh.fs (lsProg_579 H) 579) hsteps2 htr2).trans (congrArg FsState.files hfs1)
  have htr2_eq : s2.trace = s.trace := htr2.trans htr1
  have hpre_ev : PreEnv cEnvs g (evs_get ++ evs_drop) :=
    SeqEnv.append hget_ev (by simp only [PreAfterGetEnv, herr]; exact hfo_drop)
  have hst_eq : M.stepEvents evs_drop st1 = M.stepEvents (evs_get ++ evs_drop) st0 := by
    rw [hst1, ← M.stepEvents_append]
  exact hrej s2 (M.stepEvents evs_drop st1) StoresGhost.opened .preDispatch
    { base := ⟨hpc2, hrun2, hsp2.trans hsp1, hfp2.trans hfp1, hinv2, hv2.trans hv1, hbase.spAligned⟩
      x19 := hx19_2.trans (hx19_1.trans hx19)
      preRegs := fun _ => ⟨hx20_2.trans (hx20_1.trans hx20), hx25_2.trans (hx25_1.trans hx25)⟩
      trace := htr2_eq ▸ htr, hist := ⟨hfs2_eq.trans hhist.1, htr2_eq ▸ hhist.2⟩, ans := hans }
    ⟨evs_get ++ evs_drop, hpre_ev, hst_eq⟩

set_option maxHeartbeats 800000 in
theorem run_hop_pre_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopPrePlaced CodeOk A lim cEnvs sEnvs (PreEnv cEnvs) H B S needs resStack := by
  intro g st s0 Q Qp hh hc hdrop hres hres64 he hfit _hpanic hrej hnext
  obtain ⟨hrf, hsub63, hsub64, hsub_addr, _, _, _, hsub_get, _, _, _, _, _, _, hsub_drop, _, hsub_ext, _⟩ :=
    runNeed_bounds_placed (A := A) (lim := lim) (envs := sEnvs) hres hres64
  apply r0_sepWPp_intro_address_rp he.inv
  unfold runEntryMemPlaced CryptoVerification.SignalSession.Cli.RunCompose.runEntryMemPlaced
  rw [stackAt_run_split s0 hrf (by omega : resStack ≤ 2 ^ 64), r0_memRegion_saved_open_rp s0,
    r0_probes_split_rp s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r0_sepWPp_exists_all_rp; intro p2; apply r0_sepWPp_exists_all_rp; intro p1
  apply r0_sepWPp_exists_all_rp; intro p0; apply r0_sepWPp_exists_all_rp; intro v11
  apply r0_sepWPp_exists_all_rp; intro v10; apply r0_sepWPp_exists_all_rp; intro v9
  apply r0_sepWPp_exists_all_rp; intro v8; apply r0_sepWPp_exists_all_rp; intro v7
  apply r0_sepWPp_exists_all_rp; intro v6; apply r0_sepWPp_exists_all_rp; intro v5
  apply r0_sepWPp_exists_all_rp; intro v4; apply r0_sepWPp_exists_all_rp; intro v3
  apply r0_sepWPp_exists_all_rp; intro v2; apply r0_sepWPp_exists_all_rp; intro v1
  apply r0_sepWPp_exists_all_rp; intro v0
  have hpc0 : s0.pc = (blkPl_579).base := he.pc.trans runPcPlaced_zero
  refine r0_frame_seq_rp he.inv (F := ((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗
      (memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗ memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗
        memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8)) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s0 ∗
      memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
      storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
      CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      lsLogOff)
    (Entails.of_eq (by dsimp only [RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]; sep_ac_rfl))
    (r0_step_prologue_rp (A := A) (lim := lim) (st := st) hpc0 he.run he.spAligned) ?_
  rintro s1 hinv1 hpc1 hrun1
    ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hpool1, hx0_1, hx1_1, hx2_1, hx3_1,
     hx19_1, hx20_1, hx23_1, hx24_1, hx25_1⟩
  have hfs1_run : s1.fs.files = runFiles g.i := (congrArg FsState.files hfs1).trans he.fs
  have hfit_get :
      FitsEnv M lim st (cEnvs.dirGet s1.fs.files StoresGhost.opened.identity.own (utf8 "address")) := by
    rw [hfs1_run]; exact hfit.seq_left
  have hget_call := hc.dirGet hsub_get; unfold dirGetSpecPlaced at hget_call
  refine r0_call_lscro_steps_rp (s0 := s0) (Q := Q) (Qp := Qp)
    (({ ret := runFsp s0 + 0x4d0#64, self := g.stores, dir := StoresGhost.opened.identity.own,
        nameA := lsρ r0_addrSym_rp, name := utf8 "address", nameRo := true } : DirGetGhost), st)
    hget_call hinv1 hpc1 hrun1 (r0_spAligned_rp he.spAligned hsp1) hlr1
    (F := r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
      memRegion (runFsp s0 + 0x1750#64) 32 ∗ memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
      r0_storesRest_rp A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
      CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      lsLogOff ∗ runSaved s0)
    (hP := ?_) (hnext := ?_)
  · have hrejoin : (((s0.sp - 0x2a50#64) ↦₆₄ 0#64) ∗ ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗ memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗
        memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗
        memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8)) ⊢
        r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x1750#64) 32 := by
      rw [← r0_frame3_split_rp (runFsp s0)]; exact r0_probes_rejoin_rp s0
    simp only [CryptoVerification.SpqrV1.ChainProofs.bytesAt, ↓reduceIte]
    rw [hsp1, ← hpool1, r0_storesAt_eq_rp A.repAlloc g.stores StoresGhost.opened]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right
      ⟨hx0_1, hx1_1.trans he.x2, hx2_1, by rw [hx3_1, r0_utf8_address_rp]; rfl,
       by rw [r0_utf8_address_rp]; decide, by decide, r0_own_wrOk_rp, hfit_get⟩ ?_
    exact Entails.trans (r0_apply_head_rp hrejoin (F := runSaved s0 ∗ ((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 ∗ memRegion g.res runResSize ∗
      callAt A.repAlloc g.call g.c ∗
      (dirAt A.repAlloc g.stores StoresGhost.opened.identity.own ∗
        r0_storesRest_rp A.repAlloc g.stores StoresGhost.opened) ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
      CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      lsLogOff) (by sep_ac_rfl)) (Entails.of_eq (by sep_ac_rfl))
  intro s2 hsteps2 hinv2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, _, hx23_2, hx24_2, hx25_2, _, _, _, hfp2, hv2⟩
  apply r0_sepWPp_exists_left_rp; intro evs_get
  refine SepWPp.weaken_pre (P' := ((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗
      ((∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = StoresGhost.opened.identity.own.get cliIo.rd s1.fs.files (utf8 "address") ∧
            s2.trace = s1.trace ∧
            cEnvs.dirGet s1.fs.files StoresGhost.opened.identity.own (utf8 "address") evs_get⌝ ∗
            getResultAt A.repAlloc (runFsp s0 + 0x4d0#64) r) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_get st) s2 ∗
        r0_constFrame_rp A.repAlloc g s0))
    (by simp only [r0_constFrame_rp, CryptoVerification.SpqrV1.ChainProofs.bytesAt, ↓reduceIte]
        rw [hsp1, r0_storesAt_eq_rp A.repAlloc g.stores StoresGhost.opened]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
  apply r0_sepWPp_drop_left_rp; apply r0_sepWPp_exists_left_rp; intro r
  refine SepWPp.weaken_pre (Entails.of_eq (sepConj_assoc _ _ _)) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨hr_eq, htr2, hget_ev⟩
  have hbase2 : InRunPlaced CodeOk s0 s2 0x60 :=
    ⟨hpc2, hrun2, hsp2.trans hsp1, hfp2.trans hfp1, hinv2, hv2.trans hv1, he.spAligned⟩
  have hfs2 : s2.fs.files = runFiles g.i :=
    (r0_files_eq_of_trace_eq_rp (hh.fs (lsProg_579 H) 579) hsteps2 htr2).trans hfs1_run
  have htr2_s0 : s2.trace = s0.trace := htr2.trans htr1
  have hget_ev' :
      cEnvs.dirGet (runFiles g.i) StoresGhost.opened.identity.own (utf8 "address") evs_get :=
    hfs1_run ▸ hget_ev
  have hfit1 : FitsEnv M lim (M.stepEvents evs_get st) (PreAfterGetEnv g) :=
    hfit.seq_right hget_ev'
  cases r with
  | error u =>
    cases u; dsimp only [getResultAt]
    have herr : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .error () :=
      hfs1_run ▸ hr_eq.symm
    exact r0_err_to_reject_rp hh hdrop hsub_drop hsub64 hbase2
      (hx19_2.trans (hx19_1.trans he.x2)) (hx20_2.trans (hx20_1.trans he.x0))
      (hx25_2.trans (hx25_1.trans he.x1)) rfl hget_ev' herr (htr2_s0 ▸ List.prefix_refl _)
      ⟨hfs2, htr2_s0 ▸ he.stdout⟩ (he.reject_of_own_err herr) hrej
  | ok ownB =>
    dsimp only [getResultAt]
    have hok : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB :=
      hfs1_run ▸ hr_eq.symm
    have hfit_post :
        FitsEnv M lim (M.stepEvents evs_get st)
          (SeqEnv (· = addressEvents uuidTryParse ownB) FreeOnlyEvs) := by
      unfold PreAfterGetEnv at hfit1
      rwa [hok] at hfit1
    exact r0_ok_utf8_address_rp hh hsub_ext hsub_addr hsub63 hsub64 he hbase2
      (hx19_2.trans (hx19_1.trans he.x2)) (hx20_2.trans (hx20_1.trans he.x0))
      (hx23_2.trans (hx23_1.trans he.x3)) (hx24_2.trans (hx24_1.trans he.x4))
      (hx25_2.trans (hx25_1.trans he.x1)) hok hfit_post
      (htr2_s0 ▸ List.prefix_refl _) hfs2 (htr2_s0 ▸ he.stdout)
      (fun s' evs_post me' hseq hd => by
        have hpre : PreEnv cEnvs g (evs_get ++ evs_post) :=
          SeqEnv.append hget_ev' (by simp only [PreAfterGetEnv, hok]; exact hseq)
        have hm := hnext s' (evs_get ++ evs_post) me' hd hpre
        rwa [M.stepEvents_append] at hm)


set_option maxHeartbeats 800000 in
theorem run_hop_pre_of_slots_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A lim sEnvs S needs)) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget.RunHopPrePlacedOf
      CodeOk A lim cEnvs (PreEnv cEnvs) H B S slots resStack := by
  intro g st s0 Q Qp hh hc hdrop hres hres64 he hfit _hpanic hrej hnext
  obtain ⟨hrf, hsub63, hsub64, hsub_addr, _, _, _, hsub_get, _, _, _, _, _, _, hsub_drop, _, hsub_ext, _⟩ :=
    runNeed_bounds_placed (A := A) (lim := lim) (envs := sEnvs) (hneed_eq ▸ hres) hres64
  apply r0_sepWPp_intro_address_rp he.inv
  unfold runEntryMemPlaced CryptoVerification.SignalSession.Cli.RunCompose.runEntryMemPlaced
  rw [stackAt_run_split s0 hrf (by omega : resStack ≤ 2 ^ 64), r0_memRegion_saved_open_rp s0,
    r0_probes_split_rp s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r0_sepWPp_exists_all_rp; intro p2; apply r0_sepWPp_exists_all_rp; intro p1
  apply r0_sepWPp_exists_all_rp; intro p0; apply r0_sepWPp_exists_all_rp; intro v11
  apply r0_sepWPp_exists_all_rp; intro v10; apply r0_sepWPp_exists_all_rp; intro v9
  apply r0_sepWPp_exists_all_rp; intro v8; apply r0_sepWPp_exists_all_rp; intro v7
  apply r0_sepWPp_exists_all_rp; intro v6; apply r0_sepWPp_exists_all_rp; intro v5
  apply r0_sepWPp_exists_all_rp; intro v4; apply r0_sepWPp_exists_all_rp; intro v3
  apply r0_sepWPp_exists_all_rp; intro v2; apply r0_sepWPp_exists_all_rp; intro v1
  apply r0_sepWPp_exists_all_rp; intro v0
  have hpc0 : s0.pc = (blkPl_579).base := he.pc.trans runPcPlaced_zero
  refine r0_frame_seq_rp he.inv (F := ((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗
      (memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗ memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗
        memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8)) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s0 ∗
      memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
      storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
      CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      lsLogOff)
    (Entails.of_eq (by dsimp only [RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]; sep_ac_rfl))
    (r0_step_prologue_rp (A := A) (lim := lim) (st := st) hpc0 he.run he.spAligned) ?_
  rintro s1 hinv1 hpc1 hrun1
    ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hpool1, hx0_1, hx1_1, hx2_1, hx3_1,
     hx19_1, hx20_1, hx23_1, hx24_1, hx25_1⟩
  have hfs1_run : s1.fs.files = runFiles g.i := (congrArg FsState.files hfs1).trans he.fs
  have hfit_get :
      FitsEnv M lim st (cEnvs.dirGet s1.fs.files StoresGhost.opened.identity.own (utf8 "address")) := by
    rw [hfs1_run]; exact hfit.seq_left
  have hget_call := hc.dirGet hsub_get; unfold dirGetSpecPlaced at hget_call
  refine r0_call_lscro_steps_rp (s0 := s0) (Q := Q) (Qp := Qp)
    (({ ret := runFsp s0 + 0x4d0#64, self := g.stores, dir := StoresGhost.opened.identity.own,
        nameA := lsρ r0_addrSym_rp, name := utf8 "address", nameRo := true } : DirGetGhost), st)
    hget_call hinv1 hpc1 hrun1 (r0_spAligned_rp he.spAligned hsp1) hlr1
    (F := r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
      memRegion (runFsp s0 + 0x1750#64) 32 ∗ memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
      r0_storesRest_rp A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
      CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      lsLogOff ∗ runSaved s0)
    (hP := ?_) (hnext := ?_)
  · have hrejoin : (((s0.sp - 0x2a50#64) ↦₆₄ 0#64) ∗ ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗ memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗
        memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗
        memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8)) ⊢
        r0_gaps_rp (runFsp s0) ∗ memRegion (runFsp s0 + 0x1d0#64) 16 ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x1750#64) 32 := by
      rw [← r0_frame3_split_rp (runFsp s0)]; exact r0_probes_rejoin_rp s0
    simp only [CryptoVerification.SpqrV1.ChainProofs.bytesAt, ↓reduceIte]
    rw [hsp1, ← hpool1, r0_storesAt_eq_rp A.repAlloc g.stores StoresGhost.opened]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right
      ⟨hx0_1, hx1_1.trans he.x2, hx2_1, by rw [hx3_1, r0_utf8_address_rp]; rfl,
       by rw [r0_utf8_address_rp]; decide, by decide, r0_own_wrOk_rp, hfit_get⟩ ?_
    exact Entails.trans (r0_apply_head_rp hrejoin (F := runSaved s0 ∗ ((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 ∗ memRegion g.res runResSize ∗
      callAt A.repAlloc g.call g.c ∗
      (dirAt A.repAlloc g.stores StoresGhost.opened.identity.own ∗
        r0_storesRest_rp A.repAlloc g.stores StoresGhost.opened) ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
      CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      lsLogOff) (by sep_ac_rfl)) (Entails.of_eq (by sep_ac_rfl))
  intro s2 hsteps2 hinv2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, _, hx23_2, hx24_2, hx25_2, _, _, _, hfp2, hv2⟩
  apply r0_sepWPp_exists_left_rp; intro evs_get
  refine SepWPp.weaken_pre (P' := ((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗
      ((∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = StoresGhost.opened.identity.own.get cliIo.rd s1.fs.files (utf8 "address") ∧
            s2.trace = s1.trace ∧
            cEnvs.dirGet s1.fs.files StoresGhost.opened.identity.own (utf8 "address") evs_get⌝ ∗
            getResultAt A.repAlloc (runFsp s0 + 0x4d0#64) r) ∗ r0_gaps_rp (runFsp s0) ∗
        memRegion (runFsp s0 + 0x1d0#64) 16 ∗ memRegion (runFsp s0 + 0x1750#64) 32 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_get st) s2 ∗
        r0_constFrame_rp A.repAlloc g s0))
    (by simp only [r0_constFrame_rp, CryptoVerification.SpqrV1.ChainProofs.bytesAt, ↓reduceIte]
        rw [hsp1, r0_storesAt_eq_rp A.repAlloc g.stores StoresGhost.opened]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
  apply r0_sepWPp_drop_left_rp; apply r0_sepWPp_exists_left_rp; intro r
  refine SepWPp.weaken_pre (Entails.of_eq (sepConj_assoc _ _ _)) ?_
  apply r0_sepWPp_pure_left_rp; rintro ⟨hr_eq, htr2, hget_ev⟩
  have hbase2 : InRunPlaced CodeOk s0 s2 0x60 :=
    ⟨hpc2, hrun2, hsp2.trans hsp1, hfp2.trans hfp1, hinv2, hv2.trans hv1, he.spAligned⟩
  have hfs2 : s2.fs.files = runFiles g.i :=
    (r0_files_eq_of_trace_eq_rp (hh.fs (lsProg_579 H) 579) hsteps2 htr2).trans hfs1_run
  have htr2_s0 : s2.trace = s0.trace := htr2.trans htr1
  have hget_ev' :
      cEnvs.dirGet (runFiles g.i) StoresGhost.opened.identity.own (utf8 "address") evs_get :=
    hfs1_run ▸ hget_ev
  have hfit1 : FitsEnv M lim (M.stepEvents evs_get st) (PreAfterGetEnv g) :=
    hfit.seq_right hget_ev'
  cases r with
  | error u =>
    cases u; dsimp only [getResultAt]
    have herr : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .error () :=
      hfs1_run ▸ hr_eq.symm
    exact r0_err_to_reject_rp hh hdrop hsub_drop hsub64 hbase2
      (hx19_2.trans (hx19_1.trans he.x2)) (hx20_2.trans (hx20_1.trans he.x0))
      (hx25_2.trans (hx25_1.trans he.x1)) rfl hget_ev' herr (htr2_s0 ▸ List.prefix_refl _)
      ⟨hfs2, htr2_s0 ▸ he.stdout⟩ (he.reject_of_own_err herr) hrej
  | ok ownB =>
    dsimp only [getResultAt]
    have hok : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB :=
      hfs1_run ▸ hr_eq.symm
    have hfit_post :
        FitsEnv M lim (M.stepEvents evs_get st)
          (SeqEnv (· = addressEvents uuidTryParse ownB) FreeOnlyEvs) := by
      unfold PreAfterGetEnv at hfit1
      rwa [hok] at hfit1
    exact r0_ok_utf8_address_rp hh hsub_ext hsub_addr hsub63 hsub64 he hbase2
      (hx19_2.trans (hx19_1.trans he.x2)) (hx20_2.trans (hx20_1.trans he.x0))
      (hx23_2.trans (hx23_1.trans he.x3)) (hx24_2.trans (hx24_1.trans he.x4))
      (hx25_2.trans (hx25_1.trans he.x1)) hok hfit_post
      (htr2_s0 ▸ List.prefix_refl _) hfs2 (htr2_s0 ▸ he.stdout)
      (fun s' evs_post me' hseq hd => by
        have hpre : PreEnv cEnvs g (evs_get ++ evs_post) :=
          SeqEnv.append hget_ev' (by simp only [PreAfterGetEnv, hok]; exact hseq)
        have hm := hnext s' (evs_get ++ evs_post) me' hd hpre
        rwa [M.stepEvents_append] at hm)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
