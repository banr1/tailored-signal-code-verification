/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAuxFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FdsGe3Closed`-Threaded Relocatable Arm `R0` Proof

Proves `run_hop_pre_of_slots_placed_ok_fd` and `run_hop_pre_placed_ok_fd` on Block `579`, threading
`FdsGe3Closed` across `Dir::get("address")`, `from_utf8`, `signal_session::address`, and optional
buffer deallocation to `AtDispatchPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost noneCap okTagVec protocolAddressAt uuidTryParse vecResultAt)
open CryptoVerification.SignalSession.Cli (DirGetGhost StoresGhost dirAt getResultAt utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv RunCall addrParse callAt cliIo coinsInstalledPlaced
   fromUtf8AsciiSpec inputOf runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtRunEntryPlaced Bytes InRunPlaced MeAtDispatch RunNeeds
   RunSem runFiles runFsp runLocalBytes runOom runPcPlaced_zero
   runProgPlaced runSaved stackAt_run_split)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame runNeed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (AddressEnv addressEvents addressSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
  (PreAfterGetEnv PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAux
  (r0_addrSym_rp r0_apply_head_rp r0_call_lscro_steps_rp r0_constFrame_rp r0_decResultOk_eq_words_rp
   r0_files_eq_of_trace_eq_rp r0_four_words_entails_32_rp r0_frame3_split_rp r0_frame_seq_rp
   r0_gaps_rp r0_memRegion_saved_open_rp r0_own_wrOk_rp r0_ownedBytes_split_rp r0_ownedRest_rp
   r0_probes_rejoin_rp r0_probes_split_rp r0_sepWPp_drop_left_rp r0_sepWPp_exists_all_rp
   r0_sepWPp_exists_left_rp r0_sepWPp_intro_address_rp r0_sepWPp_pure_left_rp r0_spAligned_rp
   r0_step_ok_pre_addr_rp r0_step_ok_pre_utf8_rp r0_step_prologue_rp r0_storesAt_eq_rp
   r0_storesRest_rp r0_subStack_split_rp r0_three_words_entails_24_rp r0_utf8_address_rp)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (RunHopPrePlacedFd RunHopPrePlacedFdOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAuxFd
  (r0_err_to_reject_rp r0_post_address_rp_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (dispatchMemPlaced runEntryMemPlaced runNeed_bounds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced fromUtf8_placed_ok runAddress_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (dirGetSpecPlaced)

set_option maxHeartbeats 800000 in
theorem r0_ok_utf8_address_rp_fd [LibsignalPlacement] {M : AllocCostModel}
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
    (hfds : FdsGe3Closed s.fs)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hnext : ∀ (s' : State) (evs_post : List AllocEvent) (me' : MeAtDispatch),
      SeqEnv (· = addressEvents uuidTryParse ownB) FreeOnlyEvs evs_post →
      AtDispatchPlaced CodeOk g me' s0 s' →
      FdsGe3Closed s'.fs →
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
  exact r0_post_address_rp_fd hh hsub_ext hsub64 he
    ⟨hpc4, hrun4, hsp4.trans hsp3, hfp4.trans hfp3, hinv4, hv4.trans hv3, hbase.spAligned⟩
    (hx19_4.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19))))
    (hx20_4.trans (hx20_3.trans (hx20_2.trans (hx20_1.trans hx20))))
    (hx23_4.trans (hx23_3.trans (hx23_2.trans (hx23_1.trans hx23))))
    (hx24_4.trans (hx24_3.trans (hx24_2.trans (hx24_1.trans hx24))))
    (hx25_4.trans (hx25_3.trans (hx25_2.trans (hx25_1.trans hx25))))
    (hx26_4.trans hx26_3) (hx27_4.trans hx27_3) hget (htr4 ▸ htr_s3)
    ((congrArg FsState.files (hfs4.trans (hfs3.trans (hfs2.trans hfs1)))).trans hfs)
    ((hfs4.trans (hfs3.trans (hfs2.trans hfs1))) ▸ hfds)
    ((htr4.trans (htr3.trans (htr2.trans htr1))) ▸ hout)
    (fun s' evs_free me' hfo hd hfds' => by
      have hseq : SeqEnv (· = addressEvents uuidTryParse ownB) FreeOnlyEvs (evs_a ++ evs_free) :=
        SeqEnv.append ha_ev hfo
      have hm := hnext s' (evs_a ++ evs_free) me' hseq hd hfds'
      rwa [M.stepEvents_append] at hm)

set_option maxHeartbeats 800000 in
/-- Slot-parametric `FdsGe3Closed`-threaded Arm `R0` hop theorem (`R+0x0 → R+0x214`, early reject `R+0x124`). -/
theorem run_hop_pre_of_slots_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A lim sEnvs S needs)) :
    RunHopPrePlacedFdOf CodeOk A lim cEnvs (PreEnv cEnvs) H B S slots resStack := by
  rintro g st s0 Q Qp hh hc hdrop hres hres64 ⟨he, hfds0⟩ hfit _hpanic hrej hnext
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
  have hfds1 : FdsGe3Closed s1.fs := hfs1 ▸ hfds0
  have hfit_get :
      FitsEnv M lim st (cEnvs.dirGet s1.fs.files StoresGhost.opened.identity.own (utf8 "address")) := by
    rw [hfs1_run]; exact hfit.seq_left
  have hget_raw := hc.dirGet hsub_get; unfold dirGetSpecPlaced at hget_raw
  have hget_call := subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed hget_raw
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
    dsimp only [withFdsGe3Closed]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right hfds1 ?_
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
  dsimp only [withFdsGe3Closed]
  rw [sepConj_assoc]
  apply r0_sepWPp_pure_left_rp; intro hfds2
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
    exact r0_ok_utf8_address_rp_fd hh hsub_ext hsub_addr hsub63 hsub64 he hbase2
      (hx19_2.trans (hx19_1.trans he.x2)) (hx20_2.trans (hx20_1.trans he.x0))
      (hx23_2.trans (hx23_1.trans he.x3)) (hx24_2.trans (hx24_1.trans he.x4))
      (hx25_2.trans (hx25_1.trans he.x1)) hok hfit_post
      (htr2_s0 ▸ List.prefix_refl _) hfs2 hfds2 (htr2_s0 ▸ he.stdout)
      (fun s' evs_post me' hseq hd hfds' => by
        have hpre : PreEnv cEnvs g (evs_get ++ evs_post) :=
          SeqEnv.append hget_ev' (by simp only [PreAfterGetEnv, hok]; exact hseq)
        have hm := hnext s' (evs_get ++ evs_post) me' ⟨hd, hfds'⟩ hpre
        rwa [M.stepEvents_append] at hm)

theorem run_hop_pre_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopPrePlacedFd CodeOk A lim cEnvs sEnvs (PreEnv cEnvs) H B S needs resStack :=
  run_hop_pre_of_slots_placed_ok_fd (sEnvs := sEnvs) (needs := needs) rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetFd
