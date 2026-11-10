/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2StepsPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.Disproof.Basic

/-!
# Budget-Threaded `signal_session::run` Arm `R2`: Error Arm, Copy Steps, and Slice Frees

Proves the post-`encrypt` error arm (`r2pb_err_arm`), 31-word tag-check/copy steps, and
`SignalMessage` slice deallocation steps on Block `579` (`runProgPlaced H`) under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudgetAux

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open scoped LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2StepsPlacedBudget
open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal ctSignalTag)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost errTag)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.SignalSession (Inputs lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliWrOk inputOf ownedBytes_dealloc ownedBytes_zero_entails_emp
   runResAt runResSize sepWPp_weaken_pre storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (InRunPlaced RejectKind RunHistOk
   addrNameHeap encResAt r2_SlotWords r2_addrNameHeap_eq_ownedBytes
   r2_ans_of_trace_eq r2_csm_trans r2_hold r2_hold_eq r2_localGaps
   r2_res_open r2_res_write_none r2_words31
   r2p_CodeOk r2p_cs_regs r2p_histOk_of_trace_files r2p_inRun_mk r2p_vregs_0 r2p_vregs_1
   r2p_vregs_2 runFsp runPcPlaced runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunDrop (DropSpeOwnedGhost SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunProofs (encResAt_err_owned sret248_rejoin)
open CryptoVerification.SignalSession.Cli.RunProofs.DropPreKeyMsgHelpers
  (optSliceDeallocX sliceDeallocX)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2StepsPlacedBudget
  (r2pbFreeCapEvs r2pbFreeMePeerEvs r2pbFreeOptSliceEvs r2pbFreePeerEvs r2pbFreeSliceEvs
   r2pb_call r2pb_call_dealloc r2pb_files_of_trace_eq r2pb_free_peer_reject
   r2pb_peel_pure_tc r2pb_peel_tc r2pb_sepWP_with_vm_oom r2pb_sepWPp_exists_left
   r2pb_seq_lscro_oom r2pb_stOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget (dropSpeOwnedSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff r2_hold
attribute [local arm64_norm, local wp_norm]
  ProofLib.bv_sub_add_lit BitVec.toNat_zero r2p_vregs_0 r2p_vregs_1 r2p_vregs_2

/-! ## 1. Error Arm (`r2pb_err_arm`), Tag-Check/Copy, and `SignalMessage` Slice Frees -/

set_option maxHeartbeats 800000 in
theorem r2pb_err_arm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {peerG meG : AddrGhost} {g' : StoresGhost}
    {err : ApiError AddrVal Unit}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hdropNeed : 32 + extHookStack ≤ resStack - runFrame)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hneStore : err ≠ .store ())
    (hans : g.a = some none)
    (henv : ∀ evs_drop : List AllocEvent, FreeOnlyEvs evs_drop →
      EnvAt g' .postDispatch (M.stepEvents (evs_drop ++ r2pbFreeMePeerEvs meG peerG) st))
    (hrej : RejectKPlacedEnv r2p_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (encResAt A.repAlloc (fsp + 0x4d0#64) (.error err) ∗
        addrNameHeap A.repAlloc meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  intro fsp
  let tailErr (sPool : State) : SepProp :=
    addrNameHeap A.repAlloc meG ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st sPool ∗ anyHeap
  let tailErrPost (stCur : M.σ) (sPool : State) : SepProp :=
    memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim stCur sPool ∗ anyHeap
  let tailErrPostNoPool : SepProp :=
    memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap
  refine sepWPp_weaken_pre
    (sepConj_mono_left (encResAt_err_owned A.repAlloc (fsp + 0x4d0#64) err hneStore)) ?_
  have hpull_k :
      (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
          (∃∗ k : SpeOwned, speOwnedAt A.repAlloc ((fsp + 0x4d0#64) + 8#64) k) ∗
          memRegion ((fsp + 0x4d0#64) + 56#64) 192) ∗ tailErr s =
      (∃∗ k : SpeOwned,
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
          speOwnedAt A.repAlloc ((fsp + 0x4d0#64) + 8#64) k ∗
          memRegion ((fsp + 0x4d0#64) + 56#64) 192 ∗ tailErr s) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  rw [hpull_k]
  apply r2pb_sepWPp_exists_left; intro k
  have hpc : s.pc = runPcPlaced 1308 := hin.pc; change s.pc = (blkPl_579).base + 1308#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = fsp := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  have herr_val : errTag = 0xffffffffffffffff#64 := rfl
  have he_eq2 : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 2#64) = false := by r2pb_cond
  have he_ne2 : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 2#64) = true := by r2pb_cond
  have he_eq1 : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by r2pb_cond
  have he_ne1 : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 1#64) = false := by r2pb_cond
  have hmi_e : ConditionHolds .MI (subsPState64 0xffffffffffffffff#64 0#64) = true := by r2pb_cond
  have hpl_e : ConditionHolds .PL (subsPState64 0xffffffffffffffff#64 0#64) = false := by r2pb_cond
  apply r2pb_seq_lscro_oom (mid := (blkPl_553).base) hin.inv
  rw [herr_val, ← r2_hold_eq (speOwnedAt A.repAlloc ((fsp + 0x4d0#64) + 8#64) k ∗ _)]
  change s.readReg64 (.gpr 22#5) = fsp + 0x4d0#64 at hx22
  rw [← hsp0] at hx22 ⊢
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx22 ⊢)
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
    change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
    clear hpc
    rw [hsp0, r2_hold_eq]
    dsimp only [tailErr]
    rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
    have hdrop_call := hdrop (resStack - runFrame) hdropNeed hsub64
    refine r2pb_call (DropSpeOwnedGhost.mk ((fsp + 0x4d0#64) + 8#64) k, st)
      hdrop_call hinv1 (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
      (by dsimp only [r2pb_stOf]; simp only [State.spAligned, wp_norm, arm64_norm]; exact hsp_al)
      (ret_pc := runPcPlaced 2956) (by r2pb_pc_done)
      (F := ((fsp + 0x4d0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        memRegion ((fsp + 0x4d0#64) + 56#64) 192 ∗
        addrNameHeap A.repAlloc meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap)
      ?_
      (hnext := fun s2 hsteps2 hinv2 hpcm2 hrun2 hsp2 hcs2 => ?_)
    · dsimp only [dropSpeOwnedSpec]
      rw [sepConj_assoc]
      refine Entails.pure_right
        ⟨by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); (try dsimp only [fsp]); try bv_omega,
         ⟨579, by decide, 2956, by decide,
           (by r2pb_pc_done : (r2pb_stOf hinv1).readReg64 .lr = runPcPlaced 2956).trans
             (runPcPlaced_eq 2956)⟩⟩ ?_
      dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm])
      rw [hsp0]; dsimp only [fsp, runFsp]; (try simp only [wp_norm, arm64_norm])
      exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only [dropSpeOwnedSpec]
      apply r2pb_peel_tc; intro evs_drop
      apply r2pb_peel_pure_tc; rintro ⟨htr2, hfo_drop⟩
      simp only [emp_sepConj, sepConj_assoc]
      let st2 := M.stepEvents evs_drop st
      have hfs2 := r2pb_files_of_trace_eq hh hsteps2 htr2
      have htr_s2 : s0.trace <+: s2.trace :=
        htr2 ▸ (by dsimp only [r2pb_stOf]; simpa only [wp_norm, arm64_norm] using htr)
      have hhist_s2 : RunHistOk g.i s0 s2 :=
        r2p_histOk_of_trace_files
          (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq)) htr2 hfs2
      have hans_s2 : g.a = some none := r2_ans_of_trace_eq htr2 hans
      have hcs := r2p_cs_regs hcs2
      have hin2 : InRunPlaced r2p_CodeOk s0 s2 2956 :=
        r2p_inRun_mk hin hpcm2 hrun2 (hsp2.trans (by r2pb_eq))
          (hcs.2.2.2.2.2.2.2.2.2.2.1.trans (by r2pb_eq)) hinv2
          (hcs.2.2.2.2.2.2.2.2.2.2.2.trans (by r2pb_eq))
      have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by
        rw [hcs.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19
      have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by
        rw [hcs.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx20
      have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by
        rw [hcs.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx21
      have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr := by
        rw [hcs.2.2.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx28
      clear hcs hcs2
      have hsret := sret248_rejoin (fsp + 0x4d0#64) 0xffffffffffffffff#64
      refine sepWPp_weaken_pre
        (P' := memRegion g.res runResSize ∗ addrNameHeap A.repAlloc meG ∗ tailErrPost st2 s2)
        (by
          dsimp only [tailErrPost, st2]
          rw [← hsp2, (hin2.sp : s2.sp = fsp)]
          refine Entails.trans (Entails.of_eq ?_)
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsret)))))))))))))))
          sep_ac_rfl) ?_
      refine sepWPp_weaken_pre (sepConj_mono_left (r2_res_open g.res)) ?_
      rw [sepExists_sepConj_left]
      apply r2pb_sepWPp_exists_left; intro r0
      rw [r2_addrNameHeap_eq_ownedBytes A.repAlloc meG]
      have hpc2 : s2.pc = runPcPlaced 2956 := hin2.pc; change s2.pc = (blkPl_579).base + 2956#64 at hpc2
      have hrun2' : s2.status = .Running := hin2.run
      have hsp2_cur : s2.sp = fsp := hin2.sp
      have hsp_al2 : s2.spAligned = true := hin2.spAligned_cur
      have henv_me_peer := henv evs_drop hfo_drop
      rw [AllocCostModel.stepEvents_append] at henv_me_peer
      by_cases hcap : meG.name.cap = 0#64
      · have henv0 : EnvAt g' .postDispatch (M.stepEvents (r2pbFreePeerEvs peerG) st2) := by
          simpa [st2, r2pbFreeMePeerEvs, r2pbFreePeerEvs, r2pbFreeCapEvs, hcap] using henv_me_peer
        rw [hcap]
        refine sepWPp_weaken_pre
          (sepConj_mono_right (sepConj_mono_left (ownedBytes_zero_entails_emp A.repAlloc _ _ _))) ?_
        rw [emp_sepConj]
        apply r2pb_seq_lscro_oom (mid := runPcPlaced 2984) hin2.inv
        have hx21_0 : s2.readReg64 (.gpr 21#5) = 0#64 := hx21_2.trans hcap
        rw [← r2_hold_eq (tailErrPost st2 s2), runPcPlaced_eq]
        dsimp only [runProgPlaced, lsProg_579]
        by_vm_open (
          wp_steps
          refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun2'])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm3 hinv3 => ?_⟩
          change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv3) _ _ _ _
          rw [r2_hold_eq]
          dsimp only [tailErrPost]
          rw [← A.pool_transport lim st2 s2 (r2pb_stOf hinv3) hvm3]
          have hin3 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv3) 2984 :=
            r2p_inRun_mk hin2 (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun2'])
              (by r2pb_eq) (by r2pb_eq) hinv3 (by r2pb_eq)
          refine sepWPp_weaken_pre
            (sepConj_mono_left (r2_res_write_none A.repAlloc g.res 0xffffffffffffffff#64 rfl)) ?_
          exact r2pb_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin3
            (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19_2)
            (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr_s2)
            (r2p_histOk_of_trace_files hhist_s2 (by r2pb_eq) (by r2pb_eq))
            hans_s2 henv0 hrej
        )
      · have henv1 : EnvAt g' .postDispatch
            (M.stepEvents (r2pbFreePeerEvs peerG)
              (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st2)) := by
          simpa [st2, r2pbFreeMePeerEvs, r2pbFreePeerEvs, r2pbFreeCapEvs, hcap,
            AllocCostModel.stepEvents_append] using henv_me_peer
        refine sepWPp_weaken_pre
          (sepConj_mono_right (sepConj_mono_left (ownedBytes_dealloc A.repAlloc hcap))) ?_
        have hpull_me :
            ((g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
              (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗ A.repAlloc.live meG.name.ptr meG.name.cap.toNat 1 ∗
                memRegion meG.name.ptr meG.name.cap.toNat) ∗ tailErrPost st2 s2 =
            ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
              (((g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
                (A.live meG.name.ptr meG.name.cap.toNat 1 ∗
                  memRegion meG.name.ptr meG.name.cap.toNat ∗ tailErrPost st2 s2)) := by
          dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl
        rw [hpull_me]
        apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
        have hlt63 : meG.name.cap.toNat < 2 ^ 63 := by omega
        have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
        have hx21_b : (s2.readReg64 (.gpr 21#5) == 0#64) = false := hx21_2.symm ▸ hbeq
        apply r2pb_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hin2.inv
        rw [← r2_hold_eq (A.live meG.name.ptr meG.name.cap.toNat 1 ∗ _)]
        dsimp only [runProgPlaced, lsProg_579]
        by_vm_open (
          wp_steps
          refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun2'])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm3 hinv3 => ?_⟩
          change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv3) _ _ _ _
          rw [r2_hold_eq]
          dsimp only [tailErrPost]
          rw [← A.pool_transport lim st2 s2 (r2pb_stOf hinv3) hvm3]
          have hres_none := r2_res_write_none A.repAlloc g.res 0xffffffffffffffff#64 rfl
          refine sepWPp_weaken_pre (sepConj_mono_left hres_none) ?_
          have hreord_da :
              runResAt A.repAlloc cliWrOk g.res (some none) ∗
                (A.live meG.name.ptr meG.name.cap.toNat 1 ∗
                  memRegion meG.name.ptr meG.name.cap.toNat ∗
                  (memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗
                    (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
                    ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
                    ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
                    memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
                    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
                    memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
                    memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
                    stackAt fsp (resStack - runFrame) ∗
                    A.pool lim st2 (r2pb_stOf hinv3) ∗ anyHeap)) =
              A.live meG.name.ptr meG.name.cap.toNat 1 ∗
                memRegion meG.name.ptr meG.name.cap.toNat ∗
                A.pool lim st2 (r2pb_stOf hinv3) ∗ stackAt fsp (resStack - runFrame) ∗
                (runResAt A.repAlloc cliWrOk g.res (some none) ∗ tailErrPostNoPool) := by
            dsimp only [tailErrPostNoPool]; sep_ac_rfl
          rw [hreord_da]
          refine r2pb_call_dealloc (nextOff := 2984) hh hextNeed hsub64 hin2 hinv3
            (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun2'])
            (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_pc_done)
            (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); try exact hx28_2)
            (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); try exact hx21_2)
            (by r2pb_eq) hpos hlt63
            (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr_s2)
            (r2p_histOk_of_trace_files hhist_s2 (by r2pb_eq) (by r2pb_eq))
            fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
          have hcs_f := r2p_cs_regs hcsm
          have hback :
              A.pool lim (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st2) sf ∗
                stackAt fsp (resStack - runFrame) ∗
                (runResAt A.repAlloc cliWrOk g.res (some none) ∗ tailErrPostNoPool) ⊢
              runResAt A.repAlloc cliWrOk g.res (some none) ∗
                tailErrPost (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st2) sf := by
            dsimp only [tailErrPost, tailErrPostNoPool]; exact Entails.of_eq (by sep_ac_rfl)
          exact sepWPp_weaken_pre hback
            (r2pb_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin_f
              (by rw [hcs_f.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19_2)
              htr_f hhist_f
              (r2_ans_of_trace_eq htr_eq hans_s2)
              henv1 hrej)
        )
  )

set_option maxHeartbeats 800000 in
theorem r2pb_step_chk_copy_sig [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {ws dst0 : r2_SlotWords} {s0 s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hw0 : ws.w0 = ctSignalTag)
    (hnext : ∀ s' : State,
      s'.trace = s.trace →
      s'.fs = s.fs →
      InRunPlaced r2p_CodeOk s0 s' 1476 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          A.pool lim st s' ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) dst0 ∗
        A.pool lim st s ∗ F)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 1308 := hin.pc; change s.pc = (blkPl_579).base + 1308#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  have hw0_val : ws.w0 = 0x8000000000000000#64 := hw0
  have hs_eq2 : ConditionHolds .EQ (addsPState64 0x8000000000000000#64 2#64) = false := by r2pb_cond
  have hs_ne2 : ConditionHolds .NE (addsPState64 0x8000000000000000#64 2#64) = true := by r2pb_cond
  have hs_eq1 : ConditionHolds .EQ (addsPState64 0x8000000000000000#64 1#64) = false := by r2pb_cond
  have hs_ne1 : ConditionHolds .NE (addsPState64 0x8000000000000000#64 1#64) = true := by r2pb_cond
  have hmi_s : ConditionHolds .MI (subsPState64 0x8000000000000000#64 0#64) = true := by r2pb_cond
  have hpl_s : ConditionHolds .PL (subsPState64 0x8000000000000000#64 0#64) = false := by r2pb_cond
  have hgt_s : ConditionHolds .GT (subsPState64 0#64 1#64) = false := by r2pb_cond
  have hle_s : ConditionHolds .LE (subsPState64 0#64 1#64) = true := by r2pb_cond
  apply r2pb_seq_lscro_oom (mid := runPcPlaced 1476) hin.inv
  unfold r2_words31
  rw [hw0_val, ← r2_hold_eq (A.pool lim st s ∗ F)]
  rw [← hin.sp] at hx22 hx26 hx27 ⊢
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx22 hx26 hx27 ⊢)
  rw [runPcPlaced_eq]
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
    change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
    rw [hin.sp, r2_hold_eq]
    rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
    have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 1476 :=
      r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
    refine sepWPp_weaken_pre
      (P' := r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗
        A.pool lim st (r2pb_stOf hinv1) ∗ F)
      (by
        unfold r2_words31; rw [hw0_val]
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
        exact Entails.of_eq (by sep_ac_rfl))
      (hnext (r2pb_stOf hinv1) (by r2pb_eq) (by r2pb_eq) hin1
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_eq))
  )

set_option maxHeartbeats 800000 in
theorem r2pb_step_chk_copy_pk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {ws dst0 : r2_SlotWords} {s0 s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hw0 : ws.w0.toNat < 2 ^ 63)
    (hnext : ∀ s' : State,
      s'.trace = s.trace →
      s'.fs = s.fs →
      InRunPlaced r2p_CodeOk s0 s' 3792 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          A.pool lim st s' ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) dst0 ∗
        A.pool lim st s ∗ F)
      Q Qp oom := by
  have hz2 : (ws.w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
  have hnz2 : (ws.w0 + 2#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hz1 : (ws.w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
  have hnz1 : (ws.w0 + 1#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have heq2 : ConditionHolds .EQ (addsPState64 ws.w0 2#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact hz2
  have hne2 : ConditionHolds .NE (addsPState64 ws.w0 2#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact hnz2
  have heq1 : ConditionHolds .EQ (addsPState64 ws.w0 1#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact hz1
  have hne1 : ConditionHolds .NE (addsPState64 ws.w0 1#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact hnz1
  have hmsb : ws.w0.msb = false := by bv_bits
  have hmsb0 : (ws.w0 - 0#64).msb = false := by rw [BitVec.sub_zero]; exact hmsb
  have hbit63 : ws.w0.getLsbD 63 = false := by bv_bits
  have hmi : ConditionHolds .MI (subsPState64 ws.w0 0#64) = false := by
    rw [conditionHolds_mi_subsPState64]; exact hmsb0
  have hpl : ConditionHolds .PL (subsPState64 ws.w0 0#64) = true := by
    rw [conditionHolds_pl_subsPState64, hmsb0]; rfl
  have hgt_p : ConditionHolds .GT (subsPState64 1#64 1#64) = false := by r2pb_cond
  have hle_p : ConditionHolds .LE (subsPState64 1#64 1#64) = true := by r2pb_cond
  have hpc : s.pc = runPcPlaced 1308 := hin.pc; change s.pc = (blkPl_579).base + 1308#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  apply r2pb_seq_lscro_oom (mid := runPcPlaced 3792) hin.inv
  unfold r2_words31
  rw [← r2_hold_eq (A.pool lim st s ∗ F)]
  rw [← hin.sp] at hx22 hx26 hx27 ⊢
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx22 hx26 hx27 ⊢)
  rw [runPcPlaced_eq]
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
    change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
    rw [hin.sp, r2_hold_eq]
    rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
    have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 3792 :=
      r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
    refine sepWPp_weaken_pre
      (P' := r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗
        A.pool lim st (r2pb_stOf hinv1) ∗ F)
      (by
        unfold r2_words31
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
        exact Entails.of_eq (by sep_ac_rfl))
      (hnext (r2pb_stOf hinv1) (by r2pb_eq) (by r2pb_eq) hin1
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_eq))
  )

set_option maxHeartbeats 800000 in
theorem r2pb_sig_free_ct [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {i : Inputs} {ws : r2_SlotWords} {s0 s : State} {sub : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1532)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRunPlaced r2p_CodeOk s0 sf 1552 →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          A.pool lim (M.stepEvents (r2pbFreeSliceEvs ws.w5) st) sf ∗
          stackAt (runFsp s0) sub ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
        sliceDeallocX A.repAlloc ws.w4 ws.w5 ∗
        A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 1532 := hin.pc; change s.pc = (blkPl_579).base + 1532#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  unfold sliceDeallocX
  by_cases hzero : ws.w5 = 0#64
  · simp only [hzero, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply r2pb_seq_lscro_oom (mid := runPcPlaced 1552) hin.inv
    unfold r2_words31
    rw [hzero, ← r2_hold_eq (A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F), ← hin.sp, runPcPlaced_eq]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [hin.sp, r2_hold_eq]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 1552 :=
        r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
          (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
      have hst0 : M.stepEvents (r2pbFreeSliceEvs ws.w5) st = st := by
        simp [r2pbFreeSliceEvs, hzero]
      refine sepWPp_weaken_pre
        (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          A.pool lim (M.stepEvents (r2pbFreeSliceEvs ws.w5) st) (r2pb_stOf hinv1) ∗
          stackAt (runFsp s0) sub ∗ F)
        (by
          unfold r2_words31; rw [hst0, hzero]
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext (r2pb_stOf hinv1) (by r2pb_eq) hin1
          (by dsimp only [r2pb_stOf]; unfold CalleeSavedPreserved; simp [calleeSavedVRegs, wp_norm, arm64_norm])
          (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
          (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq)))
    )
  · have hbeq : (ws.w5 == 0#64) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    have hpull :
        r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          (⌜0 < ws.w5.toNat ∧ ws.w5.toNat < 2 ^ 63⌝ ∗ A.repAlloc.live ws.w4 ws.w5.toNat 1 ∗
            memRegion ws.w4 ws.w5.toNat) ∗
          A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F =
        ⌜0 < ws.w5.toNat ∧ ws.w5.toNat < 2 ^ 63⌝ ∗
          (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
            (A.live ws.w4 ws.w5.toNat 1 ∗ memRegion ws.w4 ws.w5.toNat ∗
              A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F)) := by
      dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, hlt⟩
    apply r2pb_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hin.inv
    unfold r2_words31
    rw [← r2_hold_eq (A.live ws.w4 ws.w5.toNat 1 ∗ _), ← hin.sp]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [hin.sp, r2_hold_eq]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      refine sepWPp_weaken_pre
        (P' := A.live ws.w4 ws.w5.toNat 1 ∗ memRegion ws.w4 ws.w5.toNat ∗
          A.pool lim st (r2pb_stOf hinv1) ∗ stackAt (runFsp s0) sub ∗
          (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F))
        (by
          unfold r2_words31
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine r2pb_call_dealloc (nextOff := 1552) hh hextNeed hsub64 hin hinv1
        (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_pc_done)
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq)
        hpos hlt
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq))
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hcsm' : CalleeSavedPreserved s sf :=
        r2_csm_trans
          (by dsimp only [r2pb_stOf]; unfold CalleeSavedPreserved; simp [calleeSavedVRegs, wp_norm, arm64_norm])
          hcsm
      have hst1 : M.stepEvents (r2pbFreeSliceEvs ws.w5) st =
          M.stepEvents (rustDeallocEvents ws.w5.toNat 1) st := by
        simp [r2pbFreeSliceEvs, hzero]
      have hback :
          A.pool lim (M.stepEvents (rustDeallocEvents ws.w5.toNat 1) st) sf ∗
            stackAt (runFsp s0) sub ∗ (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F) ⊢
          r2_words31 (runFsp s0 + 0x1750#64) ws ∗
            A.pool lim (M.stepEvents (r2pbFreeSliceEvs ws.w5) st) sf ∗
            stackAt (runFsp s0) sub ∗ F := by
        rw [hst1]; exact Entails.of_eq (by sep_ac_rfl)
      exact sepWPp_weaken_pre hback
        (hnext sf (htr_eq.trans (by r2pb_eq)) hin_f hcsm' htr_f hhist_f)
    )

set_option maxHeartbeats 800000 in
theorem r2pb_sig_free_pq [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {i : Inputs} {ws : r2_SlotWords} {s0 s : State} {sub : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1552)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRunPlaced r2p_CodeOk s0 sf 1572 →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          A.pool lim (M.stepEvents (r2pbFreeSliceEvs ws.w1) st) sf ∗
          stackAt (runFsp s0) sub ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
        sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗
        A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 1552 := hin.pc; change s.pc = (blkPl_579).base + 1552#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  unfold sliceDeallocX
  by_cases hzero : ws.w1 = 0#64
  · simp only [hzero, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply r2pb_seq_lscro_oom (mid := runPcPlaced 1572) hin.inv
    unfold r2_words31
    rw [hzero, ← r2_hold_eq (A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F), ← hin.sp, runPcPlaced_eq]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [hin.sp, r2_hold_eq]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 1572 :=
        r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
          (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
      have hst0 : M.stepEvents (r2pbFreeSliceEvs ws.w1) st = st := by
        simp [r2pbFreeSliceEvs, hzero]
      refine sepWPp_weaken_pre
        (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          A.pool lim (M.stepEvents (r2pbFreeSliceEvs ws.w1) st) (r2pb_stOf hinv1) ∗
          stackAt (runFsp s0) sub ∗ F)
        (by
          unfold r2_words31; rw [hst0, hzero]
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext (r2pb_stOf hinv1) (by r2pb_eq) hin1
          (by dsimp only [r2pb_stOf]; unfold CalleeSavedPreserved; simp [calleeSavedVRegs, wp_norm, arm64_norm])
          (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
          (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq)))
    )
  · have hbeq : (ws.w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    apply r2pb_peel_pure_tc; rintro ⟨hpos, hlt⟩; simp only [emp_sepConj, sepConj_assoc]
    apply r2pb_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hin.inv
    unfold r2_words31
    rw [← r2_hold_eq (A.repAlloc.live ws.w2 ws.w1.toNat 1 ∗ _), ← hin.sp]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [hin.sp, r2_hold_eq]
      dsimp only [RustCliAllocBudget.repAlloc]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      refine sepWPp_weaken_pre
        (P' := A.live ws.w2 ws.w1.toNat 1 ∗ memRegion ws.w2 ws.w1.toNat ∗
          A.pool lim st (r2pb_stOf hinv1) ∗ stackAt (runFsp s0) sub ∗
          (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F))
        (by
          unfold r2_words31
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine r2pb_call_dealloc (nextOff := 1572) hh hextNeed hsub64 hin hinv1
        (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_pc_done)
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq)
        hpos hlt
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq))
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hcsm' : CalleeSavedPreserved s sf :=
        r2_csm_trans
          (by dsimp only [r2pb_stOf]; unfold CalleeSavedPreserved; simp [calleeSavedVRegs, wp_norm, arm64_norm])
          hcsm
      have hst1 : M.stepEvents (r2pbFreeSliceEvs ws.w1) st =
          M.stepEvents (rustDeallocEvents ws.w1.toNat 1) st := by
        simp [r2pbFreeSliceEvs, hzero]
      have hback :
          A.pool lim (M.stepEvents (rustDeallocEvents ws.w1.toNat 1) st) sf ∗
            stackAt (runFsp s0) sub ∗ (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F) ⊢
          r2_words31 (runFsp s0 + 0x1750#64) ws ∗
            A.pool lim (M.stepEvents (r2pbFreeSliceEvs ws.w1) st) sf ∗
            stackAt (runFsp s0) sub ∗ F := by
        rw [hst1]; exact Entails.of_eq (by sep_ac_rfl)
      exact sepWPp_weaken_pre hback
        (hnext sf (htr_eq.trans (by r2pb_eq)) hin_f hcsm' htr_f hhist_f)
    )

set_option maxHeartbeats 800000 in
theorem r2pb_sig_free_ad [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {i : Inputs} {ws : r2_SlotWords} {s0 s : State} {sub : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1572)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRunPlaced r2p_CodeOk s0 sf 1596 →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          A.pool lim (M.stepEvents (r2pbFreeOptSliceEvs ws.w12 ws.w13) st) sf ∗
          stackAt (runFsp s0) sub ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
        optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗
        A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 1572 := hin.pc; change s.pc = (blkPl_579).base + 1572#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  unfold optSliceDeallocX
  by_cases hp0 : ws.w12 = 0#64
  · simp only [hp0, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply r2pb_seq_lscro_oom (mid := runPcPlaced 1596) hin.inv
    unfold r2_words31
    rw [hp0, ← r2_hold_eq (A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F), ← hin.sp, runPcPlaced_eq]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [hin.sp, r2_hold_eq]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 1596 :=
        r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
          (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
      have hst0 : M.stepEvents (r2pbFreeOptSliceEvs ws.w12 ws.w13) st = st := by
        simp [r2pbFreeOptSliceEvs, hp0]
      refine sepWPp_weaken_pre
        (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          A.pool lim (M.stepEvents (r2pbFreeOptSliceEvs ws.w12 ws.w13) st) (r2pb_stOf hinv1) ∗
          stackAt (runFsp s0) sub ∗ F)
        (by
          unfold r2_words31; rw [hst0, hp0]
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext (r2pb_stOf hinv1) (by r2pb_eq) hin1
          (by dsimp only [r2pb_stOf]; unfold CalleeSavedPreserved; simp [calleeSavedVRegs, wp_norm, arm64_norm])
          (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
          (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq)))
    )
  · have hbeqp : (ws.w12 == 0#64) = false := beq_eq_false_iff_ne.mpr hp0
    simp only [hbeqp, Bool.false_eq_true, ↓reduceIte]
    unfold sliceDeallocX
    by_cases hl0 : ws.w13 = 0#64
    · simp only [hl0, beq_self_eq_true, ↓reduceIte, emp_sepConj]
      apply r2pb_seq_lscro_oom (mid := runPcPlaced 1596) hin.inv
      unfold r2_words31
      rw [hl0, ← r2_hold_eq (A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F), ← hin.sp, runPcPlaced_eq]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
        change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
        rw [hin.sp, r2_hold_eq]
        rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
        have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 1596 :=
          r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
            (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
        have hst0 : M.stepEvents (r2pbFreeOptSliceEvs ws.w12 ws.w13) st = st := by
          simp [r2pbFreeOptSliceEvs, r2pbFreeSliceEvs, hp0, hl0]
        refine sepWPp_weaken_pre
          (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗
            A.pool lim (M.stepEvents (r2pbFreeOptSliceEvs ws.w12 ws.w13) st) (r2pb_stOf hinv1) ∗
            stackAt (runFsp s0) sub ∗ F)
          (by
            unfold r2_words31; rw [hst0, hl0]
            (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
            exact Entails.of_eq (by sep_ac_rfl))
          (hnext (r2pb_stOf hinv1) (by r2pb_eq) hin1
            (by dsimp only [r2pb_stOf]; unfold CalleeSavedPreserved; simp [calleeSavedVRegs, wp_norm, arm64_norm])
            (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
            (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq)))
      )
    · have hbeql : (ws.w13 == 0#64) = false := beq_eq_false_iff_ne.mpr hl0
      simp only [hbeql, Bool.false_eq_true, ↓reduceIte]
      apply r2pb_peel_pure_tc; rintro ⟨hpos, hlt⟩; simp only [emp_sepConj, sepConj_assoc]
      apply r2pb_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hin.inv
      unfold r2_words31
      rw [← r2_hold_eq (A.repAlloc.live ws.w12 ws.w13.toNat 1 ∗ _), ← hin.sp]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
        change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
        rw [hin.sp, r2_hold_eq]
        dsimp only [RustCliAllocBudget.repAlloc]
        rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
        refine sepWPp_weaken_pre
          (P' := A.live ws.w12 ws.w13.toNat 1 ∗ memRegion ws.w12 ws.w13.toNat ∗
            A.pool lim st (r2pb_stOf hinv1) ∗ stackAt (runFsp s0) sub ∗
            (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F))
          (by
            unfold r2_words31
            (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
            exact Entails.of_eq (by sep_ac_rfl)) ?_
        refine r2pb_call_dealloc (nextOff := 1596) hh hextNeed hsub64 hin hinv1
          (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
          (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_pc_done)
          (by r2pb_eq) (by r2pb_eq) (by r2pb_eq)
          hpos hlt
          (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
          (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq))
          fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
        have hcsm' : CalleeSavedPreserved s sf :=
          r2_csm_trans
            (by dsimp only [r2pb_stOf]; unfold CalleeSavedPreserved; simp [calleeSavedVRegs, wp_norm, arm64_norm])
            hcsm
        have hst1 : M.stepEvents (r2pbFreeOptSliceEvs ws.w12 ws.w13) st =
            M.stepEvents (rustDeallocEvents ws.w13.toNat 1) st := by
          simp [r2pbFreeOptSliceEvs, r2pbFreeSliceEvs, hp0, hl0]
        have hback :
            A.pool lim (M.stepEvents (rustDeallocEvents ws.w13.toNat 1) st) sf ∗
              stackAt (runFsp s0) sub ∗ (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F) ⊢
            r2_words31 (runFsp s0 + 0x1750#64) ws ∗
              A.pool lim (M.stepEvents (r2pbFreeOptSliceEvs ws.w12 ws.w13) st) sf ∗
              stackAt (runFsp s0) sub ∗ F := by
          rw [hst1]; exact Entails.of_eq (by sep_ac_rfl)
        exact sepWPp_weaken_pre hback
          (hnext sf (htr_eq.trans (by r2pb_eq)) hin_f hcsm' htr_f hhist_f)
      )

set_option maxHeartbeats 800000 in
theorem r2pb_sig_free_ser [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {i : Inputs} {serPtr serLen : BitVec 64} {s0 s : State} {sub : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1596)
    (hx23 : s.readReg64 (.gpr 23#5) = serPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = serLen)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRunPlaced r2p_CodeOk s0 sf 3940 →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (A.pool lim (M.stepEvents (r2pbFreeSliceEvs serLen) st) sf ∗
          stackAt (runFsp s0) sub ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (sliceDeallocX A.repAlloc serPtr serLen ∗
        A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 1596 := hin.pc; change s.pc = (blkPl_579).base + 1596#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  unfold sliceDeallocX
  by_cases hzero : serLen = 0#64
  · simp only [hzero, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply r2pb_seq_lscro_oom (mid := runPcPlaced 3940) hin.inv
    rw [← r2_hold_eq (A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F), runPcPlaced_eq]
    have hx24_0 : s.readReg64 (.gpr 24#5) = 0#64 := hx24.trans hzero
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [r2_hold_eq]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 3940 :=
        r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
          (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
      have hst0 : M.stepEvents (r2pbFreeSliceEvs serLen) st = st := by
        simp [r2pbFreeSliceEvs, hzero]
      rw [← hst0]
      exact hnext (r2pb_stOf hinv1) (by r2pb_eq) hin1
        (by dsimp only [r2pb_stOf]; unfold CalleeSavedPreserved; simp [calleeSavedVRegs, wp_norm, arm64_norm])
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq))
    )
  · have hbeq : (serLen == 0#64) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWPp.pure_left; rintro ⟨hpos, hlt⟩
    have hx24_b : (s.readReg64 (.gpr 24#5) == 0#64) = false := hx24.symm ▸ hbeq
    apply r2pb_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hin.inv
    rw [← r2_hold_eq (A.repAlloc.live serPtr serLen.toNat 1 ∗ _)]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [r2_hold_eq]
      dsimp only [RustCliAllocBudget.repAlloc]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      have hassoc :
          A.live serPtr serLen.toNat 1 ∗ (memRegion serPtr serLen.toNat ∗
            (A.pool lim st (r2pb_stOf hinv1) ∗ stackAt (runFsp s0) sub ∗ F)) =
          A.live serPtr serLen.toNat 1 ∗ memRegion serPtr serLen.toNat ∗
            A.pool lim st (r2pb_stOf hinv1) ∗ stackAt (runFsp s0) sub ∗ F := by sep_ac_rfl
      rw [hassoc]
      refine r2pb_call_dealloc (nextOff := 3940) hh hextNeed hsub64 hin hinv1
        (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_pc_done)
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); try exact hx23)
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); try exact hx24)
        (by r2pb_eq) hpos hlt
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq))
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hcsm' : CalleeSavedPreserved s sf :=
        r2_csm_trans
          (by dsimp only [r2pb_stOf]; unfold CalleeSavedPreserved; simp [calleeSavedVRegs, wp_norm, arm64_norm])
          hcsm
      have hst1 : M.stepEvents (r2pbFreeSliceEvs serLen) st =
          M.stepEvents (rustDeallocEvents serLen.toNat 1) st := by
        simp [r2pbFreeSliceEvs, hzero]
      rw [← hst1]
      exact hnext sf (htr_eq.trans (by r2pb_eq)) hin_f hcsm' htr_f hhist_f
    )

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudgetAux
