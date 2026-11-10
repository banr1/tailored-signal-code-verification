/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2StepsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2Placed
public meta import Lean
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
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
# `signal_session::run` Placed Send Arm (`run_hop_send_placed_ok`)

Relocatable (`[LibsignalPlacement]`) proof of `run_hop_send_placed_ok` (`RunHopSendPlaced`) on
Block `579` (`runProgPlaced H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff r2_hold
attribute [local arm64_norm, local wp_norm]
  ProofLib.bv_sub_add_lit BitVec.toNat_zero r2p_vregs_0 r2p_vregs_1 r2p_vregs_2
attribute [-arm64_norm]
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

local macro (priority := high) "r2p_eq" : tactic =>
  `(tactic| ((try simp only [arm64_norm]); (try rfl)))

private class R2pPeel (P : SepProp) (α : outParam Type) (R : outParam (α → SepProp)) : Prop where
  entails : P ⊢ ∃∗ x : α, R x
private instance (priority := 100) {α : Type} {P : α → SepProp} : R2pPeel (∃∗ x : α, P x) α P := ⟨Entails.refl _⟩
private instance (priority := 90) {α : Type} {A B : SepProp} {R : α → SepProp} [h : R2pPeel A α R] :
    R2pPeel (A ∗ B) α (fun x => R x ∗ B) := ⟨by rw [← sepExists_sepConj_left]; exact sepConj_mono_left h.entails⟩
private instance (priority := 80) {α : Type} {A B : SepProp} {R : α → SepProp} [h : R2pPeel B α R] :
    R2pPeel (A ∗ B) α (fun x => A ∗ R x) := ⟨by rw [← sepExists_sepConj_right]; exact sepConj_mono_right h.entails⟩
private theorem r2p_peel_tc {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {R : α → SepProp} [h : R2pPeel P α R] {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (k : ∀ x : α, SepWPp prog ret s (R x) Q Qp oom) : SepWPp prog ret s P Q Qp oom :=
  sepWPp_weaken_pre h.entails (r2_sepWPp_exists_left k)

private class R2pPeelPure (P : SepProp) (φ : outParam Prop) (R : outParam SepProp) : Prop where
  entails : P ⊢ ⌜φ⌝ ∗ R
private instance (priority := 100) {φ : Prop} : R2pPeelPure ⌜φ⌝ φ emp := ⟨Entails.of_eq (sepConj_emp _).symm⟩
private instance (priority := 90) {φ : Prop} {A B R : SepProp} [h : R2pPeelPure A φ R] :
    R2pPeelPure (A ∗ B) φ (R ∗ B) := ⟨Entails.trans (sepConj_mono_left h.entails) (Entails.of_eq (sepConj_assoc _ _ _))⟩
private instance (priority := 80) {φ : Prop} {A B R : SepProp} [h : R2pPeelPure B φ R] :
    R2pPeelPure (A ∗ B) φ (A ∗ R) := ⟨Entails.trans (sepConj_mono_right h.entails) (Entails.of_eq (sepConj_left_comm _ _ _))⟩
private theorem r2p_peel_pure_tc {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P R : SepProp} [h : R2pPeelPure P φ R] {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (k : φ → SepWPp prog ret s R Q Qp oom) : SepWPp prog ret s P Q Qp oom :=
  sepWPp_weaken_pre h.entails (SepWPp.pure_left k)

set_option maxHeartbeats 800000 in
theorem r2p_sig_free_pq [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {i : Inputs} {ws : r2_SlotWords} {s0 s : State} {sub : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1552) (htr : s0.trace <+: s.trace) (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State, sf.trace = s.trace → InRunPlaced r2p_CodeOk s0 sf 1572 →
      CalleeSavedPreserved s sf → s0.trace <+: sf.trace → RunHistOk i s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 1552 := hin.pc; change s.pc = (blkPl_579).base + 1552#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  unfold DropPreKeyMsgHelpers.sliceDeallocX
  by_cases hzero : ws.w1 = 0#64
  · simp only [hzero, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 1572) hin.inv
    unfold r2_words31; rw [hzero, ← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F), ← hin.sp]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    rw [hin.sp, r2_hold_eq]; intro hinv1
    have hin1 : InRunPlaced r2p_CodeOk s0 _ 1572 :=
      r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0]) (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
    refine sepWPp_weaken_pre
      (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      (by unfold r2_words31; rw [hzero]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
      (hnext _ (by r2p_eq) hin1 (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
        (by (try simp only [arm64_norm]); exact htr) (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq)))
  · have hbeq : (ws.w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    apply r2p_peel_pure_tc; rintro ⟨hpos, hlt⟩; simp only [emp_sepConj, sepConj_assoc]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hin.inv
    unfold r2_words31; rw [← r2_hold_eq (A.live ws.w2 ws.w1.toNat 1 ∗ _), ← hin.sp]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    rw [hin.sp, r2_hold_eq]; intro hinv1
    refine sepWPp_weaken_pre
      (P' := A.live ws.w2 ws.w1.toNat 1 ∗ memRegion ws.w2 ws.w1.toNat ∗ A.pool ∗ stackAt (runFsp s0) sub ∗
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F))
      (by unfold r2_words31; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl)) ?_
    refine r2p_call_dealloc (nextOff := 1572) hh hextNeed hsub64 hin hinv1
      (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_pc_done) (by r2p_eq) (by r2p_eq) (by r2p_eq)
      hpos hlt (by (try simp only [arm64_norm]); exact htr)
      (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq))
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hcsm' : CalleeSavedPreserved s sf :=
      r2_csm_trans (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm]) hcsm
    exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl)) (hnext sf htr_eq hin_f hcsm' htr_f hhist_f)

set_option maxHeartbeats 800000 in
theorem r2p_sig_free_ad [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {i : Inputs} {ws : r2_SlotWords} {s0 s : State} {sub : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1572) (htr : s0.trace <+: s.trace) (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State, sf.trace = s.trace → InRunPlaced r2p_CodeOk s0 sf 1596 →
      CalleeSavedPreserved s sf → s0.trace <+: sf.trace → RunHistOk i s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 1572 := hin.pc; change s.pc = (blkPl_579).base + 1572#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  unfold DropPreKeyMsgHelpers.optSliceDeallocX
  by_cases hp0 : ws.w12 = 0#64
  · simp only [hp0, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 1596) hin.inv
    unfold r2_words31; rw [hp0, ← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F), ← hin.sp]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    rw [hin.sp, r2_hold_eq]; intro hinv1
    have hin1 : InRunPlaced r2p_CodeOk s0 _ 1596 :=
      r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0]) (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
    refine sepWPp_weaken_pre
      (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      (by unfold r2_words31; rw [hp0]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
      (hnext _ (by r2p_eq) hin1 (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
        (by (try simp only [arm64_norm]); exact htr) (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq)))
  · have hbeqp : (ws.w12 == 0#64) = false := beq_eq_false_iff_ne.mpr hp0
    simp only [hbeqp, Bool.false_eq_true, ↓reduceIte]
    unfold DropPreKeyMsgHelpers.sliceDeallocX
    by_cases hl0 : ws.w13 = 0#64
    · simp only [hl0, beq_self_eq_true, ↓reduceIte, emp_sepConj]
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 1596) hin.inv
      unfold r2_words31; rw [hl0, ← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F), ← hin.sp]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      r2p_step_run
      apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      rw [hin.sp, r2_hold_eq]; intro hinv1
      have hin1 : InRunPlaced r2p_CodeOk s0 _ 1596 :=
        r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0]) (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
      refine sepWPp_weaken_pre
        (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
        (by unfold r2_words31; rw [hl0]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
        (hnext _ (by r2p_eq) hin1 (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
          (by (try simp only [arm64_norm]); exact htr) (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq)))
    · have hbeql : (ws.w13 == 0#64) = false := beq_eq_false_iff_ne.mpr hl0
      simp only [hbeql, Bool.false_eq_true, ↓reduceIte]
      apply r2p_peel_pure_tc; rintro ⟨hpos, hlt⟩; simp only [emp_sepConj, sepConj_assoc]
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hin.inv
      unfold r2_words31; rw [← r2_hold_eq (A.live ws.w12 ws.w13.toNat 1 ∗ _), ← hin.sp]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      r2p_step_run
      apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      rw [hin.sp, r2_hold_eq]; intro hinv1
      refine sepWPp_weaken_pre
        (P' := A.live ws.w12 ws.w13.toNat 1 ∗ memRegion ws.w12 ws.w13.toNat ∗ A.pool ∗ stackAt (runFsp s0) sub ∗
          (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F))
        (by unfold r2_words31; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl)) ?_
      refine r2p_call_dealloc (nextOff := 1596) hh hextNeed hsub64 hin hinv1
        (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
        (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_pc_done) (by r2p_eq) (by r2p_eq) (by r2p_eq)
        hpos hlt (by (try simp only [arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq))
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hcsm' : CalleeSavedPreserved s sf :=
        r2_csm_trans (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm]) hcsm
      exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl)) (hnext sf htr_eq hin_f hcsm' htr_f hhist_f)

set_option maxHeartbeats 800000 in
theorem r2p_sig_free_ser [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {i : Inputs} {serPtr serLen : BitVec 64} {s0 s : State} {sub : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
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
        (A.pool ∗ stackAt (runFsp s0) sub ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (DropPreKeyMsgHelpers.sliceDeallocX A serPtr serLen ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 1596 := hin.pc; change s.pc = (blkPl_579).base + 1596#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  unfold DropPreKeyMsgHelpers.sliceDeallocX
  by_cases hzero : serLen = 0#64
  · simp only [hzero, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 3940) hin.inv
    rw [← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F)]
    have hx24_0 : s.readReg64 (.gpr 24#5) = 0#64 := hx24.trans hzero
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    rw [r2_hold_eq]
    have hin1 : InRunPlaced r2p_CodeOk s0 _ 3940 :=
      r2p_inRun_mk hin (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
        (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
    exact hnext _ (by r2p_eq) hin1
      (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
      (by (try simp only [arm64_norm]); exact htr)
      (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq))
  · have hbeq : (serLen == 0#64) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWPp.pure_left; rintro ⟨hpos, hlt⟩
    have hx24_b : (s.readReg64 (.gpr 24#5) == 0#64) = false := hx24.symm ▸ hbeq
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hin.inv
    rw [← r2_hold_eq (A.live serPtr serLen.toNat 1 ∗ _)]
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    intro hinv1
    rw [r2_hold_eq]
    have hassoc :
        A.live serPtr serLen.toNat 1 ∗ (memRegion serPtr serLen.toNat ∗
          (A.pool ∗ stackAt (runFsp s0) sub ∗ F)) =
        A.live serPtr serLen.toNat 1 ∗ memRegion serPtr serLen.toNat ∗
          A.pool ∗ stackAt (runFsp s0) sub ∗ F := by ac_rfl
    rw [hassoc]
    refine r2p_call_dealloc (nextOff := 3940) hh hextNeed hsub64 hin hinv1
      (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      (by r2p_eq) (by r2p_eq) (by r2p_eq) (by r2p_pc_done)
      (by (try simp only [arm64_norm]); try exact hx23)
      (by (try simp only [arm64_norm]); try exact hx24)
      (by r2p_eq) hpos hlt
      (by (try simp only [arm64_norm]); exact htr)
      (r2p_histOk_of_trace_files hhist (by r2p_eq) (by r2p_eq))
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hcsm' : CalleeSavedPreserved s sf :=
      r2_csm_trans (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm]) hcsm
    exact hnext sf htr_eq hin_f hcsm' htr_f hhist_f

set_option maxHeartbeats 800000 in
theorem r2p_sig_arm [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {peerG meG : AddrGhost} {g' : StoresGhost} {m : SignalMessage}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hcatNeed : 96 + extHookStack ≤ resStack - runFrame)
    (hextNeed : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64) (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) (hpanic : PanicK g s0 Qp)
    (hjoin : JoinKPlaced r2p_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (encResAt A (fsp + 0x4d0#64) (.ok (.signalMessage m)) ∗ addrNameHeap A meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let sigTailNoOut : SepProp :=
    addrNameHeap A meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap
  let sigTail : SepProp :=
    memRegion (fsp + 0x208#64) 24 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ sigTailNoOut
  rw [encResAt_ok]; dsimp only [apiEncResultAt]
  have hpull_gm :
      (((fsp + 0x4d0#64) ↦₆₄ ctSignalTag) ∗
          (∃∗ gMsg : SignalMessageGhost, signalMessageAt A gMsg ((fsp + 0x4d0#64) + 8#64) m) ∗
          memRegion ((fsp + 0x4d0#64) + 0x80#64) 120) ∗
        (addrNameHeap A meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ∃∗ gMsg : SignalMessageGhost,
        (((fsp + 0x4d0#64) ↦₆₄ ctSignalTag) ∗ signalMessageAt A gMsg ((fsp + 0x4d0#64) + 8#64) m ∗
          memRegion ((fsp + 0x4d0#64) + 0x80#64) 120) ∗
        memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x2a0#64) 8 ∗ sigTail := by
    dsimp only [sigTail, sigTailNoOut]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; ac_rfl
  rw [hpull_gm]; apply r2_sepWPp_exists_left; intro gMsg
  refine sepWPp_weaken_pre
    (sepConj_mono (r2_open_signalMessage A (fsp + 0x4d0#64) gMsg m)
      (sepConj_mono (r2_memRegion248_open (fsp + 0x1750#64))
        (sepConj_mono_left (r2_tag8_open (fsp + 0x2a0#64))))) ?_
  apply r2p_peel_tc; intro ws; apply r2p_peel_tc; intro _adPtr; apply r2p_peel_tc; intro _adLen
  apply r2p_peel_tc; intro dst0; apply r2p_peel_tc; intro b2a0; apply r2p_peel_pure_tc
  rintro ⟨hw0, hw1, hw2, hw4, hw5, hw6, hw7, hw12, hw13, hser_lt, _⟩
  simp only [emp_sepConj, sepConj_assoc]
  rw [← hw4, ← hw5, ← hw2, ← hw1, ← hw12, ← hw13]
  have hcopy_pre :
      r2_words31 (fsp + 0x4d0#64) ws ∗ (gMsg.serPtr ↦ₛ m.serialized) ∗
        r2_boxLive A gMsg.serPtr m.serialized ∗ DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗ DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
        r2_words31 (fsp + 0x1750#64) dst0 ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ sigTail =
      r2_words31 (fsp + 0x4d0#64) ws ∗ r2_words31 (fsp + 0x1750#64) dst0 ∗
        (((fsp + 0x2a0#64) ↦₈ b2a0) ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          (gMsg.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A gMsg.serPtr m.serialized ∗
          DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗ DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
          DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗ sigTail) := by ac_rfl
  rw [hcopy_pre]
  refine r2p_step_chk_copy_sig hin hx22 hx26 hx27 hw0
    fun s1 htr1 hfs1 hin1 hx19_1 hx20_1 hx21_1 hx28_1 => ?_
  have htr_s1 : s0.trace <+: s1.trace := htr1 ▸ htr
  have hhist_s1 : RunHistOk g.i s0 s1 := r2p_histOk_of_trace_files hhist htr1 (congrArg FsState.files hfs1)
  have hans_s1 : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) := r2_ans_of_trace_eq htr1 hans
  have hopen_4d0 :
      r2_words31 (fsp + 0x4d0#64) ws ⊢
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((fsp + 0x4d0#64) ↦₆₄ c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ c1) ∗
          (((fsp + 0x4d0#64) + 16#64) ↦₆₄ c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ c3)) ∗
        memRegion ((fsp + 0x4d0#64) + 32#64) 216 := by
    refine Entails.trans (r2_words31_to_memRegion248 (fsp + 0x4d0#64) ws) ?_
    rw [ProofLib.memRegion_split (fsp + 0x4d0#64) 32 216 (by decide)]
    exact sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x4d0#64))
  refine sepWPp_weaken_pre (sepConj_mono_left hopen_4d0) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply r2_sepWPp_exists_left; intro _c0; apply r2_sepWPp_exists_left; intro _c1
  apply r2_sepWPp_exists_left; intro _c2; apply r2_sepWPp_exists_left; intro _c3
  have hpc : s1.pc = runPcPlaced 1476 := hin1.pc; change s1.pc = (blkPl_579).base + 1476#64 at hpc
  have hrun1 : s1.status = .Running := hin1.run
  have hsp1_al : s1.spAligned = true := hin1.spAligned_cur
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := (blkPl_598).base) hin1.inv
  rw [← r2_hold_eq (memRegion ((fsp + 0x4d0#64) + 32#64) 216),
      ← r2_hold_eq (memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ _)]
  unfold r2_words31; dsimp only [fsp]; rw [← hin1.sp]
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
  r2p_step_run
  apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun1])
  rw [hin1.sp, r2_hold_eq, r2_hold_eq]; intro hinv2; clear hpc
  refine sepWPp_weaken_pre
    (P' := ((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ 1#64) ∗
      (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gMsg.serPtr) ∗
      (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
      SpqrV1.ChainProofs.bytesAt false (fsp + 0x2a0#64) [2#8] ∗
      SpqrV1.ChainProofs.bytesAt false gMsg.serPtr m.serialized ∗
      memRegion (fsp + 0x208#64) 24 ∗ A.pool ∗ stackAt fsp (resStack - runFrame) ∗
      (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
        r2_words31 (fsp + 0x1750#64) ws ∗ r2_boxLive A gMsg.serPtr m.serialized ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
        DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗ sigTailNoOut))
    (by
      unfold r2_words31; dsimp only [fsp, sigTail, sigTailNoOut]
      rw [hw6, hw7, SpqrV1.ChainProofs.bytesAt_false, SpqrV1.ChainProofs.bytesAt_false,
        ProofLib.pointsToBytes_singleton]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact Entails.of_eq (by ac_rfl)) ?_
  have hhist_cat : RunHistOk g.i s0 _ := r2p_histOk_of_trace_files hhist_s1 (by r2p_eq) (by r2p_eq)
  have hans_cat : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) := hans_s1
  let catG : SpqrV1.ChainProofs.SliceConcat2Ghost :=
    ⟨fsp + 0x208#64, fsp + 0x4d0#64, false, fsp + 0x2a0#64, [2#8], false, gMsg.serPtr, m.serialized⟩
  have hcat_call := RunSkeleton.concat_placed_ok (callerProg := runProgPlaced H) (i := 579)
    hh (resStack - runFrame) hcatNeed hsub64
  refine r2p_call (s0 := s0) catG hcat_call hinv2
    (by r2p_pc_done) (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm]; exact hsp1_al)
    (ret_pc := runPcPlaced 1532) (by r2p_pc_done)
    (F := memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
      r2_words31 (fsp + 0x1750#64) ws ∗ r2_boxLive A gMsg.serPtr m.serialized ∗
      DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗ DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
      DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗ sigTailNoOut) ?_
    (hpanic := fun sf R' _ hp => by
      dsimp only [RunProofs.cliConcat2Spec, catG] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inr
        (allocFailedIn_of_prefix htr_s1 (r2_allocFailedIn_of_trace_eq (by r2p_eq) hp.1.1))))
    (hnext := fun s2 hsteps2 hinv_s2 hpcm2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [RunProofs.cliConcat2Spec, catG]; rw [sepConj_assoc]; apply Entails.pure_right
    · exact ⟨by (try simp only [arm64_norm]); (try dsimp only [fsp]); try bv_omega,
             by (try simp only [arm64_norm]); (try dsimp only [fsp]); try bv_omega,
             by r2p_eq, by dsimp only [List.length]; omega⟩
    · (try simp only [arm64_norm]); rw [hin1.sp]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [RunProofs.cliConcat2Spec, catG]; rw [sepConj_assoc]
    apply SepWPp.pure_left; intro htr2
    have hfs2 := r2p_files_of_trace_eq hh hsteps2 htr2
    have htr_s2 : s0.trace <+: s2.trace := by rw [htr2]; (try simp only [arm64_norm]); exact htr_s1
    have hhist_s2 : RunHistOk g.i s0 s2 := r2p_histOk_of_trace_files hhist_cat htr2 hfs2
    have hans_s2 := r2_ans_of_trace_eq htr2 hans_cat
    have hcs2_r := r2p_cs_regs hcs2
    have hin2 : InRunPlaced r2p_CodeOk s0 s2 1532 :=
      r2p_inRun_mk hin1 hpcm2 hrun2 (hsp2.trans (by r2p_eq))
        (hcs2_r.2.2.2.2.2.2.2.2.2.2.1.trans (by r2p_eq)) hinv_s2
        (hcs2_r.2.2.2.2.2.2.2.2.2.2.2.trans (by r2p_eq))
    have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by
      rw [hcs2_r.1]; (try simp only [arm64_norm]); exact hx19_1.trans hx19
    have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by
      rw [hcs2_r.2.1]; (try simp only [arm64_norm]); exact hx20_1.trans hx20
    have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by
      rw [hcs2_r.2.2.1]; (try simp only [arm64_norm]); exact hx21_1.trans hx21
    have hx23_2 : s2.readReg64 (.gpr 23#5) = gMsg.serPtr := by
      rw [hcs2_r.2.2.2.2.1]; simp only [arm64_norm]
    have hx24_2 : s2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 m.serialized.length := by
      rw [hcs2_r.2.2.2.2.2.1]; simp only [arm64_norm]
    have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr := by
      rw [hcs2_r.2.2.2.2.2.2.2.2.2.1]; (try simp only [arm64_norm]); exact hx28_1.trans hx28
    refine sepWPp_weaken_pre (P' :=
        r2_words31 (fsp + 0x1750#64) ws ∗ DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
            DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
            DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut)) ?_ ?_
    · refine Entails.trans (Entails.of_eq (Q :=
          (((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗
              (((fsp + 0x4d0#64) + 8#64) ↦₆₄ BitVec.ofNat 64 ([2#8] : List (BitVec 8)).length) ∗
              (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gMsg.serPtr) ∗
              (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
              memRegion ((fsp + 0x4d0#64) + 32#64) 216) ∗
            (SpqrV1.ChainProofs.bytesAt false (fsp + 0x2a0#64) [2#8] ∗
              memRegion ((fsp + 0x2a0#64) + 1#64) 7) ∗
            ((gMsg.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A gMsg.serPtr m.serialized) ∗
            (r2_words31 (fsp + 0x1750#64) ws ∗ DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
              A.pool ∗ stackAt fsp (resStack - runFrame) ∗ DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
              DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
              vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗ sigTailNoOut)) ?_) ?_
      · rw [SpqrV1.ChainProofs.bytesAt_false gMsg.serPtr m.serialized]
        (try simp only [arm64_norm]); rw [hin1.sp]; dsimp only [fsp, runFsp]; (try simp only [arm64_norm]); ac_rfl
      · refine Entails.trans
          (sepConj_mono (r2_words4_216_rejoin (fsp + 0x4d0#64) _ _ _ _)
            (sepConj_mono (r2_tag8_close (fsp + 0x2a0#64) 2#8)
              (sepConj_mono_left (r2_boxLive_to_sliceDeallocX A gMsg.serPtr m.serialized (by omega)))))
          (Entails.of_eq (by ac_rfl))
    refine r2p_sig_free_ct hh hextNeed hsub64 hin2 htr_s2 hhist_s2 fun s3 htr3 hin3 hcs3 htr_s3 hhist_s3 => ?_
    refine sepWPp_weaken_pre (P' :=
        r2_words31 (fsp + 0x1750#64) ws ∗ DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
            DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut))
      (Entails.of_eq (by ac_rfl)) ?_
    refine r2p_sig_free_pq hh hextNeed hsub64 hin3 htr_s3 hhist_s3 fun s4 htr4 hin4 hcs4 htr_s4 hhist_s4 => ?_
    refine sepWPp_weaken_pre (P' :=
        r2_words31 (fsp + 0x1750#64) ws ∗ DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut))
      (Entails.of_eq (by ac_rfl)) ?_
    refine r2p_sig_free_ad hh hextNeed hsub64 hin4 htr_s4 hhist_s4 fun s5 htr5 hin5 hcs5 htr_s5 hhist_s5 => ?_
    refine sepWPp_weaken_pre (P' :=
        DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (memRegion (fsp + 0x1750#64) 248 ∗ vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut))
      (Entails.trans (sepConj_mono_left (r2_words31_to_memRegion248 (fsp + 0x1750#64) ws))
        (Entails.of_eq (by ac_rfl))) ?_
    have hcs25_r := r2p_cs_regs (r2_csm_trans hcs3 (r2_csm_trans hcs4 hcs5))
    have hans_s5 := r2_ans_of_trace_eq (htr5.trans (htr4.trans htr3)) hans_s2
    refine r2p_sig_free_ser hh hextNeed hsub64 hin5
      (hcs25_r.2.2.2.2.1.trans hx23_2) (hcs25_r.2.2.2.2.2.1.trans hx24_2) htr_s5 hhist_s5
      fun s6 htr6 hin6 hcs6 htr_s6 hhist_s6 => ?_
    have hcs26_r := r2p_cs_regs (r2_csm_trans (r2_csm_trans hcs3 (r2_csm_trans hcs4 hcs5)) hcs6)
    refine sepWPp_weaken_pre (P' :=
        addrNameHeap A meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      (by dsimp only [sigTailNoOut]; exact Entails.of_eq (by ac_rfl))
      (r2p_free_me_peer_join (peerG := peerG) (meG := meG) hh hextNeed hsub64 hin6
        (hcs26_r.1.trans hx19_2) (hcs26_r.2.1.trans hx20_2)
        (hcs26_r.2.2.1.trans hx21_2) (hcs26_r.2.2.2.2.2.2.2.2.2.1.trans hx28_2)
        htr_s6 hhist_s6 (r2_ans_of_trace_eq htr6 hans_s5) hwr hjoin)

set_option maxHeartbeats 800000 in
theorem r2p_pk_arm [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {peerG meG : AddrGhost} {g' : StoresGhost} {m : PreKeySignalMessage}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hcatNeed : 96 + extHookStack ≤ resStack - runFrame)
    (hdpkNeed : 48 + extHookStack ≤ resStack - runFrame)
    (hextNeed : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64) (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) (hser42 : m.serialized.length < 2 ^ 42)
    (hpanic : PanicK g s0 Qp) (hjoin : JoinKPlaced r2p_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (encResAt A (fsp + 0x4d0#64) (.ok (.preKeySignalMessage m)) ∗ addrNameHeap A meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let pkTailNoOut : SepProp :=
    addrNameHeap A meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap
  let pkTail : SepProp :=
    memRegion (fsp + 0x208#64) 24 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ pkTailNoOut
  rw [encResAt_ok]; dsimp only [apiEncResultAt]
  have hpull_gp :
      (∃∗ gPk : PreKeyMsgGhost, preKeyMsgAt A gPk (fsp + 0x4d0#64) m) ∗
        (addrNameHeap A meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ∃∗ gPk : PreKeyMsgGhost,
        preKeyMsgAt A gPk (fsp + 0x4d0#64) m ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x2a0#64) 8 ∗ pkTail := by
    dsimp only [pkTail, pkTailNoOut]; simp only [sepExists_sepConj_left]; ac_rfl
  rw [hpull_gp]; apply r2_sepWPp_exists_left; intro gPk
  refine sepWPp_weaken_pre
    (sepConj_mono (r2_open_preKeyMessage A (fsp + 0x4d0#64) gPk m)
      (sepConj_mono (r2_memRegion248_open (fsp + 0x1750#64))
        (sepConj_mono_left (r2_tag8_open (fsp + 0x2a0#64))))) ?_
  apply r2p_peel_tc; intro ws; apply r2p_peel_tc; intro Hrel; apply r2p_peel_tc; intro dst0
  apply r2p_peel_tc; intro b2a0; apply r2p_peel_pure_tc
  rintro ⟨hw0_lt, hw16, hw17, _, _hser_lt, hclose_pk⟩
  simp only [emp_sepConj, sepConj_assoc]
  have hcopy_pre :
      r2_words31 (fsp + 0x4d0#64) ws ∗ (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel ∗
        r2_words31 (fsp + 0x1750#64) dst0 ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ pkTail =
      r2_words31 (fsp + 0x4d0#64) ws ∗ r2_words31 (fsp + 0x1750#64) dst0 ∗
        (((fsp + 0x2a0#64) ↦₈ b2a0) ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel ∗ pkTail) := by ac_rfl
  rw [hcopy_pre]
  refine r2p_step_chk_copy_pk hin hx22 hx26 hx27 hw0_lt
    fun s1 htr1 hfs1 hin1 hx19_1 hx20_1 hx21_1 hx28_1 => ?_
  have htr_s1 : s0.trace <+: s1.trace := htr1 ▸ htr
  have hhist_s1 : RunHistOk g.i s0 s1 := r2p_histOk_of_trace_files hhist htr1 (congrArg FsState.files hfs1)
  have hans_s1 : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) := r2_ans_of_trace_eq htr1 hans
  have hopen_4d0 :
      r2_words31 (fsp + 0x4d0#64) ws ⊢
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((fsp + 0x4d0#64) ↦₆₄ c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ c1) ∗
          (((fsp + 0x4d0#64) + 16#64) ↦₆₄ c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ c3)) ∗
        memRegion ((fsp + 0x4d0#64) + 32#64) 216 := by
    refine Entails.trans (r2_words31_to_memRegion248 (fsp + 0x4d0#64) ws) ?_
    rw [ProofLib.memRegion_split (fsp + 0x4d0#64) 32 216 (by decide)]
    exact sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x4d0#64))
  refine sepWPp_weaken_pre (sepConj_mono_left hopen_4d0) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply r2_sepWPp_exists_left; intro _c0; apply r2_sepWPp_exists_left; intro _c1
  apply r2_sepWPp_exists_left; intro _c2; apply r2_sepWPp_exists_left; intro _c3
  have hpc : s1.pc = runPcPlaced 3792 := hin1.pc; change s1.pc = (blkPl_579).base + 3792#64 at hpc
  have hrun1 : s1.status = .Running := hin1.run
  have hsp1_al : s1.spAligned = true := hin1.spAligned_cur
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := (blkPl_598).base) hin1.inv
  rw [← r2_hold_eq (memRegion ((fsp + 0x4d0#64) + 32#64) 216),
      ← r2_hold_eq (memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ _)]
  unfold r2_words31; dsimp only [fsp]; rw [← hin1.sp]
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
  r2p_step_run
  apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun1])
  rw [hin1.sp, r2_hold_eq, r2_hold_eq]; intro hinv2; clear hpc
  refine sepWPp_weaken_pre
    (P' := ((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ 1#64) ∗
      (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gPk.serPtr) ∗
      (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
      SpqrV1.ChainProofs.bytesAt false (fsp + 0x2a0#64) [3#8] ∗
      SpqrV1.ChainProofs.bytesAt false gPk.serPtr m.serialized ∗
      memRegion (fsp + 0x208#64) 24 ∗ A.pool ∗ stackAt fsp (resStack - runFrame) ∗
      (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
        r2_words31 (fsp + 0x1750#64) ws ∗ Hrel ∗ pkTailNoOut))
    (by
      unfold r2_words31; dsimp only [fsp, pkTail, pkTailNoOut]
      rw [hw16, hw17, SpqrV1.ChainProofs.bytesAt_false, SpqrV1.ChainProofs.bytesAt_false,
        ProofLib.pointsToBytes_singleton]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact Entails.of_eq (by ac_rfl)) ?_
  have hhist_cat : RunHistOk g.i s0 _ := r2p_histOk_of_trace_files hhist_s1 (by r2p_eq) (by r2p_eq)
  have hans_cat : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) := hans_s1
  let catG : SpqrV1.ChainProofs.SliceConcat2Ghost :=
    ⟨fsp + 0x208#64, fsp + 0x4d0#64, false, fsp + 0x2a0#64, [3#8], false, gPk.serPtr, m.serialized⟩
  have hcat_call := RunSkeleton.concat_placed_ok (callerProg := runProgPlaced H) (i := 579)
    hh (resStack - runFrame) hcatNeed hsub64
  refine r2p_call (s0 := s0) catG hcat_call hinv2
    (by r2p_pc_done) (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm]; exact hsp1_al)
    (ret_pc := runPcPlaced 3848) (by r2p_pc_done)
    (F := memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
      r2_words31 (fsp + 0x1750#64) ws ∗ Hrel ∗ pkTailNoOut) ?_
    (hpanic := fun sf R' _ hp => by
      dsimp only [RunProofs.cliConcat2Spec, catG] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inr
        (allocFailedIn_of_prefix htr_s1 (r2_allocFailedIn_of_trace_eq (by r2p_eq) hp.1.1))))
    (hnext := fun s2 hsteps2 hinv_s2 hpcm2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [RunProofs.cliConcat2Spec, catG]; rw [sepConj_assoc]; apply Entails.pure_right
    · exact ⟨by (try simp only [arm64_norm]); (try dsimp only [fsp]); try bv_omega,
             by (try simp only [arm64_norm]); (try dsimp only [fsp]); try bv_omega,
             by r2p_eq, by dsimp only [List.length]; omega⟩
    · (try simp only [arm64_norm]); rw [hin1.sp]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [RunProofs.cliConcat2Spec, catG]; rw [sepConj_assoc]
    apply SepWPp.pure_left; intro htr2
    have hfs2 := r2p_files_of_trace_eq hh hsteps2 htr2
    have htr_s2 : s0.trace <+: s2.trace := by rw [htr2]; (try simp only [arm64_norm]); exact htr_s1
    have hhist_s2 : RunHistOk g.i s0 s2 := r2p_histOk_of_trace_files hhist_cat htr2 hfs2
    have hans_s2 := r2_ans_of_trace_eq htr2 hans_cat
    have hcs2_r := r2p_cs_regs hcs2
    have hin2 : InRunPlaced r2p_CodeOk s0 s2 3848 :=
      r2p_inRun_mk hin1 hpcm2 hrun2 (hsp2.trans (by r2p_eq))
        (hcs2_r.2.2.2.2.2.2.2.2.2.2.1.trans (by r2p_eq)) hinv_s2
        (hcs2_r.2.2.2.2.2.2.2.2.2.2.2.trans (by r2p_eq))
    have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by
      rw [hcs2_r.1]; (try simp only [arm64_norm]); exact hx19_1.trans hx19
    have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by
      rw [hcs2_r.2.1]; (try simp only [arm64_norm]); exact hx20_1.trans hx20
    have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by
      rw [hcs2_r.2.2.1]; (try simp only [arm64_norm]); exact hx21_1.trans hx21
    have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr := by
      rw [hcs2_r.2.2.2.2.2.2.2.2.2.1]; (try simp only [arm64_norm]); exact hx28_1.trans hx28
    refine sepWPp_weaken_pre (P' :=
        preKeyMsgAt A gPk (fsp + 0x1750#64) m ∗ A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (vecU8 A (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ pkTailNoOut)) ?_ ?_
    · refine Entails.trans (Entails.of_eq (Q :=
          (r2_words31 (fsp + 0x1750#64) ws ∗ (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel) ∗
            (((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗
              (((fsp + 0x4d0#64) + 8#64) ↦₆₄ BitVec.ofNat 64 ([3#8] : List (BitVec 8)).length) ∗
              (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gPk.serPtr) ∗
              (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
              memRegion ((fsp + 0x4d0#64) + 32#64) 216) ∗
            (SpqrV1.ChainProofs.bytesAt false (fsp + 0x2a0#64) [3#8] ∗
              memRegion ((fsp + 0x2a0#64) + 1#64) 7) ∗
            (A.pool ∗ stackAt fsp (resStack - runFrame) ∗
              vecU8 A (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗ pkTailNoOut)) ?_) ?_
      · rw [SpqrV1.ChainProofs.bytesAt_false gPk.serPtr m.serialized]
        (try simp only [arm64_norm]); rw [hin1.sp]; dsimp only [fsp, runFsp]; (try simp only [arm64_norm]); ac_rfl
      · refine Entails.trans
          (sepConj_mono (hclose_pk (fsp + 0x1750#64))
            (sepConj_mono (r2_words4_216_rejoin (fsp + 0x4d0#64) _ _ _ _)
              (sepConj_mono_left (r2_tag8_close (fsp + 0x2a0#64) 3#8))))
          (Entails.of_eq (by ac_rfl))
    have hpc : s2.pc = runPcPlaced 3848 := hin2.pc; change s2.pc = (blkPl_579).base + 3848#64 at hpc
    have hsp2_al : s2.spAligned = true := hin2.spAligned_cur
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := (blkPl_555).base) hin2.inv
    rw [← r2_hold_eq (preKeyMsgAt A gPk (fsp + 0x1750#64) m ∗ _)]
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun2])
    intro hinv3; rw [r2_hold_eq]; clear hpc
    have hdpk_call := RunSkeleton.dropPreKeyMsg_placed_ok (callerProg := runProgPlaced H) (i := 579)
      hh (resStack - runFrame)
      (Nat.le_trans (by decide : 32 + extHookStack ≤ 48 + extHookStack) hdpkNeed) hsub64
    refine r2p_call (s0 := s0) ⟨fsp + 0x1750#64, gPk, m⟩ hdpk_call hinv3
      (by r2p_pc_done) (by simp only [arm64_norm, hrun2]) (by simp only [arm64_norm]; exact hsp2_al)
      (ret_pc := runPcPlaced 3860) (by r2p_pc_done)
      (F := vecU8 A (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗
        memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ pkTailNoOut) ?_
      (hnext := fun s3 hsteps3 hinv_s3 hpcm3 hrun3 hsp3 hcs3 => ?_)
    · dsimp only [RunProofs.dropPreKeyMsgSpec]; rw [sepConj_assoc]
      refine Entails.pure_right (by (try simp only [arm64_norm]); rw [hin1.sp]) ?_
      (try simp only [arm64_norm]); rw [hin2.sp]; dsimp only [fsp, runFsp]; (try simp only [arm64_norm])
      exact Entails.of_eq (by ac_rfl)
    · dsimp only [RunProofs.dropPreKeyMsgSpec]; rw [sepConj_assoc]
      apply SepWPp.pure_left; intro htr3
      have hfs3 := r2p_files_of_trace_eq hh hsteps3 htr3
      have htr_s3 : s0.trace <+: s3.trace := htr3 ▸ (by simpa only [arm64_norm] using htr_s2)
      have hhist_s3 : RunHistOk g.i s0 s3 :=
        r2p_histOk_of_trace_files (r2p_histOk_of_trace_files hhist_s2 (by r2p_eq) (by r2p_eq)) htr3 hfs3
      have hans_s3 := r2_ans_of_trace_eq htr3 hans_s2
      have hcs3_r := r2p_cs_regs hcs3
      have hin3 : InRunPlaced r2p_CodeOk s0 s3 3860 :=
        r2p_inRun_mk hin2 hpcm3 hrun3 (hsp3.trans (by r2p_eq))
          (hcs3_r.2.2.2.2.2.2.2.2.2.2.1.trans (by r2p_eq)) hinv_s3
          (hcs3_r.2.2.2.2.2.2.2.2.2.2.2.trans (by r2p_eq))
      have hpc : s3.pc = runPcPlaced 3860 := hin3.pc; change s3.pc = (blkPl_579).base + 3860#64 at hpc
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 3940) hin3.inv
      rw [← r2_hold_eq ((memRegion (fsp + 0x1750#64) 248 ∗ _) ∗ _)]
      r2p_step_run
      apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun3])
      intro hinv4; rw [r2_hold_eq]
      have hin4 : InRunPlaced r2p_CodeOk s0 _ 3940 :=
        r2p_inRun_mk hin3 (by r2p_pc_done) (by simp only [arm64_norm, hrun3])
          (by r2p_eq) (by r2p_eq) hinv4 (by r2p_eq)
      refine sepWPp_weaken_pre (P' :=
          addrNameHeap A meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            vecU8 A (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
        (by (try simp only [arm64_norm]); rw [hin2.sp]; dsimp only [pkTailNoOut, fsp, runFsp]; (try simp only [arm64_norm]); exact Entails.of_eq (by ac_rfl))
        (r2p_free_me_peer_join (peerG := peerG) (meG := meG) hh hextNeed hsub64 hin4
          (by (try simp only [arm64_norm]); exact hcs3_r.1.trans (by (try simp only [arm64_norm]); exact hx19_2))
          (by (try simp only [arm64_norm]); exact hcs3_r.2.1.trans (by (try simp only [arm64_norm]); exact hx20_2))
          (by (try simp only [arm64_norm]); exact hcs3_r.2.2.1.trans (by (try simp only [arm64_norm]); exact hx21_2))
          (by (try simp only [arm64_norm]); exact hcs3_r.2.2.2.2.2.2.2.2.2.1.trans (by (try simp only [arm64_norm]); exact hx28_2))
          (by (try simp only [arm64_norm]); exact htr_s3)
          (r2p_histOk_of_trace_files hhist_s3 (by r2p_eq) (by r2p_eq))
          hans_s3 hwr hjoin)

def r2p_encInnerSpec [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) : Spec EncGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
      x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.peerA ∧ s.readReg64 .x3 = x.meA ∧
      s.readReg64 .x4 = x.stores + 0xf0#64 ∧ s.readReg64 .x5 = sessVtPlaced ∧
      s.readReg64 .x6 = x.stores ∧ s.readReg64 .x7 = idVtPlaced ∧
      s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
      S.encOk x.F x.peer.val x.coins ∧ stk ≤ s.sp.toNat ∧ x.meA ≠ 0#64⌝ ∗
    slotFramePlaced A x.toSlotCtx ∗ (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s.sp unixEpoch ∗
    memRegion x.ret 248 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) CiphertextMessage,
      ⌜slotTrace s0 sf ∧
        slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf ∧
        (∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
          m.serialized.length < 2 ^ 42)⌝ ∗
      storesAt A x.stores g' ∗ encResAt A x.ret e ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
      stackAt s0.sp stk ∗ anyHeap
  onPanic := fun x s0 sf =>
    ⌜S.encrypt x.F x.peer.val x.me.val x.ptext x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
      anyHeap

set_option maxHeartbeats 1600000 in
theorem run_hop_send_of_slots [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A S needs))
    (henc_eq : slots.encrypt = (slotsOfPlaced A S needs).encrypt) :
    RunHopSendPlacedOf (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S slots resStack := by
  intro g s0 s me peerV Q Qp hh hc hdrop hres hres64 _hspb he hd hcall hpanic hrej hjoin
  rw [hneed_eq] at hres
  obtain ⟨hframeLe, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _, _, hdropNeed, hcatNeed, hextNeed,
    hencNeed, _, _, _, hdpkNeed⟩ := runNeed_bounds_placed hres hres64
  let fsp := runFsp s0
  have hfsp_def : runFsp s0 = fsp := rfl
  have hpc : s.pc = runPcPlaced 532 := hd.base.pc; change s.pc = (blkPl_579).base + 532#64 at hpc
  have hrun0 : s.status = .Running := hd.base.run
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 2#64 := by rw [hd.x8, hcall]; rfl
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  have hd_gt : ConditionHolds .GT (subsPState64 2#64 1#64) = true := by r2p_cond
  have hd_le : ConditionHolds .LE (subsPState64 2#64 1#64) = false := by r2p_cond
  have hs_ne : ConditionHolds .NE (subsPState64 2#64 2#64) = false := by r2p_cond
  have hs_eq : ConditionHolds .EQ (subsPState64 2#64 2#64) = true := by r2p_cond
  have hhist0 : RunHistOk g.i s0 s := ⟨hd.fs, hd.stdout⟩
  refine sepWPp_weaken_pre
    (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
      (sepConj_mono_right (entails_anyHeap emp))) ?_
  cases me with
  | none =>
    have hans_none : g.a = some none := hd.reject_of_me_none he
    have hx20 : s.readReg64 (.gpr 20#5) = g.res := hd.x20
    have hx21_none : s.readReg64 (.gpr 21#5) = 0xffffffffffffffff#64 := hd.meRegs
    have hmn_eq : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by r2p_cond
    have hmn_ne : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 1#64) = false := by r2p_cond
    dsimp only [dispatchMemPlaced, dispatchMeHeap, dispatchCells]
    rw [hfsp_def, hcall, emp_sepConj, r2_locals_none_eq fsp]
    have hopen_none :
        (memRegion g.res runResSize ∗ callAt A g.call (.send peerV) ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
          (memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool) ∗ anyHeap ⊢
        (∃∗ r0 : BitVec 64, (g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        (∃∗ peerG : AddrGhost, ∃∗ cw : CallW,
          ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = cw.w1 ∧ peerG.name.ptr = cw.w2 ∧
            cw.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ cw.w4.setWidth 8 = peerG.device⌝ ∗
          ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
            ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
            ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗ addrNameHeap A peerG) ∗
        (∃∗ p0 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ p3 : BitVec 64,
          ((fsp + 0x320#64) ↦₆₄ p0) ∗ (((fsp + 0x320#64) + 8#64) ↦₆₄ p1) ∗
          (((fsp + 0x320#64) + 16#64) ↦₆₄ p2) ∗ (((fsp + 0x320#64) + 24#64) ↦₆₄ p3)) ∗
        (storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
          memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗
          memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
          r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) := by
      refine Entails.trans (Entails.of_eq (Q :=
          memRegion g.res runResSize ∗ callAt A g.call (.send peerV) ∗ memRegion (fsp + 0x320#64) 32 ∗
            (storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
              coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
              SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗
              memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
              r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)) (by ac_rfl)) ?_
      exact sepConj_mono (r2_res_open g.res)
        (sepConj_mono (r2_callAt_send_unpack A g.call peerV)
          (sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x320#64))))
    refine sepWPp_weaken_pre hopen_none ?_
    apply r2p_peel_tc; intro _r0; apply r2p_peel_tc; intro peerG; apply r2p_peel_tc; intro cw
    apply r2p_peel_tc; intro _p0; apply r2p_peel_tc; intro _p1; apply r2p_peel_tc; intro _p2; apply r2p_peel_tc; intro _p3
    apply r2p_peel_pure_tc; rintro ⟨_, hw1, hw2, _, _⟩
    simp only [emp_sepConj, sepConj_assoc]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 2984) hd.base.inv
    rw [← r2_hold_eq (memRegion (g.res + 8#64) (runResSize - 8)),
        ← r2_hold_eq (addrNameHeap A peerG),
        ← r2_hold_eq (storesAt A g.stores StoresGhost.opened ∗ _)]
    dsimp only [fsp]; rw [← hd.base.sp]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    rw [hd.base.sp, r2_hold_eq, r2_hold_eq, r2_hold_eq]
    intro hinv1
    have hin1 : InRunPlaced r2p_CodeOk s0 _ 2984 :=
      r2p_inRun_mk hd.base (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
        (by r2p_eq) (by r2p_eq) hinv1 (by r2p_eq)
    have hp16 :
        ((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4) ⊢
          memRegion (fsp + 0x330#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x330#64) (n := 8) (k := 8)
            (b' := fsp + 0x338#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    let postNone : SepProp :=
      runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
    refine sepWPp_weaken_pre (P' := postNone) ?_ ?_
    · dsimp only [postNone]; rw [hcall]
      have hres_n := r2_res_write_none A g.res 0xffffffffffffffff#64 rfl
      have hcw_m := r2_callWords_to_memRegion56 g.call cw
      refine Entails.trans (Entails.of_eq (Q :=
          (((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
            ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
              ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
              ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
            (((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4)) ∗
            (coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
              SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ anyHeap) ∗
            (storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
              addrNameHeap A peerG ∗ runSaved s0 ∗
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
              stackAt fsp (resStack - runFrame) ∗ A.pool))) ?_) ?_
      · rw [← hw1, ← hw2]; dsimp only [fsp]; ac_rfl
      · refine Entails.trans (sepConj_mono hres_n (sepConj_mono hcw_m (sepConj_mono hp16
          (sepConj_mono_left (entails_anyHeap _))))) (Entails.of_eq (by ac_rfl))
    · exact r2p_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin1
        (by (try simp only [arm64_norm]); exact hd.x19)
        (by (try simp only [arm64_norm]); exact hd.trace)
        (r2p_histOk_of_trace_files hhist0 (by r2p_eq) (by r2p_eq))
        hans_none hrej
  | some meV meG =>
    obtain ⟨hptLt, hcoinsLt, hfs0, hfilesOk, hencOk, hansLink⟩ := hd.send_facts he hcall
    rcases hd.meRegs with ⟨hx21, hx28, hme_bytes, _, hme_dev⟩
    have hme_val : meG.val = addrValOf meV := by
      unfold AddrGhost.val addrValOf; simp [hme_bytes, hme_dev]
    dsimp only [dispatchMemPlaced, dispatchMeHeap, dispatchCells]
    rw [hfsp_def, hcall, r2_locals_some_eq fsp]
    have hopen_some :
        (memRegion g.res runResSize ∗ callAt A g.call (.send peerV) ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
          addrNameHeap A meG ∗ runSaved s0 ∗
          (memRegion fsp 16 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x208#64) 24 ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool) ∗ anyHeap ⊢
        (∃∗ peerG : AddrGhost, ∃∗ cw : CallW,
          ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = cw.w1 ∧ peerG.name.ptr = cw.w2 ∧
            cw.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ cw.w4.setWidth 8 = peerG.device⌝ ∗
          ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
            ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
            ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗ addrNameHeap A peerG) ∗
        (⌜meG.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A meG) ∗
        (∃∗ n0 : BitVec 64, ∃∗ n1 : BitVec 32,
          (fsp ↦₆₄ n0) ∗ ((fsp + 8#64) ↦₃₂ n1) ∗ memRegion (fsp + 12#64) 4) ∗
        (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
          ⌜∀ dst, (dst ↦₆₄ u0) ∗ ((dst + 8#64) ↦₆₄ u1) ⊢ addrUpperAt dst meG⌝ ∗
            ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ (((fsp + 0x1d0#64) + 8#64) ↦₆₄ u1)) ∗
        (∃∗ p0 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ p3 : BitVec 64,
          ((fsp + 0x320#64) ↦₆₄ p0) ∗ (((fsp + 0x320#64) + 8#64) ↦₆₄ p1) ∗
          (((fsp + 0x320#64) + 16#64) ↦₆₄ p2) ∗ (((fsp + 0x320#64) + 24#64) ↦₆₄ p3)) ∗
        (∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64, ∃∗ m3 : BitVec 64,
          ((fsp + 0x23b0#64) ↦₆₄ m0) ∗ (((fsp + 0x23b0#64) + 8#64) ↦₆₄ m1) ∗
          (((fsp + 0x23b0#64) + 16#64) ↦₆₄ m2) ∗ (((fsp + 0x23b0#64) + 24#64) ↦₆₄ m3)) ∗
        (memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ g.i.stdin) ∗
          coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) := by
      have hinp : inputOf g.i (.send peerV) = g.i.stdin := rfl
      rw [hinp]
      refine Entails.trans (Entails.of_eq (Q :=
          callAt A g.call (.send peerV) ∗ addrNameHeap A meG ∗ memRegion fsp 16 ∗
            addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗
            (memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ g.i.stdin) ∗
              coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
              SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)) (by ac_rfl)) ?_
      exact sepConj_mono (r2_callAt_send_unpack A g.call peerV)
        (sepConj_mono (r2_addrNameHeap_cap_lt A meG)
          (sepConj_mono (r2_now_open fsp)
            (sepConj_mono (r2_addrUpperAt_reloc (fsp + 0x1d0#64) meG)
              (sepConj_mono (r2_memRegion32_words4 (fsp + 0x320#64))
                (sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x23b0#64)))))))

    refine sepWPp_weaken_pre hopen_some ?_
    apply r2p_peel_tc; intro peerG; apply r2p_peel_tc; intro cw
    apply r2p_peel_tc; intro _n0; apply r2p_peel_tc; intro _n1
    apply r2p_peel_tc; intro u0; apply r2p_peel_tc; intro u1
    apply r2p_peel_tc; intro _p0; apply r2p_peel_tc; intro _p1; apply r2p_peel_tc; intro _p2; apply r2p_peel_tc; intro _p3
    apply r2p_peel_tc; intro _m0; apply r2p_peel_tc; intro _m1; apply r2p_peel_tc; intro _m2; apply r2p_peel_tc; intro _m3
    apply r2p_peel_pure_tc; rintro ⟨hpeer_val, hw1, hw2, hw3, hw4⟩
    apply r2p_peel_pure_tc; intro hme_lt
    let _ := hme_lt
    apply r2p_peel_pure_tc; intro hu_me
    simp only [emp_sepConj, sepConj_assoc]
    have hcmn_z : (meG.name.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
    have hcmn_nz : (meG.name.cap + 1#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
    have hcmn_ne : ConditionHolds .EQ (addsPState64 meG.name.cap 1#64) = false := by
      rw [conditionHolds_eq_addsPState64]; exact hcmn_z
    have hcmn_neq : ConditionHolds .NE (addsPState64 meG.name.cap 1#64) = true := by
      rw [conditionHolds_ne_addsPState64]; exact hcmn_nz
    let _ := hcmn_z; let _ := hcmn_nz; let _ := hcmn_ne; let _ := hcmn_neq
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 464) hd.base.inv
    rw [← r2_hold_eq (addrNameHeap A peerG), ← r2_hold_eq (addrNameHeap A meG),
        ← r2_hold_eq (memRegion (fsp + 12#64) 4), ← r2_hold_eq (memRegion g.res runResSize ∗ _)]
    dsimp only [fsp]; rw [← hd.base.sp]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    r2p_step_run
    apply SepWP.done (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
    have hsp0 : s.sp = fsp := hd.base.sp
    rw [hsp0, r2_hold_eq, r2_hold_eq, r2_hold_eq, r2_hold_eq]
    intro hinv_enc
    have hx24_toNat : (s.readReg64 (.gpr 24#5)).toNat = g.i.stdin.length := by
      rw [hd.x24, hcall]
      have hinp : (inputOf g.i (.send peerV)).length = g.i.stdin.length := rfl
      rw [hinp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    let encG : EncGhost :=
      { peer := peerG, peerA := fsp + 0x320#64, me := meG, meA := fsp + 0x23b0#64
        stores := g.stores, ret := fsp + 0x4d0#64, coinsP := g.coins, F := runFiles g.i
        coins := MainHops.coinsOf g.i, ptA := g.inp, ptext := g.i.stdin }
    have hspb_enc : resStack - runFrame ≤ (runFsp s0).toNat := by
      dsimp only [runFsp]; dsimp only [runFrame] at hframeLe ⊢; bv_omega
    have hmeA_ne : fsp + 0x23b0#64 ≠ 0#64 := by
      dsimp only [fsp, runFsp]; dsimp only [runFrame] at hframeLe; bv_omega
    have henc_ok : CalleeSlot.OkPlaced (runProgPlaced H) (lsmpl.base 464)
        (slotsOfPlaced A S needs).encrypt := henc_eq ▸ hc.encrypt
    have henc_call : subroutine_ok (runProgPlaced H) (lsmpl.base 464)
        (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (r2p_encInnerSpec A S (resStack - runFrame))) :=
      henc_ok (resStack - runFrame) hencNeed hsub63
    refine r2p_call (spec := r2p_encInnerSpec A S (resStack - runFrame)) (s0 := s0) encG
      henc_call hinv_enc
      (by r2p_pc_done) (by simp only [arm64_norm, hrun0])
      (by (try simp only [arm64_norm]); exact hsp_al)
      (ret_pc := runPcPlaced 1308) (by r2p_pc_done)
      (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗
        memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
        memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        r2_localGaps fsp ∗ anyHeap) ?_
      (hpanic := fun sf R' _ hp => by
        (try dsimp only [r2p_encInnerSpec, encG] at hp)
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        rcases hp.1 with hnone | halloc
        · rw [hpeer_val, hme_val] at hnone
          have ga0 : g.a = none := by rw [hansLink, hnone]; rfl
          exact hpanic sf _ (Or.inl ga0)
        · exact hpanic sf _ (Or.inr
            (allocFailedIn_of_prefix hd.trace (r2_allocFailedIn_of_trace_eq (by r2p_eq) halloc))))
      (hoom := fun _ _ _ ho => by
        (try dsimp only [r2p_encInnerSpec, encG] at ho)
        exact (not_satisfies_false_sepConj ho).elim)
      (hnext := fun s_ret _ hinv_ret hpcm_ret hrun_ret hsp_ret hcs_ret => ?_)
    · dsimp only [r2p_encInnerSpec, slotFramePlaced, encG]; rw [sepConj_assoc]
      apply Entails.pure_right
      · refine ⟨by (try simp only [arm64_norm]); exact hd.x23,
                by (try simp only [arm64_norm]); exact hx24_toNat,
                hptLt,
                by simp only [arm64_norm],
                by simp only [arm64_norm],
                by (try simp only [arm64_norm]); rw [hd.x19],
                by simp only [sessVtPlaced, lsρ, cliSessionVtSym, arm64_norm],
                by (try simp only [arm64_norm]); exact hd.x19,
                by simp only [idVtPlaced, lsρ, cliIdentityVtSym, arm64_norm],
                by simp only [arm64_norm],
                by (try simp only [arm64_norm]); exact hfs0,
                by rw [hpeer_val, hme_val]; exact hfilesOk,
                by rw [hpeer_val]; exact hencOk,
                by (try simp only [arm64_norm]); rw [hsp0]; exact hspb_enc,
                hmeA_ne⟩
      · (try simp only [arm64_norm])
        rw [hsp0, ← hw3]
        have hcw_m := r2_callWords_to_memRegion56 g.call cw
        have hpeer_p := r2_peerWords_pack A (fsp + 0x320#64) peerG cw hw1 hw2 hw3 hw4
        have hme_p :
            ((fsp + 0x23b0#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x23b8#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x23c0#64) ↦₆₄ u0) ∗ ((fsp + 0x23c8#64) ↦₆₄ u1) ∗ addrNameHeap A meG ⊢
            protocolAddressAt A meG (fsp + 0x23b0#64) := by
          rw [protocolAddressAt_eq_parts A meG (fsp + 0x23b0#64)]
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact sepConj_mono_right (sepConj_mono_right
            (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
              (sepConj_mono_left
                (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hu_me (fsp + 0x23c0#64)))))
        have hu16 :
            ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1) ⊢ memRegion (fsp + 0x1d0#64) 16 := by
          rw [ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 8) (k := 8)
                (b' := fsp + 0x1d8#64) rfl (by bv_omega) (by decide)]
          exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpeer_p)
        refine Entails.trans (Entails.of_eq (Q :=
            (((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
                ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
                ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
              (((fsp + 0x320#64) ↦₆₄ cw.w1) ∗ ((fsp + 0x328#64) ↦₆₄ cw.w2) ∗
                ((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4) ∗ addrNameHeap A peerG) ∗
              (((fsp + 0x23b0#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x23b8#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x23c0#64) ↦₆₄ u0) ∗ ((fsp + 0x23c8#64) ↦₆₄ u1) ∗ addrNameHeap A meG) ∗
              (((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1)) ∗ nowCellAt fsp unixEpoch ∗
              (storesAt A g.stores StoresGhost.opened ∗
                coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
                SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
                (g.inp ↦ₛ g.i.stdin) ∗ memRegion (fsp + 0x4d0#64) 248 ∗
                stackAt fsp (resStack - runFrame) ∗ memRegion g.res runResSize ∗ runSaved s0 ∗
                memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
                memRegion (fsp + 0x1750#64) 248 ∗ r2_localGaps fsp ∗ anyHeap)))
          (by dsimp only [nowCellAt, unixEpoch, fsp, runFsp]; (try simp only [arm64_norm]); ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hcw_m (sepConj_mono hpeer_p (sepConj_mono hme_p (sepConj_mono_left hu16)))) ?_
        exact Entails.pure_right hcoinsLt
          (Entails.of_eq (by dsimp only [nowCellAt, unixEpoch, fsp, runFsp]; (try simp only [arm64_norm]); ac_rfl))
    · (try dsimp only [r2p_encInnerSpec, encG])
      apply r2p_peel_tc; intro g'; apply r2p_peel_tc; intro e
      apply r2p_peel_pure_tc; rintro ⟨hst, hout, hpkBound⟩
      simp only [emp_sepConj, sepConj_assoc]
      have hhist_ret : RunHistOk g.i s0 s_ret :=
        r2p_histOk_of_slotTrace (r2p_histOk_of_trace_files hhist0 (by r2p_eq) (by r2p_eq)) hst
      have htr_ret : s0.trace <+: s_ret.trace :=
        (by simpa only [arm64_norm] using hd.trace : s0.trace <+: _).trans hst.1
      have hcs_r := r2p_cs_regs hcs_ret
      have hin_ret : InRunPlaced r2p_CodeOk s0 s_ret 1308 :=
        r2p_inRun_mk hd.base hpcm_ret hrun_ret (hsp_ret.trans (by r2p_eq))
          (hcs_r.2.2.2.2.2.2.2.2.2.2.1.trans (by r2p_eq)) hinv_ret
          (hcs_r.2.2.2.2.2.2.2.2.2.2.2.trans (by r2p_eq))
      have hx19_r : s_ret.readReg64 (.gpr 19#5) = g.stores := by
        rw [hcs_r.1]; (try simp only [arm64_norm]); exact hd.x19
      have hx20_r : s_ret.readReg64 (.gpr 20#5) = g.res := by
        rw [hcs_r.2.1]; (try simp only [arm64_norm]); exact hd.x20
      have hx21_r : s_ret.readReg64 (.gpr 21#5) = meG.name.cap := by
        rw [hcs_r.2.2.1]; (try simp only [arm64_norm]); exact hx21
      have hx22_r : s_ret.readReg64 (.gpr 22#5) = fsp + 0x4d0#64 := by
        rw [hcs_r.2.2.2.1]; simp only [arm64_norm]
      have hx26_r : s_ret.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 := by
        rw [hcs_r.2.2.2.2.2.2.2.1]; (try simp only [arm64_norm]); exact hd.x26
      have hx27_r : s_ret.readReg64 (.gpr 27#5) = fsp + 0x1750#64 := by
        rw [hcs_r.2.2.2.2.2.2.2.2.1]; (try simp only [arm64_norm]); exact hd.x27
      have hx28_r : s_ret.readReg64 (.gpr 28#5) = meG.name.ptr := by
        rw [hcs_r.2.2.2.2.2.2.2.2.2.1]; (try simp only [arm64_norm]); exact hx28
      refine sepWPp_weaken_pre (P' :=
          encResAt A (fsp + 0x4d0#64) e ∗ addrNameHeap A meG ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) ?_ ?_
      · (try simp only [arm64_norm])
        rw [hsp0, hcall]
        have hinp : inputOf g.i (.send peerV) = g.i.stdin := rfl
        rw [hinp]
        have hpeer_split :
            protocolAddressAt A peerG (fsp + 0x320#64) ⊢
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x330#64) 16 ∗ addrNameHeap A peerG := by
          rw [protocolAddressAt_eq_parts A peerG (fsp + 0x320#64)]
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left
              (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                addrUpperAt_entails_memRegion (fsp + 0x330#64) peerG)))
        refine Entails.trans (Entails.of_eq (Q :=
            protocolAddressAt A peerG (fsp + 0x320#64) ∗ protocolAddressAt A meG (fsp + 0x23b0#64) ∗
              nowCellAt fsp unixEpoch ∗ (FromRecordCallees.lsLogOff ∗ anyHeap ∗ anyHeap) ∗
              (encResAt A (fsp + 0x4d0#64) e ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores g' ∗ (g.inp ↦ₛ g.i.stdin) ∗ runSaved s0 ∗
                memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
                memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
                r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool))
          (by dsimp only [fsp, runFsp]; (try simp only [arm64_norm]); ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hpeer_split
            (sepConj_mono (r2_protocolAddress_to_mem32_heap A meG (fsp + 0x23b0#64))
              (sepConj_mono (r2_now_to_mem16 fsp) (sepConj_mono_left (entails_anyHeap _)))))
          (Entails.of_eq (by dsimp only [fsp, runFsp]; (try simp only [arm64_norm]); ac_rfl))
      rw [hpeer_val, hme_val] at hout
      cases e with
      | error err =>
        have hneStore : err ≠ .store () := RunProofs.slotOut_err_ne_store hout
        have hans_err : g.a = some none := by rw [hansLink, hout.2.2]; rfl
        exact r2p_err_arm (peerG := peerG) (meG := meG) hh hdrop hdropNeed hextNeed hsub64 hin_ret
          hx19_r hx20_r hx21_r hx22_r hx28_r htr_ret hhist_ret hneStore hans_err hrej
      | ok msg =>
        rcases hout.2.2 with ⟨hans_ok, hwr⟩
        cases msg with
        | signalMessage m =>
          have hans_sig : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) := by
            rw [hansLink, hans_ok]; rfl
          exact r2p_sig_arm (peerG := peerG) (meG := meG) hh hcatNeed hextNeed hsub64 hin_ret
            hx19_r hx20_r hx21_r hx22_r hx26_r hx27_r hx28_r
            htr_ret hhist_ret hans_sig hwr hpanic hjoin
        | preKeySignalMessage m =>
          have hans_pk : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) := by
            rw [hansLink, hans_ok]; rfl
          exact r2p_pk_arm (peerG := peerG) (meG := meG) hh hcatNeed hdpkNeed hextNeed hsub64 hin_ret
            hx19_r hx20_r hx21_r hx22_r hx26_r hx27_r hx28_r
            htr_ret hhist_ret hans_pk hwr (hpkBound m rfl) hpanic hjoin

theorem run_hop_send_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopSendPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack :=
  run_hop_send_of_slots (needs := needs) rfl rfl

end CryptoVerification.SignalSession.Cli.RunCompose
