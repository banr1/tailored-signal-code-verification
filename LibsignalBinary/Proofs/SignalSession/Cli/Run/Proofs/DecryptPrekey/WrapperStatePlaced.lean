/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperState
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.ProloguePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LscroKitPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced

/-!
# Relocatable State-Coupled Wrapper Reduction for `decrypt_prekey`

Proves the `[LibsignalPlacement]` wrapper reduction for `signal_session_handshake::decrypt_prekey`
on block `520` (`lsProg_520`) from the poll contract on block `518`, and transfers it to caller
blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre

private def dps_fixedK_placed (K : DpPollKState) (s0 : State) : DpPollK where
  Ghost := K.Ghost
  args := K.args
  inv := fun g => K.inv g s0.fs s0.trace
  res := fun _ _ => emp
  io := fun _ _ _ _ _ => True
  panics := K.panics
  need := K.need

private theorem dps_sepWPp_seq_keepsFrozen_placed {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P
      (fun sm Pm => s.mem.KeepsFrozen sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (Φ := fun m => s.mem.KeepsFrozen m)
    (fun _ _ h1 h2 => h1.trans h2) (Memory.KeepsFrozen.refl s.mem) h

private structure dps_EpilogueMidPlaced [LibsignalPlacement] (s0 sm se : State) : Prop where
  pc : se.pc = (blkPl_520).base + 176#64
  run : se.status = .Running
  sp : se.sp = s0.sp - 2144#64
  sp_align : se.spAligned = true
  x22 : se.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)
  x23 : se.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5)
  x24 : se.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : se.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : se.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : se.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  vregs : calleeSavedVRegs se = calleeSavedVRegs s0
  fs : se.fs = sm.fs
  trace : se.trace = sm.trace

private abbrev dps_epilogueMidProp_placed (stk : Nat) (s0 sm : State) (ret : BitVec 64)
    {K : DpPollKState} (g : K.Ghost) (w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (∃∗ ws : List (BitVec 64),
      ⌜ws.length = 6 ∧ ws.head? ≠ some (BitVec.ofNat 64 (2 ^ 64 - 3))⌝ ∗
        dpWordsAt ret ws ∗ K.res g s0.fs s0.trace sm.fs sm.trace ws) ∗
    dpWordsAt s0.sp ((K.args g).drop 8) ∗
    stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗
    memRegion (s0.sp - 2144#64) 704 ∗
    ((s0.sp - 1440#64) ↦₈ 1#8) ∗
    memRegion (s0.sp - 1439#64) 1303 ∗
    memRegion (s0.sp - 136#64) 32 ∗
    ((s0.sp - 104#64) ↦₆₄ w0) ∗ ((s0.sp - 96#64) ↦₆₄ w1) ∗
    ((s0.sp - 88#64) ↦₆₄ w2) ∗ ((s0.sp - 80#64) ↦₆₄ w3) ∗
    ((s0.sp - 72#64) ↦₆₄ w4) ∗ ((s0.sp - 64#64) ↦₆₄ w5) ∗
    memRegion (s0.sp - 56#64) 8 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
set_option maxHeartbeats 400000 in
private theorem dps_wrapper_epilogue_a_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {K : DpPollKState} {stk : Nat}
    {s0 s1 sm : State} {ret : BitVec 64} {g : K.Ghost}
    {Q : State → SepProp → Prop} {oom : State → SepProp}
    (hp1 : DpProloguePostPlaced s0 ret s1)
    (hpcm : sm.pc = (blkPl_520).base + 100#64)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s1.sp)
    (hcsm : CalleeSavedPreserved s1 sm)
    (hk : ∀ se Pe w0 w1 w2 w3 w4 w5,
      dps_EpilogueMidPlaced s0 sm se →
      Pe = dps_epilogueMidProp_placed stk s0 sm ret g w0 w1 w2 w3 w4 w5 →
      Q se Pe) :
    SepWP (lsProg_520 (Rust.withPanics ext))
      ((blkPl_520).base + 176#64)
      sm
      ((dpPollSpecState K (stk - dpWrapFrame)).post
          ⟨s0.sp - 104#64, s0.sp - 2144#64, s0.sp - 136#64, g⟩ s1 sm ∗
        dpCallerFrame s0 ret ((K.args g).drop 8))
      Q oom := by
  dsimp only [lsProg_520]
  have hsp_align_sm : sm.spAligned = true := by
    simp only [State.spAligned, hspm]; exact hp1.sp_align
  have hfp_sm : sm.readReg64 Reg.fp = s0.sp - 48#64 := hcsm.readReg64_fp.trans hp1.fp
  have hx19_sm : sm.readReg64 (.gpr 19#5) = ret := hcsm.readReg64_x19.trans hp1.x19
  have hx22_sm : sm.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) := hcsm.readReg64_x22.trans hp1.x22
  have hx23_sm : sm.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) := hcsm.readReg64_x23.trans hp1.x23
  have hx24_sm : sm.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) := hcsm.readReg64_x24.trans hp1.x24
  have hx25_sm : sm.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) := hcsm.readReg64_x25.trans hp1.x25
  have hx26_sm : sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) := hcsm.readReg64_x26.trans hp1.x26
  have hx27_sm : sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) := hcsm.readReg64_x27.trans hp1.x27
  have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs s0 := hcsm.vregs.trans hp1.vregs
  have hsp_s1 : s1.sp = s0.sp - 2144#64 := hp1.sp
  have hfs_s1 : s1.fs = s0.fs := hp1.fs
  have htr_s1 : s1.trace = s0.trace := hp1.trace
  refine sepWP_unpack_callerFrame fun r0 r1 r2 r3 r4 r5 => ?_
  dsimp only [dpPollSpecState]
  rw [hsp_s1, hfs_s1, htr_s1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i ws
  wp_focus_pure; rintro ⟨hws_len, hws_head⟩
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl, hw0_ne⟩ := ws6_unpack hws_len hws_head
  obtain ⟨hw0_add3, hcmn_ne⟩ := cmn3_ne_zero hw0_ne
  rw [dpFutDoneAt_eq s0.sp, dpWords6_eq (s0.sp - 104#64) w0 w1 w2 w3 w4 w5]
  simp only [bv_off_14, bv_off_15, bv_off_15b, bv_off_17, bv_off_17b, sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq (dpWords6_eq ret w0 w1 w2 w3 w4 w5).symm) (by sep_focus)
  apply SepWP.fold (dpRetRes_pack (res := K.res g s0.fs s0.trace sm.fs sm.trace)
    ret w0 w1 w2 w3 w4 w5 hw0_ne) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine hk _ _ w0 w1 w2 w3 w4 w5 ?_ (sep_rearrange (by dsimp only [dps_epilogueMidProp_placed]; sep_focus))
  exact
    { pc := by simp only [wp_norm, arm64_norm]
      run := by simp only [wp_norm, arm64_norm, *]
      sp := by simp only [wp_norm, arm64_norm, *]
      sp_align := by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_sm ⊢; exact hsp_align_sm
      x22 := by simp only [wp_norm, arm64_norm, *]
      x23 := by simp only [wp_norm, arm64_norm, *]
      x24 := by simp only [wp_norm, arm64_norm, *]
      x25 := by simp only [wp_norm, arm64_norm, *]
      x26 := by simp only [wp_norm, arm64_norm, *]
      x27 := by simp only [wp_norm, arm64_norm, *]
      vregs := by simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
      fs := by simp only [wp_norm, arm64_norm, *]
      trace := by simp only [wp_norm, arm64_norm, *] }

set_option maxHeartbeats 400000 in
private theorem dps_wrapper_epilogue_b_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {K : DpPollKState} {stk : Nat} (hge_wrap : dpWrapFrame ≤ stk) (hle_wrap : stk ≤ 2 ^ 64)
    {s0 sm se : State} {ret : BitVec 64} {g : K.Ghost}
    {w0 w1 w2 w3 w4 w5 : BitVec 64}
    {R : SepProp} {oom : State → SepProp}
    (hsp_align : s0.spAligned = true)
    (he : dps_EpilogueMidPlaced s0 sm se) :
    SepWP (lsProg_520 (Rust.withPanics ext))
      (s0.readReg64 Reg.lr) se
      (dps_epilogueMidProp_placed stk s0 sm ret g w0 w1 w2 w3 w4 w5)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (cliDecryptPrekeySpecState K stk)).post ⟨ret, g⟩ s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      oom := by
  rcases he with ⟨hpc_e, hrun_e, hsp_e, hsp_align_e, hx22_e, hx23_e, hx24_e,
    hx25_e, hx26_e, hx27_e, hvregs_e, hfs_e, htr_e⟩
  dsimp only [lsProg_520, dps_epilogueMidProp_placed]
  wp_steps
  apply SepWP.fold (stackAt_dp_epilogue s0.sp hge_wrap hle_wrap w0 w1 w2 w3 w4 w5
    (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr)
    (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))) (by sep_focus)
  apply SepWP.fold
    (Entails.refl ((∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
          dpWordsAt ret ws ∗ K.res g s0.fs s0.trace sm.fs sm.trace ws) ∗
      dpWordsAt s0.sp ((K.args g).drop 8) ∗ stackAt s0.sp stk))
    (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨fun hm => ?_, by simp only [wp_norm, arm64_norm, *], ?_⟩
  · rw [sepConj_emp] at hm
    dsimp only [StoreKit.withLsCodeRoLoaded, cliDecryptPrekeySpecState]
    simp only [arm64_norm, hfs_e, htr_e] at hm ⊢
    exact hm
  · constructor <;> simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
theorem dps_cliDecryptPrekey_ok_state_impl_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (K : DpPollKState)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 520)
      (StoreKit.withLsCodeRoLoaded lsmpl (cliDecryptPrekeySpecState K stk)) := by
  have hge_wrap : dpWrapFrame ≤ stk := by omega
  have hle_wrap : stk ≤ 2 ^ 64 := by omega
  have hpoll_rocl : subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 518)
      (StoreKit.withLsRoCl lsmpl (dpPollSpecState K (stk - dpWrapFrame))) :=
    StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := lsProg_520 (Rust.withPanics ext))
      (hK (stk - dpWrapFrame) (by omega) (by omega))
  clear hK
  wpp_init x s0
  obtain ⟨ret, g⟩ := x
  dsimp only [StoreKit.withLsCodeRoLoaded, cliDecryptPrekeySpecState] at *
  have hx8 : s0.readReg64 Reg.x8 = ret := by assumption
  have hlen13 : (K.args g).length = 13 := by assumption
  have htake8 : (K.args g).take 8 =
      [s0.readReg64 Reg.x0, s0.readReg64 Reg.x1, s0.readReg64 Reg.x2, s0.readReg64 Reg.x3,
       s0.readReg64 Reg.x4, s0.readReg64 Reg.x5, s0.readReg64 Reg.x6, s0.readReg64 Reg.x7] := by
    assumption
  have hsp_le : stk ≤ s0.sp.toNat := by assumption
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  obtain ⟨a8, a9, a10, a11, a12, hdrop_eq, hargs_eq⟩ := args13_unpack hlen13 htake8
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a1_placed (K := dps_fixedK_placed K s0) (g := g)
    hge_wrap hle_wrap hpc hrun hsp_align hx8 hdrop_eq ?_
  rintro sa _ ha rfl hkf1
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a2_placed (K := dps_fixedK_placed K s0) (g := g) ha ?_
  rintro sb _ f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 hb rfl hkf2
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_b_placed (K := dps_fixedK_placed K s0) (g := g) hb hargs_eq ?_
  rintro s1 _ hp1 rfl hkf3
  have hsp_le1 : stk - dpWrapFrame ≤ (s0.sp - 2144#64).toNat := by
    have hw : dpWrapFrame = 2144 := rfl
    rw [hw] at hge_wrap ⊢
    bv_omega
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
    hcrl0.of_keepsFrozen ((hkf1.trans hkf2).trans hkf3)
  exact SepWPp.call_withLsRoCl
    (spec := dpPollSpecState K (stk - dpWrapFrame))
    (x := DpPollGhostState.mk (s0.sp - 104#64) (s0.sp - 2144#64) (s0.sp - 136#64) g)
    (F := dpCallerFrame s0 ret ((K.args g).drop 8))
    hpoll_rocl hcrl1 hp1.pc hp1.run hp1.sp_align hp1.lr
    (fun R' hm => by
      dsimp only [dpPollSpecState]
      rw [hp1.fs, hp1.trace, hp1.sp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hp1.x0, hp1.x1, hp1.x2, hlen13, hsp_le1⟩, ?_⟩
      dsimp only [dps_fixedK_placed] at hm
      simpa only [sepConj_assoc] using hm)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf_pan _ hmpan => by
      dsimp only [StoreKit.withLsRoCl, StoreKit.withLsCodeRoLoaded,
        dpPollSpecState, cliDecryptPrekeySpecState] at hmpan ⊢
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmpan
      obtain ⟨⟨htr_pan, hpan_or⟩, hmpan_rest⟩ := hmpan
      rw [hp1.trace] at htr_pan
      have hpan0 : allocFailedIn s0 sf_pan ∨ K.panics g :=
        hpan_or.imp_left (allocFailedIn_eq_of_trace_eq hp1.trace).mp
      rw [← sepConj_assoc] at hmpan_rest
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨htr_pan, hpan0⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmpan_rest⟩)
    (fun sm hpcm hrunm hspm hcsm _ => by
      apply dps_sepWPp_seq_keepsFrozen_placed
      refine dps_wrapper_epilogue_a_placed hp1 hpcm hrunm hspm hcsm ?_
      rintro se _ w0 w1 w2 w3 w4 w5 he rfl _
      exact SepWPp.of_sepWP_ret (dps_wrapper_epilogue_b_placed hge_wrap hle_wrap hsp_align he))
    (fun _ _ _ hmo => (not_satisfies_false_sepConj hmo).elim)

theorem dps_cliDecryptPrekey_ok_state_impl_frozen_placed [LibsignalFullPlacement]
    {ext : String → Option (State → State)}
    (K : DpPollKState)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (withLsFrozen lsmpl (dpPollSpecState K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 520)
      (withLsFrozen lsmpl (cliDecryptPrekeySpecState K stk)) := by
  have hge_wrap : dpWrapFrame ≤ stk := by omega
  have hle_wrap : stk ≤ 2 ^ 64 := by omega
  have hpoll_fr : subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 518)
      (withLsFrozen lsmpl (dpPollSpecState K (stk - dpWrapFrame))) :=
    _root_.LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
      (callerProg := lsProg_520 (Rust.withPanics ext))
      (hK (stk - dpWrapFrame) (by omega) (by omega))
  clear hK
  wpp_init x s0
  obtain ⟨ret, g⟩ := x
  dsimp only [withLsFrozen, cliDecryptPrekeySpecState] at *
  have hx8 : s0.readReg64 Reg.x8 = ret := by assumption
  have hlen13 : (K.args g).length = 13 := by assumption
  have htake8 : (K.args g).take 8 =
      [s0.readReg64 Reg.x0, s0.readReg64 Reg.x1, s0.readReg64 Reg.x2, s0.readReg64 Reg.x3,
       s0.readReg64 Reg.x4, s0.readReg64 Reg.x5, s0.readReg64 Reg.x6, s0.readReg64 Reg.x7] := by
    assumption
  have hsp_le : stk ≤ s0.sp.toNat := by assumption
  have hfr0 : LibsignalFrozen lsmpl s0.mem := by assumption
  obtain ⟨a8, a9, a10, a11, a12, hdrop_eq, hargs_eq⟩ := args13_unpack hlen13 htake8
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a1_placed (K := dps_fixedK_placed K s0) (g := g)
    hge_wrap hle_wrap hpc hrun hsp_align hx8 hdrop_eq ?_
  rintro sa _ ha rfl hkf1
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a2_placed (K := dps_fixedK_placed K s0) (g := g) ha ?_
  rintro sb _ f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 hb rfl hkf2
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_b_placed (K := dps_fixedK_placed K s0) (g := g) hb hargs_eq ?_
  rintro s1 _ hp1 rfl hkf3
  have hsp_le1 : stk - dpWrapFrame ≤ (s0.sp - 2144#64).toNat := by
    have hw : dpWrapFrame = 2144 := rfl
    rw [hw] at hge_wrap ⊢
    bv_omega
  have hfr1 : LibsignalFrozen lsmpl s1.mem :=
    libsignalFrozen_of_keepsFrozen hfr0 ((hkf1.trans hkf2).trans hkf3)
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
    ⟨LibsignalCodeLoaded.of_codeLoaded hfr1.2, hfr1.1⟩
  exact SepWPp.call_lscro_plain
    (spec := withLsFrozen lsmpl (dpPollSpecState K (stk - dpWrapFrame)))
    (x := DpPollGhostState.mk (s0.sp - 104#64) (s0.sp - 2144#64) (s0.sp - 136#64) g)
    (F := dpCallerFrame s0 ret ((K.args g).drop 8))
    hpoll_fr hcrl1 hp1.pc hp1.run hp1.sp_align hp1.lr
    (fun R' hm => by
      dsimp only [withLsFrozen, dpPollSpecState]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hfr1, ?_⟩
      rw [hp1.fs, hp1.trace, hp1.sp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hp1.x0, hp1.x1, hp1.x2, hlen13, hsp_le1⟩, ?_⟩
      dsimp only [dps_fixedK_placed] at hm
      simpa only [sepConj_assoc] using hm)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf_pan _ hmpan => by
      dsimp only [withLsFrozen, dpPollSpecState, cliDecryptPrekeySpecState] at hmpan ⊢
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmpan
      obtain ⟨⟨htr_pan, hpan_or⟩, hmpan_rest⟩ := hmpan
      rw [hp1.trace] at htr_pan
      have hpan0 : allocFailedIn s0 sf_pan ∨ K.panics g :=
        hpan_or.imp_left (allocFailedIn_eq_of_trace_eq hp1.trace).mp
      rw [← sepConj_assoc] at hmpan_rest
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨htr_pan, hpan0⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmpan_rest⟩)
    (fun sm hpcm hrunm hspm hcsm _ => by
      apply dps_sepWPp_seq_keepsFrozen_placed
      refine dps_wrapper_epilogue_a_placed hp1 hpcm hrunm hspm hcsm ?_
      rintro se _ w0 w1 w2 w3 w4 w5 he rfl _
      exact SepWPp.of_sepWP_ret (dps_wrapper_epilogue_b_placed hge_wrap hle_wrap hsp_align he))
    (fun _ _ _ hmo => (not_satisfies_false_sepConj hmo).elim)

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Relocatable wrapper reduction on block `520`: given `dpPollSpecState K` on block `518` for
`K.need ≤ stk' ≤ 2 ^ 63`, `decrypt_prekey` satisfies `cliDecryptPrekeySpecState K` for
`0x860 + K.need ≤ stk ≤ 2 ^ 63`. -/
theorem cliDecryptPrekey_ok_state_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (K : DpPollKState)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 520)
      (StoreKit.withLsCodeRoLoaded lsmpl (cliDecryptPrekeySpecState K stk)) :=
  DecryptPrekeyHelpers.dps_cliDecryptPrekey_ok_state_impl_placed K hK stk hstk hstk64

/-- Transfers `cliDecryptPrekey_ok_state_placed` to any caller block `i < 619`. -/
theorem cliDecryptPrekey_ok_state_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (K : DpPollKState)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 520)
      (StoreKit.withLsCodeRoLoaded lsmpl (cliDecryptPrekeySpecState K stk)) := by
  have hrocl := StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
    (cliDecryptPrekey_ok_state_placed K hK stk hstk hstk64) hi
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [StoreKit.withLsRoCl, StoreKit.withLsCodeRoLoaded] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

theorem cliDecryptPrekey_ok_state_frozen_placed [LibsignalFullPlacement]
    {ext : String → Option (State → State)}
    (K : DpPollKState)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (withLsFrozen lsmpl (dpPollSpecState K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 520)
      (withLsFrozen lsmpl (cliDecryptPrekeySpecState K stk)) :=
  DecryptPrekeyHelpers.dps_cliDecryptPrekey_ok_state_impl_frozen_placed K hK stk hstk hstk64

theorem cliDecryptPrekey_ok_state_frozen_placed_at_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (K : DpPollKState)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (withLsFrozen lsmpl (dpPollSpecState K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (_hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 520)
      (withLsFrozen lsmpl (cliDecryptPrekeySpecState K stk)) :=
  _root_.LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
    (callerProg := callerProg)
    (cliDecryptPrekey_ok_state_frozen_placed K hK stk hstk hstk64)

end CryptoVerification.SignalSession.Cli.RunProofs
end
