/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cStepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# `signal_session::run` Arm `R1c` Placed Proof

Proves `run_hop_init3_placed_ok` on Block `579` (`runProgPlaced H`), establishing
`RunHopInit3Placed (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A H B S needs resStack`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunDrop

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

attribute [local simp, local arm64_norm, local wp_norm]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem

local macro "r1c_close_post" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals (simp (config := { zetaDelta := true }) only [runPcPlaced_eq, BitVec.ofNat_eq_ofNat, runFsp, wp_norm, arm64_norm, *]; try bv_omega)))

theorem r1c_err_after_drop [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x29d0)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced R1cCodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  have hres_split : r1c_okCore A g g' s0 ⊢
      ∃∗ rv0 : BitVec 64, (g.res ↦₆₄ rv0) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
        (memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ anyHeap) := by
    dsimp only [r1c_okCore, runResSize]
    rw [ProofLib.memRegion_split' (b := g.res) (n := 8) (k := 336) (b' := g.res + 8#64) rfl rfl (by decide)]
    simp only [ProofLib.memRegion_eight, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro rv0
    exact Entails.sepExists_right rv0 (Entails.of_eq (by ac_rfl))
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      hres_split (by ac_rfl) rfl)
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro rv0
  let lowRest := ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hlow_eq :
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗ lowRest =
      r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, lowRest]; ac_rfl
  let coreRest := memRegion (g.res + 8#64) (runResSize - 8) ∗
    (memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      runSaved s0 ∗ anyHeap)
  let tailHold := addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
    lowRest ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  have hstep1 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
      ((g.res ↦₆₄ rv0) ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)))
      (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
        s1.readReg64 .lr = runPcPlaced 0x29f0 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 .x0 = d.spkSigPtr ∧ s1.readReg64 .x1 = 64#64 ∧ s1.readReg64 .x2 = 1#64 ∧
        s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P1 = ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗
          (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64))))
      (fun _ => ⌜False⌝) := by
    have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
    have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
    have hal : s.spAligned = true := hs.spAligned_cur
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, by ac_rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ tailHold ∗ coreRest)
    hs.inv (Entails.of_eq (by dsimp only [tailHold, coreRest]; rw [← hlow_eq]; ac_rfl)) hstep1
    fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx21_1⟩ => ?_
  have herr_core : (g.res ↦₆₄ 0xffffffffffffffff#64) ∗ coreRest = r1c_errCore A g g' s0 := by
    dsimp only [r1c_errCore, runResAt, coreRest]; ac_rfl
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      ((((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        tailHold ∗ r1c_errCore A g g' s0))
    (Entails.of_eq (by rw [← herr_core]; ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
      hx0_1 (by rw [hx1_1]; rfl) hx2_1 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, _, hx21_2, _, _, _, _, _, _, _, hfp2, hv2⟩
  have hstep2 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s2
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr))
      (fun s3 P3 => (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
        s3.readReg64 .lr = runPcPlaced 0x2a08 ∧
        calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
        s3.readReg64 .x0 = d.kpkPtr ∧ s3.readReg64 .x1 = 1568#64 ∧ s3.readReg64 .x2 = 1#64 ∧
        s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P3 = (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)))
      (fun _ => ⌜False⌝) := by
    rw [runPcPlaced_eq] at hpc2
    have hfp := hfp2.trans hfp1; have hv := hv2.trans hv1
    have hx19' := hx19_2.trans hx19_1; have hx21' := hx21_2.trans hx21_1
    have hal : s2.spAligned = true := r1c_spAligned hs.spAligned hsp2
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s2.sp from hsp2.symm]; clear hsp2; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, by ac_rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ tailHold ∗ r1c_errCore A g g' s0)
    hinv2 (Entails.of_eq (by dsimp only [fsp]; ac_rfl)) hstep2
    fun s3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3, hx0_3, hx1_3, hx2_3, hx19_3, hx21_3⟩ => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      ((A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        tailHold ∗ r1c_errCore A g g' s0))
    (Entails.of_eq (by ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv3 hpc3 hrun3 hsp3 hlr3
      hx0_3 (by rw [hx1_3]; rfl) hx2_3 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s4 hinv4 hpc4 hrun4 hsp4 hcs4 hfs4 htr4 => ?_)
  rcases hcs4 with ⟨hx19_4, _, hx21_4, _, _, _, _, _, _, _, hfp4, hv4⟩
  have hstep3 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s4
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64))
      (fun s5 P5 => (s5.sp = fsp ∧ s5.readReg64 .fp = s0.sp - 0x60#64 ∧
        s5.readReg64 .lr = runPcPlaced 0x2a20 ∧
        calleeSavedVRegs s5 = calleeSavedVRegs s0 ∧ s5.trace = s4.trace ∧ s5.fs = s4.fs ∧
        s5.readReg64 .x0 = d.kpkSigPtr ∧ s5.readReg64 .x1 = 64#64 ∧ s5.readReg64 .x2 = 1#64 ∧
        s5.readReg64 (.gpr 19#5) = g.stores ∧ s5.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P5 = (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)))
      (fun _ => ⌜False⌝) := by
    rw [runPcPlaced_eq] at hpc4
    have hfp := hfp4.trans hfp3; have hv := hv4.trans hv3
    have hx19' := hx19_4.trans hx19_3; have hx21' := hx21_4.trans hx21_3
    have hal : s4.spAligned = true := r1c_spAligned hs.spAligned hsp4
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s4.sp from hsp4.symm]; clear hsp4; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, by ac_rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ tailHold ∗ r1c_errCore A g g' s0)
    hinv4 (Entails.of_eq (by dsimp only [fsp]; ac_rfl)) hstep3
    fun s5 hinv5 hpc5 hrun5 ⟨hsp5, hfp5, hlr5, hv5, htr5, hfs5, hx0_5, hx1_5, hx2_5, hx19_5, hx21_5⟩ => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      ((((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        tailHold ∗ r1c_errCore A g g' s0))
    (Entails.of_eq (by ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv5 hpc5 hrun5 hsp5 hlr5
      hx0_5 (by rw [hx1_5]; rfl) hx2_5 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s6 hinv6 hpc6 hrun6 hsp6 hcs6 hfs6 htr6 => ?_)
  rcases hcs6 with ⟨hx19_6, _, hx21_6, _, _, _, _, _, _, _, hfp6, hv6⟩
  have hs6 : InRunPlaced R1cCodeOk s0 s6 0x2a20 :=
    ⟨hpc6, hrun6, hsp6, hfp6.trans hfp5, hinv6, hv6.trans hv5, hs.spAligned⟩
  have htr_all : s6.trace = s.trace :=
    ((((htr6.trans htr5).trans htr4).trans htr3).trans htr2).trans htr1
  have hfs_all : s6.fs = s.fs :=
    ((((hfs6.trans hfs5).trans hfs4).trans hfs3).trans hfs2).trans hfs1
  refine r1c_sepWPp_weaken_pre ?_
    (r1c_err_free_me (g' := g') (d := d) hh hext_le hsub64 hs6
      (hx19_6.trans hx19_5) (hx21_6.trans hx21_5)
      (htr_all ▸ htr) (r1c_hist_of_eq htr_all (congrArg FsState.files hfs_all) hhist)
      hans hrej)
  exact Entails.of_eq (by dsimp only [tailHold, dirG, fsp]; rw [← hlow_eq]; ac_rfl)

theorem r1c_err_tail [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {k : RunDrop.SpeOwned} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x28f4)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced R1cCodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (RunDrop.speOwnedAt A (fsp + 0x23b0#64) k ∗
        (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let heaps := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
    (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
    (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64)
  let names := addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG
  let lowPeer := r1c_lowCells fsp d ∗
    memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16)
  let gaps2c0 := memRegion (fsp + 0x2c0#64) (0x1750 - 0x2c0) ∗
    memRegion (fsp + 0x1780#64) (0x23b0 - 0x1780) ∗
    memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0)
  have hcarve_dst : memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ⊢
      (∃∗ dst0 : r1c_W6, r1c_slot6 (fsp + 0x1750#64) dst0) ∗ gaps2c0 := by
    rw [r1c_split_at fsp 0x2c0 (0x1750 - 0x2c0) 0x23b0 (by decide) (by decide),
        show (0x2c0 : Nat) + (0x1750 - 0x2c0) = 0x1750 from rfl,
        r1c_split_at fsp 0x1750 48 0x23b0 (by decide) (by decide),
        show (0x1750 : Nat) + 48 = 0x1780 from rfl]
    exact r1c_rewrite_front gaps2c0 (r1c_mem48_to_slot6 (fsp + 0x1750#64))
      (by dsimp only [gaps2c0]; ac_rfl) rfl
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      (RunDrop.speOwnedAt A (fsp + 0x23b0#64) k ∗ heaps ∗ names ∗ lowPeer ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hcarve_dst (by dsimp only [heaps, names, lowPeer]; ac_rfl) rfl)
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro dst0
  refine r1c_sepWPp_weaken_pre
    (P' := RunDrop.speOwnedAt A (fsp + 0x23b0#64) k ∗
      (r1c_slot6 (fsp + 0x1750#64) dst0 ∗ gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0))
    (Entails.of_eq (by ac_rfl)) ?_
  refine r1c_with_speOwned_words6 (dst := fsp + 0x1750#64)
    fun sw Hspe hw0_3 hw0_2 hrebuild => ?_
  have hcmn3 : ((sw.w0 + 3#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_3
  have hcmn2_eq : ((sw.w0 + 2#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_2
  have hcmn2_ne : ((sw.w0 + 2#64) != 0#64) = true := bne_iff_ne.mpr hw0_2
  have hstep_copy : SepWP (runProgPlaced H) (lsmpl.base 553) s
      (r1c_slot6 (fsp + 0x23b0#64) sw ∗ r1c_slot6 (fsp + 0x1750#64) dst0)
      (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
        s1.readReg64 .lr = runPcPlaced 0x29d0 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 .x0 = fsp + 0x1750#64 ∧
        s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
        s1.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P1 = (r1c_slot6 (fsp + 0x23b0#64) sw ∗ r1c_slot6 (fsp + 0x1750#64) sw))
      (fun _ => ⌜False⌝) := by
    have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
    have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
    have hal : s.spAligned = true := hs.spAligned_cur
    dsimp only [runProgPlaced, lsProg_579, r1c_slot6]
    rw [show fsp = s.sp from hsp.symm]; clear hsp
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, by simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]⟩
    r1c_close_post
  refine r1c_frame_seq
    (F := Hspe ∗ gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
    hs.inv (Entails.of_eq (by ac_rfl)) hstep_copy
    fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx19_1, hx20_1, hx21_1⟩ => ?_
  have hwand_src :
      r1c_slot6 (fsp + 0x23b0#64) sw ∗ r1c_slot6 (fsp + 0x1750#64) sw ∗ Hspe ⊢
      RunDrop.speOwnedAt A (fsp + 0x1750#64) k ∗ memRegion (fsp + 0x23b0#64) 48 :=
    Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono hrebuild (r1c_slot6_to_mem48 (fsp + 0x23b0#64) sw))
  refine r1c_call_lscro (s0 := s0)
    (F := memRegion (fsp + 0x23b0#64) 48 ∗ gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗ r1c_okCore A g g' s0)
    ⟨fsp + 0x1750#64, k⟩
    (hdrop (resStack - runFrame) hstk32 hsub64)
    hinv1 hpc1 hrun1 (r1c_spAligned hs.spAligned hsp1) hlr1
    (by
      dsimp only [RunDrop.dropSpeOwnedSpec]
      rw [hsp1]
      refine Entails.trans
        (r1c_rewrite_front
          (gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
          hwand_src (by ac_rfl) rfl) ?_
      conv => rhs; rw [sepConj_assoc]
      exact Entails.pure_right hx0_1 (Entails.of_eq (by ac_rfl)))
    (hnext := fun sm hsteps_m hinv_m hpcm hrunm hspm hcsm => ?_)
  rcases hcsm with ⟨hx19_m, hx20_m, hx21_m, _, _, _, _, _, _, _, hfp_m, hv_m⟩
  dsimp only [RunDrop.dropSpeOwnedSpec]
  rw [hsp1, sepConj_assoc]
  apply r1c_sepWPp_pure_left; intro htr_m
  have hfs_m : sm.fs.files = s1.fs.files :=
    r1c_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_m htr_m
  have hmerge_2c0 :
      memRegion (fsp + 0x1750#64) 48 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ gaps2c0 ⊢
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) := by
    dsimp only [gaps2c0]
    rw [r1c_split_at fsp 0x2c0 (0x1750 - 0x2c0) runLocalBytes (by decide) (by decide),
        show (0x2c0 : Nat) + (0x1750 - 0x2c0) = 0x1750 from rfl,
        r1c_split_at fsp 0x1750 48 runLocalBytes (by decide) (by decide),
        show (0x1750 : Nat) + 48 = 0x1780 from rfl,
        r1c_split_at fsp 0x1780 (0x23b0 - 0x1780) runLocalBytes (by decide) (by decide),
        show (0x1780 : Nat) + (0x23b0 - 0x1780) = 0x23b0 from rfl,
        r1c_split_at fsp 0x23b0 48 runLocalBytes (by decide) (by decide)]
    exact Entails.of_eq (by ac_rfl)
  have hsm : InRunPlaced R1cCodeOk s0 sm 0x29d0 :=
    ⟨hpcm, hrunm, hspm.trans hsp1, hfp_m.trans hfp1, hinv_m, hv_m.trans hv1, hs.spAligned⟩
  refine r1c_sepWPp_weaken_pre ?_
    (r1c_err_after_drop (g' := g') (d := d) hh hext_le hsub64 hsm
      (hx19_m.trans hx19_1) (hx20_m.trans hx20_1) (hx21_m.trans hx21_1)
      ((htr_m.trans htr1) ▸ htr)
      (r1c_hist_of_eq (htr_m.trans htr1) ((hfs_m.trans (congrArg FsState.files hfs1))) hhist)
      hans hrej)
  exact r1c_rewrite_front
    (A.pool ∗ stackAt fsp (resStack - runFrame) ∗ heaps ∗ names ∗ lowPeer ∗ r1c_okCore A g g' s0)
    hmerge_2c0 (by ac_rfl) (by dsimp only [heaps, names, lowPeer, dirG, fsp]; ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunDrop
open CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

attribute [local simp, local arm64_norm, local wp_norm]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem

local macro "r1c_close_post" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals (simp (config := { zetaDelta := true }) only [runPcPlaced_eq, BitVec.ofNat_eq_ofNat, runFsp, wp_norm, arm64_norm, *]; try bv_omega)))

/-- Parametric-slot Arm `R1c` hop proof (`R+0x28f0 → R+0xf8c / R+0x2c7c`) on Block `579`
(`runProgPlaced H`): steps `bl signal_session_handshake::initiate`, invokes `hc.initiate`, and
routes `.ok ()` through `r1c_ok_tail` to `AtJoinPlaced` (`R+0xf8c`) and `.error _` through
`r1c_err_tail` to `AtRejectPlaced .postDispatch` (`R+0x2c7c`). -/
theorem run_hop_init3_of_slots [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A S needs))
    (hinit_eq : slots.initiate = (slotsOfPlaced A S needs).initiate) :
    RunHopInit3PlacedOf (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S slots resStack := by
  intro g s0 s2 d2 Q Qp hh hc hdrop hres hres64 hspb he hi2 hpanic hrej hjoin
  rw [hneed_eq] at hres
  obtain ⟨hrf, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _, _,
      hstk32, _, hext_le, _, _, hinit_stk, _, _⟩ := runNeed_bounds_placed hres hres64
  have hspb_slot : resStack - runFrame ≤ s2.sp.toNat := by
    have hrf_eq : runFrame = 0x2a50 := rfl
    have hsp2 : s2.sp = s0.sp - 0x2a50#64 := hi2.base.sp
    have hle : (0x2a50#64 : BitVec 64) ≤ s0.sp := by
      rw [BitVec.le_def]; change 0x2a50 ≤ s0.sp.toNat; omega
    rw [hsp2, BitVec.toNat_sub_of_le hle, hrf_eq]
    change resStack - 0x2a50 ≤ s0.sp.toNat - 0x2a50; omega
  obtain ⟨hcoins63, hfs2, hspk64, hkpk64, hkpk1568, hfilesOk, hinitOk, hga⟩ :=
    AtInit2Placed.init_facts he hi2
  let fsp := runFsp s0
  let dirG : AddrGhost := ⟨⟨d2.dirCap, d2.dirPtr, d2.dir⟩, 0#8⟩
  have hstep_bl : SepWP (runProgPlaced H) (lsmpl.base 521) s2 emp
      (fun s3 P3 => (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
        s3.readReg64 .lr = runPcPlaced 0x28f4 ∧
        calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
        s3.readReg64 .x0 = fsp + 0x2a0#64 ∧ s3.readReg64 .x1 = fsp + 0x320#64 ∧
        s3.readReg64 .x2 = g.stores + 0xf0#64 ∧ s3.readReg64 .x3 = sessVtPlaced ∧
        s3.readReg64 .x4 = g.stores ∧ s3.readReg64 .x5 = idVtPlaced ∧
        s3.readReg64 .x6 = fsp + 0x4d0#64 ∧ s3.readReg64 .x7 = 0#64 ∧
        s3.readReg64 .x8 = fsp + 0x23b0#64 ∧
        s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
        s3.readReg64 (.gpr 21#5) = d2.meG.name.cap) ∧ P3 = emp)
      (fun _ => ⌜False⌝) := by
    have hpc := hi2.base.pc; rw [runPcPlaced_eq] at hpc
    have hrun := hi2.base.run; have hsp := hi2.base.sp
    have hfp := hi2.base.fp; have hv := hi2.base.vregs
    have hx0 := hi2.x0; have hx1 := hi2.x1; have hx2 := hi2.x2; have hx3 := hi2.x3
    have hx4 := hi2.x4; have hx5 := hi2.x5; have hx6 := hi2.x6; have hx7 := hi2.x7
    have hx8 := hi2.x8; have hx19 := hi2.x19; have hx20 := hi2.x20; have hx21 := hi2.x21
    dsimp only [runProgPlaced, lsProg_579]
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, rfl⟩; r1c_close_post
  refine r1c_frame_seq (F := init2MemPlaced A g d2 s0 resStack)
    hi2.base.inv (Entails.of_eq (emp_sepConj _).symm) hstep_bl
    fun s3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3,
      hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx5_3, hx6_3, hx7_3, hx8_3,
      hx19_3, hx20_3, hx21_3⟩ => ?_
  rw [emp_sepConj]
  let initX : InitGhost :=
    { peer := d2.peerG
      peerA := fsp + 0x2a0#64
      me := d2.meG
      meA := fsp + 0x320#64
      stores := g.stores
      ret := fsp + 0x23b0#64
      coinsP := g.coins
      F := runFiles g.i
      coins := MainHops.coinsOf g.i
      bundleA := fsp + 0x4d0#64
      bundle := d2.bundle
      spkSigPtr := d2.spkSigPtr
      kpkSigPtr := d2.kpkSigPtr
      kpkPtr := d2.kpkPtr }
  let lowPre := memRegion (fsp + 4#64) (0x110 - 4) ∗
    ((fsp + 0x110#64) ↦₆₄ d2.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d2.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d2.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d2.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d2.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d2.dirPtr) ∗
    memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
    memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
    memRegion (fsp + 0x180#64) 56
  let hiGaps := memRegion (fsp + 0x2c0#64) (0x320 - 0x2c0) ∗
    memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
    memRegion (fsp + 0x590#64) (0x23b0 - 0x590)
  let initFrame := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
    ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
    lowPre ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    hiGaps ∗ memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0)
  have htr_s3 : s0.trace <+: s3.trace := htr3 ▸ hi2.trace
  have hspb_s3 : resStack - runFrame ≤ s3.sp.toNat := by
    rw [hsp3]; dsimp only [fsp]; rwa [← hi2.base.sp]
  have hfs_s3 : s3.fs.files = runFiles g.i := (congrArg FsState.files hfs3).trans hfs2
  have hinit_ok : CalleeSlot.OkPlaced (runProgPlaced H) (lsmpl.base 521)
      (slotsOfPlaced A S needs).initiate := hinit_eq ▸ hc.initiate
  refine r1c_call_lscro (s0 := s0) (F := initFrame) initX
    (show subroutine_ok (runProgPlaced H) (lsmpl.base 521)
      (initSlotSpecPlaced A S (resStack - runFrame)) from
      hinit_ok (resStack - runFrame) hinit_stk hsub63)
    hinv3 hpc3 hrun3 (r1c_spAligned hi2.base.spAligned hsp3) hlr3
    (by
      dsimp only [init2MemPlaced, slotFramePlaced, initX]
      refine Entails.trans
        (r1c_rewrite_front
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
            SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
            A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
            ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
            runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool)
          (r1c_init2Locals_unpack A fsp d2)
          (by ac_rfl) rfl) ?_
      simp only [sepConj_assoc]
      apply Entails.pure_right
        ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx5_3, hx6_3, hx7_3, hx8_3,
         hfs_s3, hfilesOk, hinitOk, hspb_s3⟩
      apply Entails.pure_right hcoins63
      rw [hsp3]
      exact Entails.of_eq (by dsimp only [initFrame, lowPre, hiGaps]; ac_rfl))
    (hpanic := fun sf _ _ hp => by
      dsimp only [initX] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rcases hp.1 with hnone | halloc
      · exact hpanic sf _ (Or.inl (by rw [hga, hnone]; rfl))
      · exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix htr_s3 halloc)))
    (hoom := fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  rcases hcsm with ⟨hx19_m, hx20_m, hx21_m, _, _, _, _, _, _, _, hfp_m, hv_m⟩
  dsimp only [initX]
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro g'
  apply r1c_sepWPp_exists_left; intro e
  rw [sepConj_assoc]
  apply r1c_sepWPp_pure_left; rintro ⟨hslotTr, hslotOut⟩
  rw [hsp3]
  have hsp_m : sm.sp = fsp := hspm.trans hsp3
  have hs_m : InRunPlaced R1cCodeOk s0 sm 0x28f4 :=
    ⟨hpcm, hrunm, hsp_m, hfp_m.trans hfp3, hinv_m, hv_m.trans hv3, hi2.base.spAligned⟩
  have hx19_m' : sm.readReg64 (.gpr 19#5) = g.stores := hx19_m.trans hx19_3
  have hx20_m' : sm.readReg64 (.gpr 20#5) = g.res := hx20_m.trans hx20_3
  have hx21_m' : sm.readReg64 (.gpr 21#5) = d2.meG.name.cap := hx21_m.trans hx21_3
  have htr_m : s0.trace <+: sm.trace := htr_s3.trans hslotTr.1
  have hhist_m : RunHistOk g.i s0 sm :=
    ⟨hslotTr.2.1.trans hfs_s3, hslotTr.2.2.trans (htr3 ▸ hi2.stdout)⟩
  have hcollapse_post :
      protocolAddressAt A d2.peerG (fsp + 0x2a0#64) ∗
        protocolAddressAt A d2.meG (fsp + 0x320#64) ∗
        cliBundleAt (fsp + 0x4d0#64) d2.bundle d2.spkSigPtr d2.kpkSigPtr d2.kpkPtr ∗
        (fsp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ anyHeap ∗ initFrame ⊢
      (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
        (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
        (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
        addrNameHeap A d2.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d2.peerG ∗
        r1c_lowCells fsp d2 ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ anyHeap) := by
    have hlow : (fsp ↦₃₂ 0#32) ∗ lowPre ⊢ r1c_lowCells fsp d2 := by
      have hm110 : (fsp ↦₃₂ 0#32) ∗ memRegion (fsp + 4#64) (0x110 - 4) ⊢ memRegion fsp 0x110 := by
        rw [ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 0x110 - 4)
              (b' := fsp + 4#64) rfl rfl (by decide)]
        exact sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion fsp 0#32)
      dsimp only [lowPre, r1c_lowCells, r1c_lowGaps]
      exact r1c_rewrite_front
        (((fsp + 0x110#64) ↦₆₄ d2.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x138#64) ↦₆₄ d2.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d2.kpkPtr) ∗
          ((fsp + 0x1b8#64) ↦₆₄ d2.meG.name.ptr) ∗
          ((fsp + 0x1c0#64) ↦₆₄ d2.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d2.dirPtr) ∗
          memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
          memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
          memRegion (fsp + 0x180#64) 56)
        hm110 (by ac_rfl) (by ac_rfl)
    have hhi : memRegion (fsp + 0x320#64) 32 ∗ memRegion (fsp + 0x4d0#64) 192 ∗ hiGaps ⊢
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) := by
      dsimp only [hiGaps]
      rw [ProofLib.memRegion_split' (b := fsp + 0x2c0#64) (n := 0x320 - 0x2c0)
            (k := 0x23b0 - 0x320) (b' := fsp + 0x320#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32)
            (k := 0x23b0 - 0x340) (b' := fsp + 0x340#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x340#64) (n := 0x4d0 - 0x340)
            (k := 0x23b0 - 0x4d0) (b' := fsp + 0x4d0#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 192)
            (k := 0x23b0 - 0x590) (b' := fsp + 0x590#64) rfl (by bv_omega) (by decide)]
      exact Entails.of_eq (by ac_rfl)
    have hdir : ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ⊢
        addrNameHeap A dirG := by
      refine Entails.trans
        (r1c_ownedBytes_entails_nameHeap A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir) ?_
      exact Entails.pure_left fun _ => Entails.refl _
    have hpeer : protocolAddressAt A d2.peerG (fsp + 0x2a0#64) ⊢
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A d2.peerG := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1c_addr_unpack A d2.peerG (fsp + 0x2a0#64)
    have hany : FromRecordCallees.lsLogOff ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
    dsimp only [initFrame]
    refine Entails.trans
      (sepConj_mono hpeer
        (sepConj_mono (r1c_addr_to_mem32 A d2.meG (fsp + 0x320#64))
          (sepConj_mono (r1c_cliBundleAt_unpack (fsp + 0x4d0#64) d2.bundle d2.spkSigPtr d2.kpkSigPtr d2.kpkPtr)
            (Entails.refl _)))) ?_
    refine Entails.trans
      (r1c_rewrite_front
        ((((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A d2.peerG ∗
          memRegion (fsp + 0x320#64) 32 ∗ addrNameHeap A d2.meG ∗
          memRegion (fsp + 0x4d0#64) 192 ∗
          memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
          FromRecordCallees.lsLogOff ∗ anyHeap ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
          ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          hiGaps ∗ memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        hlow (by ac_rfl) rfl) ?_
    refine Entails.trans
      (r1c_rewrite_front
        (r1c_lowCells fsp d2 ∗
          (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A d2.peerG ∗
          addrNameHeap A d2.meG ∗
          memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
          FromRecordCallees.lsLogOff ∗ anyHeap ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
          ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        hhi (by ac_rfl) rfl) ?_
    exact r1c_rewrite_front
      (memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        r1c_lowCells fsp d2 ∗
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A d2.peerG ∗
        addrNameHeap A d2.meG ∗
        memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
      (sepConj_mono hdir hany) (by ac_rfl) (by ac_rfl)
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      (storesAt A g.stores g' ∗ initResAt A (fsp + 0x23b0#64) e ∗ A.pool ∗
        stackAt fsp (resStack - runFrame))
      hcollapse_post (by ac_rfl) rfl)
  cases e with
  | ok u =>
    cases u
    rcases hslotOut with ⟨_, _, hans_ok, hwr⟩
    have hans : g.a = some (some (namedWrites g'.writes, [])) := by
      rw [hga, hans_ok]; rfl
    dsimp only [initResAt]
    have hcmn3_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 3#64 == 0#64) = false := by decide
    have hcmn2_ne_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 != 0#64) = false := by decide
    have hcmn2_eq_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 == 0#64) = true := by decide
    have hstep_ok : SepWP (runProgPlaced H) (runPcPlaced 0x2908) sm
        ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64)
        (fun s4 P4 => (s4.sp = fsp ∧ s4.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s4 = calleeSavedVRegs s0 ∧ s4.trace = sm.trace ∧ s4.fs = sm.fs ∧
          s4.readReg64 (.gpr 19#5) = g.stores ∧ s4.readReg64 (.gpr 20#5) = g.res ∧
          s4.readReg64 (.gpr 21#5) = d2.meG.name.cap) ∧
          P4 = ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64))
        (fun _ => ⌜False⌝) := by
      have hpc := hs_m.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs_m.run; have hfp := hs_m.fp; have hv := hs_m.vregs
      have hal : sm.spAligned = true := r1c_spAligned hi2.base.spAligned hsp_m
      rw [runPcPlaced_eq, show fsp = sm.sp from hsp_m.symm]
      dsimp only [runProgPlaced, lsProg_579]; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    let okRest := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A d2.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0
    refine r1c_frame_seq
      (F := memRegion (fsp + 0x23b0#64 + 8#64) 40 ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗ okRest)
      hs_m.inv (Entails.of_eq (by dsimp only [okRest, r1c_okCore]; ac_rfl)) hstep_ok
      fun s4 hinv4 hpc4 hrun4 ⟨hsp4, hfp4, hv4, htr4, hfs4, hx19_4, hx20_4, hx21_4⟩ => ?_
    have hmerge_ok :
        ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          memRegion (fsp + 0x23b0#64 + 8#64) 40 ∗
          memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ⊢
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [r1c_split_at fsp 0x2c0 (0x23b0 - 0x2c0) runLocalBytes (by decide) (by decide),
          r1c_split_at fsp 0x23b0 8 runLocalBytes (by decide) (by decide),
          r1c_split_at fsp 0x23b8 40 runLocalBytes (by decide) (by decide)]
      exact r1c_rewrite_front
        (memRegion (fsp + 0x23b8#64) 40 ∗
          memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        (pointsTo64_entails_memRegion _ _) (by ac_rfl) (by ac_rfl)
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_tail (g' := g') (d := d2) hh hext_le hsub64 ⟨hpc4, hrun4, hsp4, hfp4, hinv4, hv4, hi2.base.spAligned⟩
        hx19_4 hx20_4 hx21_4 (htr4 ▸ htr_m)
        (r1c_hist_of_eq htr4 (congrArg FsState.files hfs4) hhist_m)
        hans hwr hjoin)
    exact r1c_rewrite_front okRest hmerge_ok (by ac_rfl) (by dsimp only [okRest, fsp, dirG]; ac_rfl)
  | error err =>
    have hans : g.a = some none := by
      rw [hga, hslotOut.2.2]; rfl
    dsimp only [initResAt]
    let errRest := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A d2.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
      memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0
    apply r1c_sepWPp_weaken_pre
      (P' := (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (fsp + 0x23b0#64) k) ∗ errRest)
      (Entails.of_eq (by dsimp only [errRest, r1c_okCore]; ac_rfl))
    simp only [sepExists_sepConj_left]
    apply r1c_sepWPp_exists_left; intro k
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_tail (g' := g') (d := d2) (k := k) hh hdrop hstk32 hext_le hsub64 hs_m hx19_m' hx20_m' hx21_m'
        htr_m hhist_m hans hrej)
    exact Entails.of_eq (by dsimp only [errRest, fsp, dirG])

theorem run_hop_init3_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopInit3Placed (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack :=
  run_hop_init3_of_slots (needs := needs) rfl rfl

end CryptoVerification.SignalSession.Cli.RunCompose
