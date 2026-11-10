/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# `signal_session::run` Arm `R1c` Placed Tail Stepping

Relocatable (`[LibsignalPlacement]`) stepping proofs on Block `579` (`runProgPlaced H`) for the
Arm `R1c` success tail (`r1c_ok_tail`, `R+0x2908 → R+0xf8c`) and error deallocation steps
(`r1c_err_free_peer`, `r1c_err_free_dir`, `r1c_err_free_me`, `R+0x2a20 → R+0x2c7c`).
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

theorem r1c_ok_free_peer [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {peerG : AddrGhost} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2988)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced R1cCodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp
  let mid := memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  let core := r1c_okCore A g g' s0
  have hrejoin_peer :
      (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗ mid ⊢
      runLocals fsp [(0x208, 24, vecU8 A (fsp + 0x208#64) [])] := by
    have hp32 :
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16 ⊢ memRegion (fsp + 0x2a0#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x2a0#64) (n := 8) (k := 24) (b' := fsp + 0x2a8#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x2a8#64) (n := 8) (k := 16) (b' := fsp + 0x2b0#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero, mid]
    rw [show fsp + BitVec.ofNat 64 0 = fsp by bv_omega,
        show (0x208 : Nat) + 24 = 0x220 from rfl,
        r1c_split_at fsp 0x220 (0x2a0 - 0x220) runLocalBytes (by decide) (by decide),
        r1c_split_at fsp 0x2a0 32 runLocalBytes (by decide) (by decide)]
    exact r1c_rewrite_front
      (memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))
      hp32 (by ac_rfl) (by ac_rfl)
  by_cases hcap : peerG.name.cap = 0#64
  · have hstep : SepWP (runProgPlaced H) (runPcPlaced 0xf8c) s
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq, hcap, show fsp = s.sp from hsp.symm]
      clear hsp; wp_steps
      apply SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := (((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x2b0#64) 16) ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A peerG hcap))
        (Entails.of_eq (by dsimp only [mid, core]; rw [emp_sepConj]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    have hat : AtJoinPlaced R1cCodeOk g g' [] s0 s1 :=
      { base := ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        x19 := hx19_1, x20 := hx20_1
        trace := htr1 ▸ htr
        hist := r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist
        ans := hans
        wrOk := hwr }
    refine r1c_sepWPp_weaken_pre ?_ (hjoin s1 g' [] hat)
    dsimp only [joinMem]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hrejoin_peer (by ac_rfl) (by dsimp only [core, r1c_okCore, fsp]; ac_rfl)
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced 0xf8c ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
          s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr)))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A peerG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        memRegion (fsp + 0x2b0#64) 16 ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hs.inv (Entails.of_eq (by dsimp only [mid, core]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ mid ∗ core))
      (Entails.of_eq (by ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hat : AtJoinPlaced R1cCodeOk g g' [] s0 s2 :=
      { base := ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
        x19 := hx19_2.trans hx19_1
        x20 := hx20_2.trans hx20_1
        trace := (htr2.trans htr1) ▸ htr
        hist := r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist
        ans := hans
        wrOk := hwr }
    refine r1c_sepWPp_weaken_pre ?_ (hjoin s2 g' [] hat)
    dsimp only [joinMem]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hrejoin_peer (by ac_rfl) (by dsimp only [core, r1c_okCore, fsp]; ac_rfl)

theorem r1c_ok_free_dir [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2974)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced R1cCodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A dirG ∗ r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
        vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let rest := memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
    vecU8 A (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
    addrNameHeap A d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0
  have hlow208 : r1c_lowCells fsp d ∗ memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ⊢
      memRegion fsp 0x208 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x208 - 0x1d0)
          (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (r1c_lowCells_to_mem1d0 fsp d)
  have hlow_eq : (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
      r1c_lowNoDir fsp d = r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, r1c_lowNoDir]; ac_rfl
  by_cases hcap : d.dirCap = 0#64
  · have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2988) s
        ((fsp + 0x1c0#64) ↦₆₄ d.dirCap)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = ((fsp + 0x1c0#64) ↦₆₄ d.dirCap)) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq, hcap, show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowNoDir fsp d ∗ rest)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A dirG hcap))
        (Entails.of_eq (by dsimp only [rest]; rw [emp_sepConj, ← hlow_eq]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    have hs1 : InRunPlaced R1cCodeOk s0 s1 0x2988 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_peer (peerG := d.peerG) hh hext_le hsub64 hs1 hx19_1 hx20_1
        (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist) hans hwr hjoin)
    exact r1c_rewrite_front
      (vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hlow208 (by dsimp only [rest]; rw [← hlow_eq]; ac_rfl) (by dsimp only [fsp]; ac_rfl)
  · have hbeq : (d.dirCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced 0x2988 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.dirPtr ∧ s1.readReg64 .x1 = d.dirCap ∧
          s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A dirG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        r1c_lowNoDir fsp d ∗ rest)
      hs.inv (Entails.of_eq (by dsimp only [dirG, rest]; rw [← hlow_eq]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
          r1c_lowNoDir fsp d ∗
          memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
          vecU8 A (fsp + 0x208#64) [] ∗
          memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
          addrNameHeap A d.peerG ∗
          (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗
          memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗ r1c_okCore A g g' s0))
      (Entails.of_eq (by dsimp only [rest]; ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hs2 : InRunPlaced R1cCodeOk s0 s2 0x2988 :=
      ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_peer (peerG := d.peerG) hh hext_le hsub64 hs2 (hx19_2.trans hx19_1) (hx20_2.trans hx20_1)
        ((htr2.trans htr1) ▸ htr)
        (r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist)
        hans hwr hjoin)
    exact r1c_rewrite_front
      (vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hlow208 (by rw [← hlow_eq]; ac_rfl) (by dsimp only [fsp]; ac_rfl)

theorem r1c_ok_free_me [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2960)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced R1cCodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
        vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let afterLow := memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
    vecU8 A (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
    addrNameHeap A d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  have hlow_eq : ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ r1c_lowNoMePtr fsp d =
      r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, r1c_lowNoMePtr]; ac_rfl
  by_cases hcap : d.meG.name.cap = 0#64
  · have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2974) s emp
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = emp) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq]; rw [hcap] at hx21; wp_steps
      apply SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := addrNameHeap A dirG ∗ r1c_lowCells fsp d ∗ afterLow ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A d.meG hcap))
        (Entails.of_eq (by dsimp only [afterLow]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    have hs1 : InRunPlaced R1cCodeOk s0 s1 0x2974 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_dir (d := d) hh hext_le hsub64 hs1 hx19_1 hx20_1
        (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist) hans hwr hjoin)
    exact Entails.of_eq (by dsimp only [afterLow, dirG, fsp]; rw [emp_sepConj]; ac_rfl)
  · have hbeq : (d.meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced 0x2974 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.meG.name.ptr ∧ s1.readReg64 .x1 = d.meG.name.cap ∧
          s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A d.meG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        addrNameHeap A dirG ∗ r1c_lowNoMePtr fsp d ∗ afterLow ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hs.inv (Entails.of_eq (by dsimp only [afterLow]; rw [← hlow_eq]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        (((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
          addrNameHeap A dirG ∗ r1c_lowNoMePtr fsp d ∗ afterLow ∗ r1c_okCore A g g' s0))
      (Entails.of_eq (by ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hs2 : InRunPlaced R1cCodeOk s0 s2 0x2974 :=
      ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_dir (d := d) hh hext_le hsub64 hs2 (hx19_2.trans hx19_1) (hx20_2.trans hx20_1)
        ((htr2.trans htr1) ▸ htr)
        (r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist)
        hans hwr hjoin)
    exact Entails.of_eq (by dsimp only [afterLow, dirG, fsp]; rw [← hlow_eq]; ac_rfl)

theorem r1c_ok_tail [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2908)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced R1cCodeOk H A g s0 resStack Q Qp) :
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
  have hcarve : memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ⊢
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (((fsp + 0x208#64) ↦₆₄ v0) ∗ ((fsp + 0x210#64) ↦₆₄ v1) ∗ ((fsp + 0x218#64) ↦₆₄ v2)) ∗
          memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
          memRegion (fsp + 0x220#64) (0x2a0 - 0x220) := by
    rw [r1c_split_at fsp 0x1d0 (0x208 - 0x1d0) 0x2a0 (by decide) (by decide),
        show (0x1d0 : Nat) + (0x208 - 0x1d0) = 0x208 from rfl,
        r1c_split_at fsp 0x208 24 0x2a0 (by decide) (by decide),
        show (0x208 : Nat) + 24 = 0x220 from rfl]
    rw [ProofLib.memRegion_split' (b := fsp + 520#64) (n := 8) (k := 16) (b' := fsp + 528#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 528#64) (n := 8) (k := 8) (b' := fsp + 536#64) rfl (by bv_omega) (by decide)]
    simp only [ProofLib.memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v2
    apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v0
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.of_eq (by ac_rfl))))
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        r1c_lowCells fsp d ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hcarve (by ac_rfl) rfl)
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro v0
  apply r1c_sepWPp_exists_left; intro v1
  apply r1c_sepWPp_exists_left; intro v2
  let lowRest := ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hlow_eq :
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗ lowRest =
      r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, lowRest]; ac_rfl
  let tailHold := addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
    lowRest ∗ memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗ r1c_okCore A g g' s0
  have hstep1 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
      ((((fsp + 0x208#64) ↦₆₄ v0) ∗ ((fsp + 0x210#64) ↦₆₄ v1) ∗ ((fsp + 0x218#64) ↦₆₄ v2)) ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)))
      (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
        s1.readReg64 .lr = runPcPlaced 0x2930 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 .x0 = d.spkSigPtr ∧ s1.readReg64 .x1 = 64#64 ∧ s1.readReg64 .x2 = 1#64 ∧
        s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
        s1.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P1 = ((((fsp + 0x208#64) ↦₆₄ 0#64) ∗ ((fsp + 0x210#64) ↦₆₄ 1#64) ∗
            ((fsp + 0x218#64) ↦₆₄ 0#64)) ∗
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
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ tailHold)
    hs.inv (Entails.of_eq (by dsimp only [tailHold]; rw [← hlow_eq]; ac_rfl)) hstep1
    fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1⟩ => ?_
  have hv8 : (((fsp + 0x208#64) ↦₆₄ 0#64) ∗ ((fsp + 0x210#64) ↦₆₄ 1#64) ∗
      ((fsp + 0x218#64) ↦₆₄ 0#64)) ⊢ vecU8 A (fsp + 0x208#64) [] := by
    rw [show fsp + 0x210#64 = (fsp + 0x208#64) + 8#64 by bv_omega,
        show fsp + 0x218#64 = (fsp + 0x208#64) + 16#64 by bv_omega]
    exact r1c_empty_vecU8 A (fsp + 0x208#64)
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      (vecU8 A (fsp + 0x208#64) [] ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗ tailHold))
    (r1c_rewrite_front
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗ tailHold)
      hv8 (by ac_rfl) (by ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
      hx0_1 (by rw [hx1_1]; rfl) hx2_1 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, _, _, _, _, _, _, hfp2, hv2⟩
  have hstep2 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s2
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr))
      (fun s3 P3 => (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
        s3.readReg64 .lr = runPcPlaced 0x2948 ∧
        calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
        s3.readReg64 .x0 = d.kpkPtr ∧ s3.readReg64 .x1 = 1568#64 ∧ s3.readReg64 .x2 = 1#64 ∧
        s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
        s3.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P3 = (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)))
      (fun _ => ⌜False⌝) := by
    rw [runPcPlaced_eq] at hpc2
    have hfp := hfp2.trans hfp1; have hv := hv2.trans hv1
    have hx19' := hx19_2.trans hx19_1; have hx20' := hx20_2.trans hx20_1
    have hx21' := hx21_2.trans hx21_1
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
      vecU8 A (fsp + 0x208#64) [] ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ tailHold)
    hinv2 (Entails.of_eq (by dsimp only [fsp]; ac_rfl)) hstep2
    fun s3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx21_3⟩ => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      ((A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        vecU8 A (fsp + 0x208#64) [] ∗ tailHold))
    (Entails.of_eq (by ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv3 hpc3 hrun3 hsp3 hlr3
      hx0_3 (by rw [hx1_3]; rfl) hx2_3 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s4 hinv4 hpc4 hrun4 hsp4 hcs4 hfs4 htr4 => ?_)
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, _, _, _, _, _, _, _, hfp4, hv4⟩
  have hstep3 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s4
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64))
      (fun s5 P5 => (s5.sp = fsp ∧ s5.readReg64 .fp = s0.sp - 0x60#64 ∧
        s5.readReg64 .lr = runPcPlaced 0x2960 ∧
        calleeSavedVRegs s5 = calleeSavedVRegs s0 ∧ s5.trace = s4.trace ∧ s5.fs = s4.fs ∧
        s5.readReg64 .x0 = d.kpkSigPtr ∧ s5.readReg64 .x1 = 64#64 ∧ s5.readReg64 .x2 = 1#64 ∧
        s5.readReg64 (.gpr 19#5) = g.stores ∧ s5.readReg64 (.gpr 20#5) = g.res ∧
        s5.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P5 = (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)))
      (fun _ => ⌜False⌝) := by
    rw [runPcPlaced_eq] at hpc4
    have hfp := hfp4.trans hfp3; have hv := hv4.trans hv3
    have hx19' := hx19_4.trans hx19_3; have hx20' := hx20_4.trans hx20_3
    have hx21' := hx21_4.trans hx21_3
    have hal : s4.spAligned = true := r1c_spAligned hs.spAligned hsp4
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s4.sp from hsp4.symm]; clear hsp4; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, by ac_rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
      vecU8 A (fsp + 0x208#64) [] ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ tailHold)
    hinv4 (Entails.of_eq (by dsimp only [fsp]; ac_rfl)) hstep3
    fun s5 hinv5 hpc5 hrun5 ⟨hsp5, hfp5, hlr5, hv5, htr5, hfs5, hx0_5, hx1_5, hx2_5, hx19_5, hx20_5, hx21_5⟩ => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      ((((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        vecU8 A (fsp + 0x208#64) [] ∗ tailHold))
    (Entails.of_eq (by ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv5 hpc5 hrun5 hsp5 hlr5
      hx0_5 (by rw [hx1_5]; rfl) hx2_5 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s6 hinv6 hpc6 hrun6 hsp6 hcs6 hfs6 htr6 => ?_)
  rcases hcs6 with ⟨hx19_6, hx20_6, hx21_6, _, _, _, _, _, _, _, hfp6, hv6⟩
  have hs6 : InRunPlaced R1cCodeOk s0 s6 0x2960 :=
    ⟨hpc6, hrun6, hsp6, hfp6.trans hfp5, hinv6, hv6.trans hv5, hs.spAligned⟩
  have htr_all : s6.trace = s.trace :=
    ((((htr6.trans htr5).trans htr4).trans htr3).trans htr2).trans htr1
  have hfs_all : s6.fs = s.fs :=
    ((((hfs6.trans hfs5).trans hfs4).trans hfs3).trans hfs2).trans hfs1
  refine r1c_sepWPp_weaken_pre ?_
    (r1c_ok_free_me (d := d) hh hext_le hsub64 hs6
      (hx19_6.trans hx19_5) (hx20_6.trans hx20_5) (hx21_6.trans hx21_5)
      (htr_all ▸ htr) (r1c_hist_of_eq htr_all (congrArg FsState.files hfs_all) hhist)
      hans hwr hjoin)
  exact Entails.of_eq (by dsimp only [tailHold, dirG, fsp]; rw [← hlow_eq]; ac_rfl)

theorem r1c_err_free_peer [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {peerG : AddrGhost} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2c68)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced R1cCodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion fsp 0x2a0 ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp
  let mid := memRegion fsp 0x2a0 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  let core := r1c_errCore A g g' s0
  have hrejoin_peer :
      (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗ mid ⊢ runLocals fsp [] := by
    have hp32 :
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16 ⊢ memRegion (fsp + 0x2a0#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x2a0#64) (n := 8) (k := 24) (b' := fsp + 0x2a8#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x2a8#64) (n := 8) (k := 16) (b' := fsp + 0x2b0#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
    dsimp only [runLocals, runLocalsFrom, mid]
    rw [r1c_split_at fsp 0 0x2a0 runLocalBytes (by decide) (by decide),
        show (0 : Nat) + 0x2a0 = 0x2a0 from rfl,
        r1c_split_at fsp 0x2a0 32 runLocalBytes (by decide) (by decide),
        show (0x2a0 : Nat) + 32 = 0x2c0 from rfl,
        show fsp + BitVec.ofNat 64 0 = fsp by bv_omega]
    exact r1c_rewrite_front (memRegion fsp 0x2a0 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))
      hp32 (by ac_rfl) (by ac_rfl)
  by_cases hcap : peerG.name.cap = 0#64
  · have hstep : SepWP (runProgPlaced H) (runPcPlaced RejectKind.postDispatch.pcOff) s
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579, RejectKind.pcOff]
      rw [runPcPlaced_eq, hcap, show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := (((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x2b0#64) 16) ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A peerG hcap))
        (Entails.of_eq (by dsimp only [mid, core]; rw [emp_sepConj]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    have hat : AtRejectPlaced R1cCodeOk g g' .postDispatch s0 s1 :=
      { base := ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        x19 := hx19_1
        preRegs := by rintro ⟨⟩
        trace := htr1 ▸ htr
        hist := r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist
        ans := hans }
    refine r1c_sepWPp_weaken_pre ?_ (hrej s1 g' .postDispatch hat)
    dsimp only [rejectMem]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hrejoin_peer (by ac_rfl) (by dsimp only [core, r1c_errCore, fsp]; ac_rfl)
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced RejectKind.postDispatch.pcOff ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
          s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr)))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579, RejectKind.pcOff]
      rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A peerG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        memRegion (fsp + 0x2b0#64) 16 ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hs.inv (Entails.of_eq (by dsimp only [mid, core]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ mid ∗ core))
      (Entails.of_eq (by ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hat : AtRejectPlaced R1cCodeOk g g' .postDispatch s0 s2 :=
      { base := ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
        x19 := hx19_2.trans hx19_1
        preRegs := by rintro ⟨⟩
        trace := (htr2.trans htr1) ▸ htr
        hist := r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist
        ans := hans }
    refine r1c_sepWPp_weaken_pre ?_ (hrej s2 g' .postDispatch hat)
    dsimp only [rejectMem]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hrejoin_peer (by ac_rfl) (by dsimp only [core, r1c_errCore, fsp]; ac_rfl)

theorem r1c_err_free_dir [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2c54)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx22 : s.readReg64 (.gpr 22#5) = d.dirPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = d.dirCap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced R1cCodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion fsp 0x2a0 ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let peerPayload := addrNameHeap A d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion fsp 0x2a0 ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  by_cases hcap : d.dirCap = 0#64
  · have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2c68) s emp
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = emp) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq]; rw [hcap] at hx24; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := peerPayload ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A dirG hcap))
        (Entails.of_eq (by dsimp only [peerPayload]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    have hs1 : InRunPlaced R1cCodeOk s0 s1 0x2c68 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_peer (g' := g') (peerG := d.peerG) hh hext_le hsub64 hs1 hx19_1
        (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist) hans hrej)
    exact Entails.of_eq (by dsimp only [peerPayload, fsp]; rw [emp_sepConj]; ac_rfl)
  · have hbeq : (d.dirCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s emp
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced 0x2c68 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.dirPtr ∧ s1.readReg64 .x1 = d.dirCap ∧
          s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = emp) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A dirG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        peerPayload ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hs.inv (Entails.of_eq (by dsimp only [dirG, peerPayload]; rw [emp_sepConj]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        (peerPayload ∗ r1c_errCore A g g' s0))
      (Entails.of_eq (by rw [emp_sepConj]; ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hs2 : InRunPlaced R1cCodeOk s0 s2 0x2c68 :=
      ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_peer (g' := g') (peerG := d.peerG) hh hext_le hsub64 hs2 (hx19_2.trans hx19_1)
        ((htr2.trans htr1) ▸ htr)
        (r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist)
        hans hrej)
    exact Entails.of_eq (by dsimp only [peerPayload, fsp]; ac_rfl)

theorem r1c_err_free_me [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2a20)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced R1cCodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  have hlow2a0 : r1c_lowCells fsp d ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ⊢
      memRegion fsp 0x2a0 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x2a0 - 0x1d0)
          (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (r1c_lowCells_to_mem1d0 fsp d)
  let tailRest := addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
    memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0
  have hlow_dir : (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
      r1c_lowNoDir fsp d = r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, r1c_lowNoDir]; ac_rfl
  by_cases hcap : d.meG.name.cap = 0#64
  · have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2c54) s
        (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧
          s1.readReg64 (.gpr 22#5) = d.dirPtr ∧ s1.readReg64 (.gpr 24#5) = d.dirCap) ∧
          P1 = (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq, show fsp = s.sp from hsp.symm]; rw [hcap] at hx21; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, by ac_rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := r1c_lowNoDir fsp d ∗ tailRest)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A d.meG hcap))
        (Entails.of_eq (by dsimp only [tailRest]; rw [emp_sepConj, ← hlow_dir]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx22_1, hx24_1⟩ => ?_
    have hs1 : InRunPlaced R1cCodeOk s0 s1 0x2c54 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_dir (g' := g') (d := d) hh hext_le hsub64 hs1 hx19_1 hx22_1 hx24_1
        (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist) hans hrej)
    exact r1c_rewrite_front
      (addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hlow2a0 (by dsimp only [tailRest]; rw [← hlow_dir]; ac_rfl) (by dsimp only [dirG, fsp]; ac_rfl)
  · have hbeq : (d.meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hlow_me : ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ r1c_lowNoMePtr fsp d =
        r1c_lowCells fsp d := by
      dsimp only [r1c_lowCells, r1c_lowNoMePtr]; ac_rfl
    have hstep1 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced 0x2a34 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.meG.name.ptr ∧ s1.readReg64 .x1 = d.meG.name.cap ∧
          s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A d.meG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        r1c_lowNoMePtr fsp d ∗ tailRest)
      hs.inv (Entails.of_eq (by dsimp only [tailRest]; rw [← hlow_me]; ac_rfl)) hstep1
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
          r1c_lowNoDir fsp d ∗
          addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗
          memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗ r1c_errCore A g g' s0))
      (Entails.of_eq (by dsimp only [tailRest, r1c_lowNoMePtr, r1c_lowNoDir]; ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hstep2 : SepWP (runProgPlaced H) (runPcPlaced 0x2c54) s2
        (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))
        (fun s3 P3 => (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
          s3.readReg64 (.gpr 19#5) = g.stores ∧
          s3.readReg64 (.gpr 22#5) = d.dirPtr ∧ s3.readReg64 (.gpr 24#5) = d.dirCap) ∧
          P3 = (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)))
        (fun _ => ⌜False⌝) := by
      rw [runPcPlaced_eq] at hpc2
      have hfp := hfp2.trans hfp1; have hv := hv2.trans hv1
      have hx19' := hx19_2.trans hx19_1
      have hal : s2.spAligned = true := r1c_spAligned hs.spAligned hsp2
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq, show fsp = s2.sp from hsp2.symm]; clear hsp2; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, by ac_rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := r1c_lowNoDir fsp d ∗
        addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hinv2 (Entails.of_eq (by dsimp only [fsp]; ac_rfl)) hstep2
      fun s3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hv3, htr3, hfs3, hx19_3, hx22_3, hx24_3⟩ => ?_
    have hs3 : InRunPlaced R1cCodeOk s0 s3 0x2c54 :=
      ⟨hpc3, hrun3, hsp3, hfp3, hinv3, hv3, hs.spAligned⟩
    have htr_all : s3.trace = s.trace := (htr3.trans htr2).trans htr1
    have hfs_all : s3.fs = s.fs := (hfs3.trans hfs2).trans hfs1
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_dir (g' := g') (d := d) hh hext_le hsub64 hs3 hx19_3 hx22_3 hx24_3
        (htr_all ▸ htr) (r1c_hist_of_eq htr_all (congrArg FsState.files hfs_all) hhist) hans hrej)
    exact r1c_rewrite_front
      (addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hlow2a0 (by rw [← hlow_dir]; ac_rfl) (by dsimp only [dirG, fsp]; ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers
