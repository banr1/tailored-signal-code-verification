/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `signal_session::run` Arm `R3b`: Placed Bad-Wire and Reject Sub-Hop

Proves `run_hop_recvBad_placed_ok` (`RunHopRecvBadPlaced`) and shared `Recv` dispatch-head /
reject-cleanup lemmas on Block `579` (`runProgPlaced H`) under `[LibsignalPlacement]`.
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
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-! ## 1. Error-Cleanup Tail `R+0x1008 → R+0x2c7c` and `R+0xfec → R+0x2c7c` -/

/-- Shared `peer` deallocation block `R+0x1008 → R+0x2c7c` (`AtRejectPlaced .postDispatch`). -/
theorem r3b_reject_from_1008_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (peerG : AddrGhost) (u230 u238 : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0x1008)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  let fsp := runFsp s0
  have hloc_rejoin :
      memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ⊢
      runLocals fsp [] := by
    have h4 :
        ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238) ⊢
        memRegion (fsp + 0x220#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 8) (k := 24)
            (b' := fsp + 0x228#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x228#64) (n := 8) (k := 16)
            (b' := fsp + 0x230#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x230#64) (n := 8) (k := 8)
            (b' := fsp + 0x238#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    have hwf : RunLocalsFromWf 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have hrej0 := runLocals_rejoin_empty fsp [(0x220, 32, memRegion (fsp + 0x220#64) 32)]
      hwf (by intro c hc; simp at hc; subst hc; exact Entails.refl _)
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero] at hrej0 ⊢
    rw [hz] at hrej0 ⊢
    rw [show BitVec.ofNat 64 (0x220 + 32) = 0x240#64 from rfl] at hrej0
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left h4)) hrej0
  by_cases hcap : peerG.name.cap = 0#64
  · have hpc : s.pc = runPcPlaced 0x1008 := hs.pc
    change s.pc = (blkPl_579).base + 0x1008#64 at hpc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = fsp := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_seq (mid := runPcPlaced 0x2c7c) hs.inv
    rw [runPcPlaced_eq, hcap, show runFsp s0 = s.sp from hsp.symm]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv'
    have hs' : InRunPlaced CodeOk s0 _ 0x2c7c :=
      r3b_inRun_step hs (by simp only [runPcPlaced_eq, arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv' (by simp only [calleeSavedVRegs, arm64_norm])
    have hat : AtRejectPlaced CodeOk g g' .postDispatch s0 _ :=
      { base := hs'
        x19 := by simp only [arm64_norm, hx19]
        preRegs := fun hk => nomatch hk
        trace := by simpa only [arm64_norm] using htr
        hist := r3b_hist_of_eq (by simp only [arm64_norm]) (by simp only [arm64_norm]) hhist
        ans := hans }
    refine r3b_sepWPp_weaken_pre ?_ (hrej _ g' .postDispatch hat)
    rw [hsp, ← hcap]
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_nameHeap_zero A peerG hcap)
          (sepConj_mono hloc_rejoin
            (Entails.refl (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap))))
        (by rw [emp_sepConj]; dsimp only [rejectMem]; ac_rfl))
      (by ac_rfl)
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hpc : s.pc = runPcPlaced 0x1008 := hs.pc
    change s.pc = (blkPl_579).base + 0x1008#64 at hpc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = fsp := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A peerG hcap))))))
    rw [show (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        runSaved s0 ∗ memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat ∗
          runSaved s0 ∗ memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) by ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlay
    apply r3b_seq (mid := lsρ lsRustDeallocSymCli) hs.inv
    rw [← hsp]
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun])
    intro hinv_c
    have hstk_split := r3b_stackAt_split_ge s.sp hext_le hsub64
    refine r3b_call_lscro
      (F := runResAt A cliWrOk g.res (some none) ∗
        memRegion g.call 56 ∗
        storesAt A g.stores g' ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗
        memRegion s.sp 0x220 ∗
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((s.sp + 0x230#64) ↦₆₄ u230) ∗
          ((s.sp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (s.sp + 0x240#64) (runLocalBytes - 0x240) ∗
        memRegion (s.sp - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - extHookStack) ∗
        anyHeap)
      (s0 := s0) (peerG.name.ptr, peerG.name.cap.toNat, 1)
      (r3b_dealloc_ok hh) hinv_c
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al)
      (retAddr := runPcPlaced 0x2c7c)
      (by simp only [runPcPlaced_eq, arm64_norm])
      ?_
      (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], hlay⟩
      rw [hstk_split]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; intro hfs_m
      apply r3b_sepWPp_pure_left; intro htr_m
      have hs_m : InRunPlaced CodeOk s0 sm 0x2c7c :=
        r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
      have hfs_tot : sm.fs = s.fs := hfs_m.trans (by simp only [arm64_norm])
      have hat : AtRejectPlaced CodeOk g g' .postDispatch s0 sm :=
        { base := hs_m
          x19 := hcsm.1.trans (by simp only [arm64_norm, hx19])
          preRegs := fun hk => nomatch hk
          trace := htr_tot ▸ htr
          hist := r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist
          ans := hans }
      refine r3b_sepWPp_weaken_pre ?_ (hrej sm g' .postDispatch hat)
      rw [hsp] at hstk_split
      dsimp only [rejectMem, fsp] at hloc_rejoin hstk_split ⊢
      simp only [arm64_norm, hsp]
      rw [hstk_split]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono hloc_rejoin
            (Entails.refl (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗
              memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
                (resStack - runFrame - extHookStack) ∗
              stackAt (runFsp s0) extHookStack ∗ A.pool ∗ anyHeap)))
          (by simp only [arm64_norm]; ac_rfl))
        (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)

/-- Shared reject tail from `R+0xfec → R+0x2c7c` when `me = .some meV meG`:
writes `-1` to `[g.res]`, frees `meG.name`, and finishes via `r3b_reject_from_1008_placed`. -/
theorem r3b_reject_from_fec_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (meG peerG : AddrGhost) (u230 u238 : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0xfec)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A meG ∗ addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  have hres_split : memRegion g.res runResSize =
      (∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]
    exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  rw [hres_split]
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro vr
  by_cases hcap : meG.name.cap = 0#64
  · have hpc : s.pc = runPcPlaced 0xfec := hs.pc
    change s.pc = (blkPl_579).base + 0xfec#64 at hpc
    have hrun : s.status = .Running := hs.run
    apply r3b_seq (mid := runPcPlaced 0x1008) hs.inv
    rw [runPcPlaced_eq]
    rw [hcap] at hx21
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv'
    have hs1 : InRunPlaced CodeOk s0 _ 0x1008 :=
      r3b_inRun_step hs (by simp only [runPcPlaced_eq, arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv' (by simp only [calleeSavedVRegs, arm64_norm])
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_reject_from_1008_placed g' peerG u230 u238 hh hext_le hsub64 hs1
        (by simp only [arm64_norm, hx19])
        (by simpa only [arm64_norm] using htr)
        (r3b_hist_of_eq (by simp only [arm64_norm]) (by simp only [arm64_norm]) hhist)
        hans
        hrej)
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_nameHeap_zero A meG hcap)
          (Entails.refl (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            memRegion (runFsp s0) 0x220 ∗
            (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
              ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
            memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
        (by rw [emp_sepConj]))
      (by dsimp only [runResAt]; ac_rfl)
  · have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hbeq21 : (s.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21]; exact hbeq
    have hpc : s.pc = runPcPlaced 0xfec := hs.pc
    change s.pc = (blkPl_579).base + 0xfec#64 at hpc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = runFsp s0 := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A meG hcap))))))
    rw [show (((g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
        (((g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) by ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlay
    apply r3b_seq (mid := lsρ lsRustDeallocSymCli) hs.inv
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun])
    intro hinv_c
    have hstk_split := r3b_stackAt_split_ge s.sp hext_le hsub64
    refine r3b_call_lscro
      (F := ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        memRegion g.call 56 ∗
        storesAt A g.stores g' ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - extHookStack) ∗
        anyHeap)
      (s0 := s0) (meG.name.ptr, meG.name.cap.toNat, 1)
      (r3b_dealloc_ok hh) hinv_c
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al)
      (retAddr := runPcPlaced 0x1008)
      (by simp only [runPcPlaced_eq, arm64_norm])
      ?_
      (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm]; try rw [hx28],
          by simp only [arm64_norm]; try rw [hx21], by simp only [arm64_norm], hlay⟩
      rw [hsp] at hstk_split
      rw [hstk_split]
      simp only [arm64_norm, hsp]
      exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; intro hfs_m
      apply r3b_sepWPp_pure_left; intro htr_m
      have hs_m : InRunPlaced CodeOk s0 sm 0x1008 :=
        r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
      have hfs_tot : sm.fs = s.fs := hfs_m.trans (by simp only [arm64_norm])
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_reject_from_1008_placed g' peerG u230 u238 hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [arm64_norm, hx19]))
          (htr_tot ▸ htr)
          (r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist)
          hans
          hrej)
      rw [hsp] at hstk_split
      rw [hstk_split]
      simp only [arm64_norm, hsp]
      exact Entails.of_eq (by dsimp only [runResAt]; ac_rfl)

/-! ## 2. Dispatch Head `me = .none` and `me = .some` Step Lemmas -/

/-- Shared `me = .none` path (`R+0x214 → R+0x4b0 → R+0x7a4 → R+0x86c → R+0x1008 → R+0x2c7c`). -/
theorem r3b_me_none_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerV : AddrV} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hres : runNeed B (slotsOfPlaced A S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g .none s0 s)
    (hcall : g.c = .recv peerV)
    (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A g .none s0 resStack) Q Qp (runOom s0) := by
  have hbnds := runNeed_bounds_placed hres hres64
  have hext_le : extHookStack ≤ resStack - runFrame := by
    have := hbnds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnds.2.2.1
  have hans : g.a = some none := hd.reject_of_me_none he
  let fsp := runFsp s0
  dsimp only [dispatchMemPlaced, dispatchMeHeap, dispatchCells]
  rw [hcall]
  dsimp only [callAt, callHeap, addrWords]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r3b_sepWPp_exists_left; intro cw
  have hres_split : memRegion g.res runResSize =
      (∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]
    exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  have hloc_split : runLocals fsp [] =
      memRegion fsp 0x220 ∗ memRegion (fsp + 0x220#64) 32 ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
    have hwf : RunLocalsFromWf 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have h0 := r3b_memRegion_to_runLocalsFrom fsp 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)]
      hwf (by intro c hc; simp at hc; subst hc; rfl)
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero] at h0 ⊢
    rw [hz] at h0 ⊢
    rw [show BitVec.ofNat 64 (0x220 + 32) = 0x240#64 from rfl,
        show 0x220 + 32 = 0x240 from rfl] at h0
    exact h0
  rw [hres_split, hloc_split]
  let peerG : AddrGhost := ⟨⟨cw.w1, cw.w2, peerV.name⟩, peerV.device⟩
  have hpre_prep :
      (((∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
          ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
          ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
          ⌜cw.w0 = 0x8000000000000003#64⌝ ∗
          (ownedBytes A cw.w1 cw.w2 cw.w3 peerV.name ∗ ⌜cw.w4.setWidth 8 = peerV.device⌝)) ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.recv peerV)) ∗
        coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ emp ∗
        runSaved s0 ∗
        (memRegion fsp 0x220 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240)) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool) ⊢
      ∃∗ vr, ∃∗ u0, ∃∗ u1, ∃∗ u2, ∃∗ u3,
        (g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
        (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
        ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
        ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion fsp 0x220 ∗
        ((fsp + 0x220#64) ↦₆₄ u0) ∗ ((fsp + 0x228#64) ↦₆₄ u1) ∗
        ((fsp + 0x230#64) ↦₆₄ u2) ∗ ((fsp + 0x238#64) ↦₆₄ u3) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap := by
    rw [← hcall, emp_sepConj]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono (r3b_ownedBytes_entails_nameHeap A cw.w1 cw.w2 cw.w3 peerV.name)
          (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x220#64))
            (sepConj_mono
              (entails_anyHeap (⌜cw.w0 = 0x8000000000000003#64⌝ ∗ ⌜cw.w4.setWidth 8 = peerV.device⌝ ∗
                coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
                SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff))
              (Entails.refl ((∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
                (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
                ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
                ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
                storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ memRegion fsp 0x220 ∗
                memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool)))))
        (by ac_rfl))
      ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro vr
    apply Entails.sepExists_elim; intro u0
    apply Entails.sepExists_elim; intro u1
    apply Entails.sepExists_elim; intro u2
    apply Entails.sepExists_elim; intro u3
    simp only [sepConj_assoc]
    apply Entails.pure_left; intro _
    rw [r3b_addrNameHeap_dev_congr A ⟨cw.w1, cw.w2, peerV.name⟩ 0#8 peerV.device]
    have ha8 : fsp + 0x220#64 + 8#64 = fsp + 0x228#64 := by bv_omega
    have ha16 : fsp + 0x220#64 + 16#64 = fsp + 0x230#64 := by bv_omega
    have ha24 : fsp + 0x220#64 + 24#64 = fsp + 0x238#64 := by bv_omega
    rw [ha8, ha16, ha24]
    exact Entails.sepExists_right vr (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
        (Entails.sepExists_right u3 (Entails.of_eq (by ac_rfl))))))
  apply r3b_sepWPp_weaken_pre hpre_prep
  apply r3b_sepWPp_exists_left; intro vr
  apply r3b_sepWPp_exists_left; intro u0
  apply r3b_sepWPp_exists_left; intro u1
  apply r3b_sepWPp_exists_left; intro u2
  apply r3b_sepWPp_exists_left; intro u3
  have hpc : s.pc = runPcPlaced 0x214 := hd.base.pc
  change s.pc = (blkPl_579).base + 0x214#64 at hpc
  have hrun : s.status = .Running := hd.base.run
  have hsp : s.sp = fsp := hd.base.sp
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa [hcall, CallV.tag] using hd.x8
  have hx20 : s.readReg64 (.gpr 20#5) = g.res := hd.x20
  have hx21 : s.readReg64 (.gpr 21#5) = noneCap := hd.meRegs
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  apply r3b_seq (mid := runPcPlaced 0x1008) hd.base.inv
  dsimp only [noneCap] at hx21
  rw [runPcPlaced_eq, ← hsp]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv1
  have hs1 : InRunPlaced CodeOk s0 _ 0x1008 :=
    r3b_inRun_step hd.base (by simp only [runPcPlaced_eq, arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1 (by simp only [calleeSavedVRegs, arm64_norm])
  have hhist : RunHistOk g.i s0 _ :=
    ⟨by simpa only [arm64_norm] using hd.fs, by simpa only [arm64_norm] using hd.stdout⟩
  refine r3b_sepWPp_weaken_pre ?_
    (r3b_reject_from_1008_placed StoresGhost.opened peerG cw.w3 cw.w4 hh hext_le hsub64 hs1
      (by simp only [arm64_norm, hd.x19])
      (by simpa only [arm64_norm] using hd.trace)
      hhist hans hrej)
  rw [hsp]
  exact r3b_perm
    (r3b_perm_post
      (sepConj_mono (r3b_call7_to_memRegion56 g.call cw)
        (Entails.refl (runResAt A cliWrOk g.res (some none) ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ cw.w3) ∗
            ((fsp + 0x238#64) ↦₆₄ cw.w4)) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
      (by dsimp only [fsp]; ac_rfl))
    (by dsimp only [fsp, runResAt, peerG]; ac_rfl)

/-- Shared `me = .some meV meG` dispatch-head step `R+0x214 → R+0x4b0 → R+0x7a4 .. R+0x7c8`. -/
theorem r3b_recv_head_some_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall} {peerV meV : AddrV} {meG : AddrGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hd : AtDispatchPlaced CodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .recv peerV)
    (hk : ∀ (s1 : State) (peerG : AddrGhost) (cw4 hiMe : BitVec 64),
      InRunPlaced CodeOk s0 s1 0x7c8 →
      s1.readReg64 (.gpr 19#5) = g.stores →
      s1.readReg64 (.gpr 20#5) = g.res →
      s1.readReg64 (.gpr 21#5) = meG.name.cap →
      s1.readReg64 (.gpr 23#5) = g.inp →
      s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length →
      s1.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64 →
      s1.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64 →
      s1.readReg64 (.gpr 28#5) = meG.name.ptr →
      s1.trace = s.trace →
      s1.fs = s.fs →
      peerG.val = addrValOf peerV →
      meG.val = addrValOf meV →
      cw4.setWidth 8 = peerG.device →
      hiMe.setWidth 8 = meG.device →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG ∗
          runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (runFsp s0 + 0x240#64) 0x20 ∗
          (((runFsp s0 + 0x260#64) ↦₆₄ meG.name.cap) ∗
            ((runFsp s0 + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((runFsp s0 + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((runFsp s0 + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (runFsp s0 + 0x280#64) (runLocalBytes - 0x280) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A g (.some meV meG) s0 resStack) Q Qp (runOom s0) := by
  let fsp := runFsp s0
  rcases hd.meRegs with ⟨hx21, hx28, hme_bytes, _, hme_dev⟩
  have hme_val : meG.val = addrValOf meV := by
    cases meG with
    | mk nm dv =>
      dsimp only [AddrGhost.val, addrValOf] at hme_bytes hme_dev ⊢
      rw [hme_bytes, hme_dev]
  dsimp only [dispatchMemPlaced, dispatchMeHeap, dispatchCells]
  rw [hcall]
  dsimp only [callAt, callHeap, addrWords]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r3b_sepWPp_exists_left; intro cw
  let peerG : AddrGhost := ⟨⟨cw.w1, cw.w2, peerV.name⟩, peerV.device⟩
  have hloc_split :
      runLocals fsp [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] =
        memRegion fsp 0x1d0 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
          memRegion (fsp + 0x1e0#64) 0x40 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) := by
    have hwf : RunLocalsFromWf 0x1e0
        [(0x220, 32, memRegion (fsp + 0x220#64) 32),
         (0x260, 32, memRegion (fsp + 0x260#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have htail := r3b_memRegion_to_runLocalsFrom fsp 0x1e0
      [(0x220, 32, memRegion (fsp + 0x220#64) 32),
       (0x260, 32, memRegion (fsp + 0x260#64) 32)]
      hwf (by intro c hc; simp at hc; rcases hc with rfl | rfl <;> rfl)
    dsimp only [runLocals, runLocalsFrom] at htail ⊢
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    rw [hz, ← htail]
  rw [hloc_split]
  have hprep :
      (memRegion g.res runResSize ∗
        ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
          ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
          ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
          ⌜cw.w0 = 0x8000000000000003#64⌝ ∗
          (ownedBytes A cw.w1 cw.w2 cw.w3 peerV.name ∗ ⌜cw.w4.setWidth 8 = peerV.device⌝)) ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.recv peerV)) ∗
        coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
        addrNameHeap A meG ∗ runSaved s0 ∗
        (memRegion fsp 0x1d0 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
          memRegion (fsp + 0x1e0#64) 0x40 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280)) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool) ⊢
      ∃∗ hiMe, ∃∗ u0, ∃∗ u1, ∃∗ u2, ∃∗ u3, ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        ⌜meG.name.cap ≠ 0xffffffffffffffff#64 ∧ cw.w3 = BitVec.ofNat 64 peerV.name.length ∧
          cw.w4.setWidth 8 = peerV.device ∧ hiMe.setWidth 8 = meG.device⌝ ∗
        memRegion g.res runResSize ∗
        (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
        ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
        ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
        addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion fsp 0x1d0 ∗
        ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((fsp + 0x1d8#64) ↦₆₄ hiMe) ∗
        memRegion (fsp + 0x1e0#64) 0x40 ∗
        ((fsp + 0x220#64) ↦₆₄ u0) ∗ ((fsp + 0x228#64) ↦₆₄ u1) ∗
        ((fsp + 0x230#64) ↦₆₄ u2) ∗ ((fsp + 0x238#64) ↦₆₄ u3) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        ((fsp + 0x260#64) ↦₆₄ v0) ∗ ((fsp + 0x268#64) ↦₆₄ v1) ∗
        ((fsp + 0x270#64) ↦₆₄ v2) ∗ ((fsp + 0x278#64) ↦₆₄ v3) ∗
        memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool := by
    rw [← hcall]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono
          (Entails.refl (⌜cw.w0 = 0x8000000000000003#64⌝ ∗
            ⌜cw.w4.setWidth 8 = peerV.device⌝))
          (sepConj_mono (r3b_nameHeap_cap_ne_neg1 A meG)
            (sepConj_mono (r3b_ownedBytes_entails_nameHeap A cw.w1 cw.w2 cw.w3 peerV.name)
              (sepConj_mono (r3b_addrUpperAt_words (fsp + 0x1d0#64) meG)
                (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x220#64))
                  (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x260#64))
                    (Entails.refl (memRegion g.res runResSize ∗
                      (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗
                      ((g.call + 16#64) ↦₆₄ cw.w2) ∗ ((g.call + 24#64) ↦₆₄ cw.w3) ∗
                      ((g.call + 32#64) ↦₆₄ cw.w4) ∗ ((g.call + 40#64) ↦₆₄ cw.w5) ∗
                      ((g.call + 48#64) ↦₆₄ cw.w6) ∗
                      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                      coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
                      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
                      runSaved s0 ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 0x40 ∗
                      memRegion (fsp + 0x240#64) 0x20 ∗
                      memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
                      stackAt fsp (resStack - runFrame) ∗ A.pool))))))))
        (by ac_rfl))
      ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0
    apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v2
    apply Entails.sepExists_elim; intro v3
    apply Entails.sepExists_elim; intro u0
    apply Entails.sepExists_elim; intro u1
    apply Entails.sepExists_elim; intro u2
    apply Entails.sepExists_elim; intro u3
    apply Entails.sepExists_elim; intro hiMe
    simp only [sepConj_assoc]
    apply Entails.pure_left; intro _
    apply Entails.pure_left; intro hdev_cw4
    apply Entails.pure_left; intro hne1
    apply r3b_pure1; intro hlen_cw3
    apply r3b_pure2; intro hhi
    rw [r3b_addrNameHeap_dev_congr A ⟨cw.w1, cw.w2, peerV.name⟩ 0#8 peerV.device]
    have hd8 : fsp + 0x1d0#64 + 8#64 = fsp + 0x1d8#64 := by bv_omega
    have hu8 : fsp + 0x220#64 + 8#64 = fsp + 0x228#64 := by bv_omega
    have hu16 : fsp + 0x220#64 + 16#64 = fsp + 0x230#64 := by bv_omega
    have hu24 : fsp + 0x220#64 + 24#64 = fsp + 0x238#64 := by bv_omega
    have hv8 : fsp + 0x260#64 + 8#64 = fsp + 0x268#64 := by bv_omega
    have hv16 : fsp + 0x260#64 + 16#64 = fsp + 0x270#64 := by bv_omega
    have hv24 : fsp + 0x260#64 + 24#64 = fsp + 0x278#64 := by bv_omega
    rw [hd8, hu8, hu16, hu24, hv8, hv16, hv24]
    exact Entails.sepExists_right hiMe (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
        (Entails.sepExists_right u3 (Entails.sepExists_right v0
          (Entails.sepExists_right v1 (Entails.sepExists_right v2
            (Entails.sepExists_right v3
              (Entails.pure_right ⟨hne1, hlen_cw3, hdev_cw4, hhi⟩
                (Entails.of_eq (by ac_rfl)))))))))))
  apply r3b_sepWPp_weaken_pre hprep
  apply r3b_sepWPp_exists_left; intro hiMe
  apply r3b_sepWPp_exists_left; intro u0
  apply r3b_sepWPp_exists_left; intro u1
  apply r3b_sepWPp_exists_left; intro u2
  apply r3b_sepWPp_exists_left; intro u3
  apply r3b_sepWPp_exists_left; intro v0
  apply r3b_sepWPp_exists_left; intro v1
  apply r3b_sepWPp_exists_left; intro v2
  apply r3b_sepWPp_exists_left; intro v3
  apply r3b_sepWPp_pure_left; rintro ⟨hne1, hlen_cw3, hdev_cw4, hhi⟩
  have hcmn : meG.name.cap + 1#64 ≠ 0#64 := fun h0 => hne1 (by bv_omega)
  have hbeq_cmn : ((meG.name.cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
  have hpc : s.pc = runPcPlaced 0x214 := hd.base.pc
  change s.pc = (blkPl_579).base + 0x214#64 at hpc
  have hrun : s.status = .Running := hd.base.run
  have hsp : s.sp = fsp := hd.base.sp
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa [hcall, CallV.tag] using hd.x8
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  apply r3b_seq (mid := runPcPlaced 0x7c8) hd.base.inv
  rw [runPcPlaced_eq, ← hsp]
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, hrun])
  intro hinv1
  have hs1 : InRunPlaced CodeOk s0 _ 0x7c8 :=
    r3b_inRun_step hd.base (by simp only [runPcPlaced_eq, arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1 (by simp only [calleeSavedVRegs, arm64_norm])
  refine r3b_sepWPp_weaken_pre ?_
    (hk _ peerG cw.w4 hiMe hs1
      (by simp only [arm64_norm, hd.x19])
      (by simp only [arm64_norm, hd.x20])
      (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hd.x23])
      (by simp only [arm64_norm, hd.x24])
      (by simp only [arm64_norm, hd.x26])
      (by simp only [arm64_norm, hd.x27])
      (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      rfl hme_val hdev_cw4 hhi)
  rw [hsp]
  have h1d0_collapse :
      memRegion fsp 0x1d0 ∗
        ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((fsp + 0x1d8#64) ↦₆₄ hiMe) ∗
        memRegion (fsp + 0x1e0#64) 0x40 ⊢
      memRegion fsp 0x220 := by
    have h16 :
        ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x1d8#64) ↦₆₄ hiMe) ⊢ memRegion (fsp + 0x1d0#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 8) (k := 8)
        (b' := fsp + 0x1d8#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x50)
          (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 16) (k := 0x40)
          (b' := fsp + 0x1e0#64) rfl (by bv_omega) (by decide)]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (sepConj_mono_left h16))
  exact r3b_perm
    (r3b_perm_post
      (sepConj_mono (r3b_call7_to_memRegion56 g.call cw)
        (sepConj_mono h1d0_collapse
          (Entails.refl (memRegion g.res runResSize ∗
            storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
            SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
            addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x238#64) ↦₆₄ cw.w4)) ∗
            memRegion (fsp + 0x240#64) 0x20 ∗
            (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
              ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
              ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
            memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool))))
      (by dsimp only [fsp]; ac_rfl))
    (by dsimp only [fsp, peerG]; rw [hlen_cw3, hme_bytes]; ac_rfl)

/-! ## 3. Bad-Wire Hop (`run_hop_recvBad_placed_ok`) -/

theorem run_hop_recvBad_placed_ok [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopRecvBadPlaced CodeOk
      A H B S needs resStack := by
  unfold RunHopRecvBadPlaced
  intro g s0 s me peerV Q Qp hh hres hres64 he hd hcall hbad hrej
  cases me with
  | none => exact r3b_me_none_placed hh hres hres64 he hd hcall hrej
  | some meV meG =>
    have hbnds := runNeed_bounds_placed hres hres64
    have hext_le : extHookStack ≤ resStack - runFrame := by
      have := hbnds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnds.2.2.1
    have hans : g.a = some none := hd.recvBad_reject he hcall hbad
    refine r3b_recv_head_some_placed hd hcall ?_
    intro s1 peerG cw4 hiMe hs1 hx19 hx20 hx21 hx23 hx24 _ _ hx28 htr1 hfs1 _ _ _ _
    let fsp := runFsp s0
    have htail_collapse :
        memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
            ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ⊢
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
      dsimp only [runLocalBytes]
      rw [ProofLib.memRegion_split' (b := fsp + 0x240#64) (n := 0x20) (k := 0x29f0 - 0x260)
            (b' := fsp + 0x260#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x260#64) (n := 32) (k := 0x29f0 - 0x280)
            (b' := fsp + 0x280#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono_right (sepConj_mono_left (r3b_words4_entails_mem32 _ _ _ _ _)))
    apply r3b_sepWPp_weaken_pre
      (r3b_perm
        (r3b_perm_post
          (sepConj_mono htail_collapse
            (sepConj_mono
              (entails_anyHeap (coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
                SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff))
              (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
                memRegion fsp 0x220 ∗
                (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                  ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                  ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                  ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool))))
          (by dsimp only [fsp]))
        (by dsimp only [fsp]; ac_rfl))
    rcases hbad with hnil | ⟨t, rest, hcons, ht2, ht3⟩
    · have hinp0 : inputOf g.i g.c = [] := by simp [hcall, inputOf, CallV.tag, hnil]
      rw [hinp0] at hx24
      dsimp only [List.length] at hx24
      have hpc1 : s1.pc = runPcPlaced 0x7c8 := hs1.pc
      change s1.pc = (blkPl_579).base + 0x7c8#64 at hpc1
      have hrun1 : s1.status = .Running := hs1.run
      apply r3b_seq (mid := runPcPlaced 0xfec) hs1.inv
      rw [runPcPlaced_eq]
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun1])
      intro hinv2
      have hs2 : InRunPlaced CodeOk s0 (r3b_stOf hinv2) 0xfec :=
        r3b_inRun_step hs1 (by simp only [runPcPlaced_eq, arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv2 (by simp only [calleeSavedVRegs, arm64_norm])
      have htr2 : s0.trace <+: (r3b_stOf hinv2).trace :=
        by simpa only [arm64_norm, htr1] using hd.trace
      have hhist2 : RunHistOk g.i s0 (r3b_stOf hinv2) :=
        ⟨by simpa only [arm64_norm, hfs1] using hd.fs,
          by simpa only [arm64_norm, htr1] using hd.stdout⟩
      refine r3b_sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
        (r3b_reject_from_fec_placed StoresGhost.opened meG peerG (BitVec.ofNat 64 peerG.name.bytes.length) cw4
          hh hext_le hsub64 hs2
          (by simp only [arm64_norm, hx19])
          (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx21])
          (by simp only [arm64_norm, hx28])
          htr2 hhist2 hans hrej)
    · have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
        hcall ▸ he.parse
      have htail_lt : rest.length < 2 ^ 32 := by
        have ht0 := he.rel.2.1.2.2.1 peerV hparse
        simpa [hcons] using ht0
      have hinp_c : inputOf g.i g.c = t :: rest := by simp [hcall, inputOf, CallV.tag, hcons]
      have hlen_ne : BitVec.ofNat 64 (t :: rest).length ≠ 0#64 := by
        rw [List.length_cons]
        intro h0
        have hv := congrArg BitVec.toNat h0
        have hzero : (0#64).toNat = 0 := rfl
        rw [BitVec.toNat_ofNat, hzero] at hv
        have hmod : (rest.length + 1) % 2 ^ 64 = rest.length + 1 := Nat.mod_eq_of_lt (by omega)
        omega
      have hbeq_len : (BitVec.ofNat 64 (t :: rest).length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hlen_ne
      have hne3 : (t.zeroExtend 32 == 3#32) = false :=
        beq_eq_false_iff_ne.mpr fun h0 => ht3 (by bv_omega)
      have hne2 : (t.zeroExtend 32 == 2#32) = false :=
        beq_eq_false_iff_ne.mpr fun h0 => ht2 (by bv_omega)
      have hne2b : (t.zeroExtend 32 != 2#32) = true :=
        bne_iff_ne.mpr fun h0 => ht2 (by bv_omega)
      rw [hinp_c] at hx24
      rw [hinp_c, pointsToBytes_cons]
      have hpc1 : s1.pc = runPcPlaced 0x7c8 := hs1.pc
      change s1.pc = (blkPl_579).base + 0x7c8#64 at hpc1
      have hrun1 : s1.status = .Running := hs1.run
      apply r3b_seq (mid := runPcPlaced 0xfec) hs1.inv
      rw [runPcPlaced_eq]
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun1])
      intro hinv2
      have hs2 : InRunPlaced CodeOk s0 (r3b_stOf hinv2) 0xfec :=
        r3b_inRun_step hs1 (by simp only [runPcPlaced_eq, arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv2 (by simp only [calleeSavedVRegs, arm64_norm])
      have htr2 : s0.trace <+: (r3b_stOf hinv2).trace := by simpa only [arm64_norm, htr1] using hd.trace
      have hhist2 : RunHistOk g.i s0 (r3b_stOf hinv2) :=
        ⟨by simpa only [arm64_norm, hfs1] using hd.fs,
          by simpa only [arm64_norm, htr1] using hd.stdout⟩
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_reject_from_fec_placed StoresGhost.opened meG peerG (BitVec.ofNat 64 peerG.name.bytes.length) cw4
          hh hext_le hsub64 hs2
          (by simp only [arm64_norm, hx19])
          (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx21])
          (by simp only [arm64_norm, hx28])
          htr2 hhist2 hans hrej)
      rw [hinp_c, pointsToBytes_cons]
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose
