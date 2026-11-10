/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `signal_session::run` Placed Arm `R3b`: PreKey Arm Proof

Proves the `decrypt_prekey` `Ok` tail (`r3b_recvP_from_dcc_placed`, `r3b_recvP_dec_ok_placed`) and
`run_hop_recvP_placed_ok` (`RunHopRecvPPlaced`) on Block `579` (`runProgPlaced H`) under
`[LibsignalPlacement]`.
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
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. `decrypt_prekey` `Ok` Tail (`r3b_recvP_from_dcc_placed`, `r3b_recvP_dec_ok_placed`) -/

set_option maxHeartbeats 800000 in
/-- Continuation from `R+0xdcc` (`R+0xdcc → R+0xde0 → R+0xf8c`, freeing `meG.name` if `cap ≠ 0`). -/
theorem r3b_recvP_from_dcc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG meG : AddrGhost)
    {s0 s_dcc : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs_c1 : InRunPlaced CodeOk s0 s_dcc 0xdcc)
    (hx19_c1 : s_dcc.readReg64 (.gpr 19#5) = g.stores)
    (hx20_c1 : s_dcc.readReg64 (.gpr 20#5) = g.res)
    (hx21_c1 : s_dcc.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28_c1 : s_dcc.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s_dcc.trace)
    (hhist : RunHistOk g.i s0 s_dcc)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s_dcc
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A meG ∗ addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x208 ∗
        vecU8 A (runFsp s0 + 0x208#64) pt ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (runFsp s0 + 0x230#64) 16) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  let fsp := runFsp s0
  by_cases hcapM : meG.name.cap = 0#64
  · have hpc1 : s_dcc.pc = runPcPlaced 0xdcc := hs_c1.pc
    change s_dcc.pc = (blkPl_579).base + 0xdcc#64 at hpc1
    have hrun1 : s_dcc.status = .Running := hs_c1.run
    apply r3b_seq (mid := runPcPlaced 0xde0) hs_c1.inv
    rw [runPcPlaced_eq]
    rw [hcapM] at hx21_c1
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    intro hinv_d
    have hs_d : InRunPlaced CodeOk s0 (r3b_stOf hinv_d) 0xde0 :=
      r3b_inRun_step hs_c1 (by simp only [runPcPlaced_eq, arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv_d (by simp only [calleeSavedVRegs, arm64_norm])
    have htr_d : (r3b_stOf hinv_d).trace = s_dcc.trace := by simp only [arm64_norm]
    have hfs_d : (r3b_stOf hinv_d).fs = s_dcc.fs := by simp only [arm64_norm]
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_recvP_from_de0_placed g' pt peerG hh hext_le hsub64 hs_d
        (by simp only [arm64_norm, hx19_c1])
        (by simp only [arm64_norm, hx20_c1])
        (htr_d ▸ htr)
        (r3b_hist_of_eq htr_d (congrArg FsState.files hfs_d) hhist)
        hans hwr hjoin)
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_nameHeap_zero A meG hcapM)
          (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x230#64) 16) ∗
            memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
        (by rw [emp_sepConj]))
      (by dsimp only [fsp]; ac_rfl)
  · have hbeqM : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcapM
    have hbeq21 : (s_dcc.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21_c1]; exact hbeqM
    have hpc1 : s_dcc.pc = runPcPlaced 0xdcc := hs_c1.pc
    change s_dcc.pc = (blkPl_579).base + 0xdcc#64 at hpc1
    have hrun1 : s_dcc.status = .Running := hs_c1.run
    have hsp1 : s_dcc.sp = fsp := hs_c1.sp
    have hsp_al1 : s_dcc.spAligned = true := hs_c1.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A meG hcapM))))))
    rw [show (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) by ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlayM
    apply r3b_seq (mid := lsρ lsRustDeallocSym) hs_c1.inv
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1])
    intro hinv_c2
    have hstk_split := r3b_stackAt_split_ge s_dcc.sp hext_le hsub64
    refine r3b_call_lscro
      (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - extHookStack) ∗
        anyHeap)
      (s0 := s0) (meG.name.ptr, meG.name.cap.toNat, 1)
      (r3b_dealloc_ok hh) hinv_c2
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al1)
      (retAddr := runPcPlaced 0xde0)
      (by simp only [runPcPlaced_eq, arm64_norm])
      ?_
      (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm]; try rw [hx28_c1],
          by simp only [arm64_norm]; try rw [hx21_c1], by simp only [arm64_norm], hlayM⟩
      rw [hsp1] at hstk_split
      rw [hstk_split]
      simp only [arm64_norm, hsp1]
      exact Entails.of_eq (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; intro hfs_m
      apply r3b_sepWPp_pure_left; intro htr_m
      have hs_m : InRunPlaced CodeOk s0 sm 0xde0 :=
        r3b_inRun_step hs_c1 hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have htr_m_eq : sm.trace = s_dcc.trace := htr_m.trans (by simp only [arm64_norm])
      have hfs_m_eq : sm.fs = s_dcc.fs := hfs_m.trans (by simp only [arm64_norm])
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_recvP_from_de0_placed g' pt peerG hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [arm64_norm, hx19_c1]))
          (hcsm.2.1.trans (by simp only [arm64_norm, hx20_c1]))
          (htr_m_eq ▸ htr)
          (r3b_hist_of_eq htr_m_eq (congrArg FsState.files hfs_m_eq) hhist)
          hans hwr hjoin)
      rw [hsp1] at hstk_split
      rw [hstk_split]
      simp only [arm64_norm, hsp1]
      exact Entails.of_eq (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
set_option maxHeartbeats 800000 in
/-- `decrypt_prekey` `Ok(pt)` tail from `R+0xd94` (`R+0xd94 → R+0xdcc → R+0xde0 → R+0xf8c` `AtJoinPlaced`). -/
theorem r3b_recvP_dec_ok_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0xd94)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A (runFsp s0 + 0x320#64) (.ok pt) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  let fsp := runFsp s0
  have h220_split : memRegion fsp 0x220 =
      memRegion fsp 0x208 ∗
        memRegion (fsp + 0x208#64) 8 ∗ memRegion (fsp + 0x210#64) 8 ∗ memRegion (fsp + 0x218#64) 8 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x208) (k := 24) (b' := fsp + 0x208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x208#64) (n := 8) (k := 16) (b' := fsp + 0x210#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x210#64) (n := 8) (k := 8) (b' := fsp + 0x218#64) rfl (by bv_omega) (by decide)]
  have h350_split : memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) =
      memRegion (fsp + 0x350#64) 0x30 ∗
        memRegion (fsp + 0x380#64) 8 ∗ memRegion (fsp + 0x388#64) 8 ∗
        memRegion (fsp + 0x390#64) (runLocalBytes - 0x390) := by
    rw [r3b_split_at fsp 0x350 0x30 runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x380 8 runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x388 8 runLocalBytes (by decide) (by decide)]
  have hprep :
      decResAt A (fsp + 0x320#64) (.ok pt) ∗
        (memRegion (fsp + 0x208#64) 8 ∗ memRegion (fsp + 0x210#64) 8 ∗ memRegion (fsp + 0x218#64) 8) ∗
        (memRegion (fsp + 0x380#64) 8 ∗ memRegion (fsp + 0x388#64) 8) ∗
        protocolAddressAt A peerG (fsp + 0x220#64) ∗
        protocolAddressAt A meG (fsp + 0x260#64) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ∃∗ o0 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o2 : BitVec 64,
        ∃∗ s0w : BitVec 64, ∃∗ s1w : BitVec 64,
          ⌜cap.toNat < 2 ^ 63⌝ ∗
          ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗
          ((fsp + 0x328#64) ↦₆₄ cap) ∗
          ((fsp + 0x330#64) ↦₆₄ ptr) ∗
          ((fsp + 0x338#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
          memRegion (fsp + 0x340#64) 16 ∗
          r3b_vecHeap A cap ptr pt ∗
          ((fsp + 0x208#64) ↦₆₄ o0) ∗ ((fsp + 0x210#64) ↦₆₄ o1) ∗ ((fsp + 0x218#64) ↦₆₄ o2) ∗
          ((fsp + 0x380#64) ↦₆₄ s0w) ∗ ((fsp + 0x388#64) ↦₆₄ s1w) ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x260#64) 32 ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG := by
    dsimp only [decResAt, vecResultAt, vecU8]
    rw [ProofLib.memRegion_eight (fsp + 0x208#64), ProofLib.memRegion_eight (fsp + 0x210#64),
        ProofLib.memRegion_eight (fsp + 0x218#64), ProofLib.memRegion_eight (fsp + 0x380#64),
        ProofLib.memRegion_eight (fsp + 0x388#64),
        protocolAddressAt_eq_parts A peerG (fsp + 0x220#64),
        protocolAddressAt_eq_parts A meG (fsp + 0x260#64)]
    have hp_up : addrUpperAt (fsp + 0x220#64 + 16#64) peerG ⊢ memRegion (fsp + 0x230#64) 16 := by
      rw [show fsp + 0x220#64 + 16#64 = fsp + 0x230#64 by bv_omega]
      exact addrUpperAt_entails_memRegion _ _
    have hm_32 :
        ((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x260#64 + 8#64) ↦₆₄ meG.name.ptr) ∗
          addrUpperAt (fsp + 0x260#64 + 16#64) meG ⊢ memRegion (fsp + 0x260#64) 32 := by
      have hm_up : addrUpperAt (fsp + 0x260#64 + 16#64) meG ⊢ memRegion (fsp + 0x270#64) 16 := by
        rw [show fsp + 0x260#64 + 16#64 = fsp + 0x270#64 by bv_omega]
        exact addrUpperAt_entails_memRegion _ _
      rw [show fsp + 0x260#64 + 8#64 = fsp + 0x268#64 by bv_omega,
          ProofLib.memRegion_split' (b := fsp + 0x260#64) (n := 8) (k := 24)
            (b' := fsp + 0x268#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x268#64) (n := 8) (k := 16)
            (b' := fsp + 0x270#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) hm_up)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro s1w
    apply Entails.sepExists_elim; intro s0w
    apply Entails.sepExists_elim; intro o2
    apply Entails.sepExists_elim; intro o1
    apply Entails.sepExists_elim; intro o0
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    rw [r3b_vecU8At_eq A (fsp + 0x320#64 + 8#64) cap ptr pt]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono (r3b_vecHeap_cap_lt A cap ptr pt)
          (sepConj_mono hp_up (sepConj_mono hm_32
            (Entails.refl (((fsp + 0x320#64) ↦₆₄ okTagVec) ∗
              ((fsp + 0x320#64 + 8#64) ↦₆₄ cap) ∗
              ((fsp + 0x320#64 + 8#64 + 8#64) ↦₆₄ ptr) ∗
              ((fsp + 0x320#64 + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
              memRegion (fsp + 0x320#64 + 32#64) 16 ∗
              ((fsp + 0x208#64) ↦₆₄ o0) ∗ ((fsp + 0x210#64) ↦₆₄ o1) ∗
              ((fsp + 0x218#64) ↦₆₄ o2) ∗
              ((fsp + 0x380#64) ↦₆₄ s0w) ∗ ((fsp + 0x388#64) ↦₆₄ s1w) ∗
              ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x220#64 + 8#64) ↦₆₄ peerG.name.ptr) ∗
              addrNameHeap A meG ∗ addrNameHeap A peerG)))))
        (by ac_rfl)) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hcap_lt
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr
      (Entails.sepExists_right o0 (Entails.sepExists_right o1
        (Entails.sepExists_right o2 (Entails.sepExists_right s0w
          (Entails.sepExists_right s1w (Entails.pure_right hcap_lt ?_)))))))
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  rw [show runFsp s0 = fsp from rfl, h220_split, h350_split]
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗
          memRegion fsp 0x208 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x350#64) 0x30 ∗
          memRegion (fsp + 0x390#64) (runLocalBytes - 0x390) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
        hprep)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro cap
  apply r3b_sepWPp_exists_left; intro ptr
  apply r3b_sepWPp_exists_left; intro o0
  apply r3b_sepWPp_exists_left; intro o1
  apply r3b_sepWPp_exists_left; intro o2
  apply r3b_sepWPp_exists_left; intro s0w
  apply r3b_sepWPp_exists_left; intro s1w
  rw [sepConj_assoc]
  apply r3b_sepWPp_pure_left; intro hcap_lt
  have hok3 : ((okTagVec + 3#64) == 0#64) = false := rfl
  have hok2 : ((okTagVec + 2#64) != 0#64) = false := rfl
  have hcap_cmn : ((cap + 1#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; bv_omega)
  have hpc : s.pc = runPcPlaced 0xd94 := hs.pc
  change s.pc = (blkPl_579).base + 0xd94#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hpack_c1 :
      (((fsp + 520#64) ↦₆₄ cap) ∗ ((fsp + 528#64) ↦₆₄ ptr) ∗
        ((fsp + 536#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗ r3b_vecHeap A cap ptr pt) ∗
      (((fsp + 800#64) ↦₆₄ okTagVec) ∗ ((fsp + 808#64) ↦₆₄ cap) ∗
        ((fsp + 816#64) ↦₆₄ ptr) ∗ ((fsp + 824#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (fsp + 832#64) 16 ∗
        memRegion (fsp + 576#64) 0x20 ∗ memRegion (fsp + 608#64) 32 ∗
        memRegion (fsp + 640#64) 0xa0 ∗ memRegion (fsp + 848#64) 0x30 ∗
        ((fsp + 896#64) ↦₆₄ ptr) ∗ ((fsp + 904#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (fsp + 912#64) (runLocalBytes - 0x390)) ⊢
      vecU8 A (fsp + 0x208#64) pt ∗ memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
    have hv :
        ((fsp + 520#64) ↦₆₄ cap) ∗ ((fsp + 528#64) ↦₆₄ ptr) ∗
          ((fsp + 536#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗ r3b_vecHeap A cap ptr pt ⊢
        vecU8 A (fsp + 0x208#64) pt := by
      dsimp only [vecU8]
      refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
      rw [r3b_vecU8At_eq A (fsp + 0x208#64) cap ptr pt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.refl _
    have hm320 :
        ((fsp + 800#64) ↦₆₄ okTagVec) ∗ ((fsp + 808#64) ↦₆₄ cap) ∗
          ((fsp + 816#64) ↦₆₄ ptr) ∗ ((fsp + 824#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
          memRegion (fsp + 832#64) 16 ⊢
        memRegion (fsp + 0x320#64) 48 := by
      have h32 := r3b_words4_entails_mem32 (fsp + 800#64) okTagVec cap ptr (BitVec.ofNat 64 pt.length)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
      rw [ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32) (k := 16)
            (b' := fsp + 832#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h32)
    have hm380 :
        ((fsp + 896#64) ↦₆₄ ptr) ∗ ((fsp + 904#64) ↦₆₄ BitVec.ofNat 64 pt.length) ⊢
        memRegion (fsp + 0x380#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x380#64) (n := 8) (k := 8)
            (b' := fsp + 904#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    have hback :
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) =
          memRegion (fsp + 576#64) 0x20 ∗
            (memRegion (fsp + 608#64) 32 ∗
              (memRegion (fsp + 640#64) 0xa0 ∗
                (memRegion (fsp + 0x320#64) 48 ∗
                  (memRegion (fsp + 848#64) 0x30 ∗
                    (memRegion (fsp + 0x380#64) 16 ∗
                      memRegion (fsp + 912#64) (runLocalBytes - 0x390)))))) := by
      rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x280 0xa0 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x320 48 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x350 0x30 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x380 16 runLocalBytes (by decide) (by decide)]
    rw [hback]
    exact sepConj_mono hv
      (r3b_perm
        (r3b_perm_post
          (sepConj_mono hm320 (sepConj_mono hm380
            (Entails.refl (memRegion (fsp + 576#64) 0x20 ∗ memRegion (fsp + 608#64) 32 ∗
              memRegion (fsp + 640#64) 0xa0 ∗ memRegion (fsp + 848#64) 0x30 ∗
              memRegion (fsp + 912#64) (runLocalBytes - 0x390)))))
          (by ac_rfl))
        (by ac_rfl))
  apply r3b_seq (mid := runPcPlaced 0xdcc) hs.inv
  rw [runPcPlaced_eq, ← hsp]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_c1
  have hs_c1 : InRunPlaced CodeOk s0 (r3b_stOf hinv_c1) 0xdcc :=
    r3b_inRun_step hs (by simp only [runPcPlaced_eq, arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv_c1 (by simp only [calleeSavedVRegs, arm64_norm])
  have hx19_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 19#5) = g.stores := by simp only [arm64_norm, hx19]
  have hx20_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 20#5) = g.res := by simp only [arm64_norm, hx20]
  have hx21_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 21#5) = meG.name.cap := by simp only [arm64_norm, hx21]
  have hx28_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 28#5) = meG.name.ptr := by simp only [arm64_norm, hx28]
  have htr_c1 : (r3b_stOf hinv_c1).trace = s.trace := by simp only [arm64_norm]
  have hfs_c1 : (r3b_stOf hinv_c1).fs = s.fs := by simp only [arm64_norm]
  refine r3b_sepWPp_weaken_pre ?_
    (r3b_recvP_from_dcc_placed g' pt peerG meG hh hext_le hsub64 hs_c1
      hx19_c1 hx20_c1 hx21_c1 hx28_c1
      (htr_c1 ▸ htr)
      (r3b_hist_of_eq htr_c1 (congrArg FsState.files hfs_c1) hhist)
      hans hwr hjoin)
  rw [hsp]
  exact r3b_perm
    (r3b_perm_post
      (sepConj_mono hpack_c1
        (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG ∗
          runSaved s0 ∗
          memRegion fsp 0x208 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
      (by dsimp only [fsp]; ac_rfl))
    (by dsimp only [fsp]; ac_rfl)
/-! ## 2. Main Hop Theorem: `run_hop_recvP_placed_ok` -/

set_option maxHeartbeats 1200000 in
theorem run_hop_recvP_of_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem}
    {needs : RunNeeds} {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A S needs))
    (hslot_eq : slots.decryptPrekey = mkSlot (decPkSlotSpecPlacedOf CodeOk A S) needs.decryptPrekey) :
    RunHopRecvPPlacedOf CodeOk A H B S slots resStack := by
  unfold RunHopRecvPPlacedOf
  intro g s0 s me peerV rest Q Qp hh hc hpksm hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej hjoin
  cases me with
  | none => exact r3b_me_none_placed hh (hneed_eq ▸ hres) hres64 he hd hcall hrej
  | some meV meG =>
    have hbnds := runNeed_bounds_placed (hneed_eq ▸ hres) hres64
    rcases hbnds with ⟨hrf_le, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _,
      hpk_stk, hstk32, _, hext_le, _, _, _, hdp_stk, _⟩
    obtain ⟨hrest32, hcoins63, _, hfilesOk, hdecPkOk, hga⟩ :=
      hd.recvP_facts he hcall hstdin
    refine r3b_recv_head_some_placed hd hcall ?_
    intro s1 peerG cw4 hiMe hs1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1
      htr1 hfs1 hpeer_val hme_val hdev_cw4 hhi
    let fsp := runFsp s0
    have hfsp_sub : resStack - runFrame ≤ fsp.toNat := by
      dsimp only [fsp, runFsp, runFrame] at hrf_le ⊢
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 0x2a50 ≤ s0.sp.toNat; omega))]
      change resStack - 0x2a50 ≤ s0.sp.toNat - 0x2a50
      omega
    have hinp_c : inputOf g.i g.c = 3#8 :: rest := by simp [hcall, inputOf, CallV.tag, hstdin]
    have hlen_ne : BitVec.ofNat 64 (3#8 :: rest).length ≠ 0#64 := by
      rw [List.length_cons]
      intro h0
      have hv := congrArg BitVec.toNat h0
      have hzero : (0#64).toNat = 0 := rfl
      rw [BitVec.toNat_ofNat, hzero] at hv
      have hmod : (rest.length + 1) % 2 ^ 64 = rest.length + 1 := Nat.mod_eq_of_lt (by omega)
      omega
    have hbeq_len : (BitVec.ofNat 64 (3#8 :: rest).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hlen_ne
    have hsub1_nat : (BitVec.ofNat 64 (3#8 :: rest).length - 1#64).toNat = rest.length := by
      rw [List.length_cons]
      have h1 : BitVec.ofNat 64 (rest.length + 1) - 1#64 = BitVec.ofNat 64 rest.length := by
        rw [BitVec.ofNat_add]; bv_omega
      rw [h1, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have h280_pkm : memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) =
        memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
          memRegion (fsp + 0x4d0#64) 248 ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) := by
      rw [r3b_split_at fsp 0x280 (0x4d0 - 0x280) runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide)]
    rw [hinp_c] at hx24_1
    rw [hinp_c, pointsToBytes_cons, h280_pkm]
    have hpc1 : s1.pc = runPcPlaced 0x7c8 := hs1.pc
    change s1.pc = (blkPl_579).base + 0x7c8#64 at hpc1
    have hrun1 : s1.status = .Running := hs1.run
    have hsp1 : s1.sp = fsp := hs1.sp
    have hsp1_al : s1.spAligned = true := hs1.spAligned_cur
    apply r3b_seq
      (mid := (CryptoVerification.blkPl_111).base) hs1.inv
    rw [← hsp1]
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm, hrun1])
    intro hinv_pk
    have hstk_pk := r3b_stackAt_split_ge s1.sp hpk_stk hsub64
    have htr_pre_pk : s0.trace <+: s1.trace := htr1 ▸ hd.trace
    refine r3b_call_raw
      (F := memRegion g.res runResSize ∗
        memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗
        (g.inp ↦₈ 3#8) ∗
        coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        addrNameHeap A meG ∗
        addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
          ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
          ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
        memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
        memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack))
      (s0 := s0)
      ({ ptr := g.inp + 1#64, bytes := rest, ret := fsp + 0x4d0#64 } : PksmGhost)
      hpksm hinv_pk
      (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm, hrun1])
      (by simpa only [State.spAligned, arm64_norm] using hsp1_al)
      (retAddr := runPcPlaced 0x994)
      (by simp only [runPcPlaced_eq, arm64_norm])
      ?_
      (hpanic := fun sf R' _ hp => by
        dsimp only [pksmSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hp
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix htr_pre_pk hp.1.1)))
      (hoom := fun _ _ _ ho => by
        dsimp only [pksmSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at ho
        exact (not_satisfies_false_sepConj ho).elim)
      (hnext := fun s2 hsteps_pk hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
    · dsimp only [pksmSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm]; try rw [hx23_1],
          by simp only [arm64_norm]; exact hsub1_nat,
          hrest32,
          by simp only [arm64_norm]; try rw [hsp1],
          by
            have hpk_spb : CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ≤ fsp.toNat :=
              Nat.le_trans hpk_stk hfsp_sub
            simpa only [arm64_norm, hsp1] using hpk_spb⟩
      rw [hsp1] at hstk_pk
      rw [hstk_pk]
      simp only [arm64_norm]
      try rw [hsp1]
      exact r3b_perm_post
        (Entails.pure_right (LsCodeInv.toRoCl hinv_pk) (Entails.refl _))
        (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
    · dsimp only [pksmSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; intro htr_pk
      have hs2 : InRunPlaced CodeOk s0 s2 0x994 :=
        r3b_inRun_step hs1 hpcm2 hrun2 (hsp2.trans (by simp only [arm64_norm]))
          (hcsm2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv2
          (hcsm2.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := hcsm2.1.trans (by simp only [arm64_norm, hx19_1])
      have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := hcsm2.2.1.trans (by simp only [arm64_norm, hx20_1])
      have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := hcsm2.2.2.1.trans (by simp only [arm64_norm, hx21_1])
      have hx26_2 : s2.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
        hcsm2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm]; exact hx26_1)
      have hx27_2 : s2.readReg64 (.gpr 27#5) = fsp + 0x1750#64 :=
        hcsm2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm]; exact hx27_1)
      have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr :=
        hcsm2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm]; exact hx28_1)
      have htr2_eq : s2.trace = s.trace :=
        (htr_pk.trans (by simp only [arm64_norm])).trans htr1
      have hfs2_files : s2.fs.files = runFiles g.i :=
        ((r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_pk htr_pk).trans
          (by simp only [arm64_norm])).trans ((congrArg FsState.files hfs1).trans hd.fs)
      have htr2 : s0.trace <+: s2.trace := htr2_eq ▸ hd.trace
      have hhist2 : RunHistOk g.i s0 s2 :=
        ⟨hfs2_files, htr2_eq ▸ hd.stdout⟩
      rw [← hsp2, hs2.sp]
      rw [hsp1] at hstk_pk
      apply r3b_sepWPp_weaken_pre
        (r3b_perm
          (sepConj_mono_left
            (Q := pksmResAt A (fsp + 0x4d0#64) (S.pksmParse rest) ∗
              ((g.inp + 1#64) ↦ₛ rest) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦₈ 3#8) ∗
              coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
              SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
              addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
              memRegion fsp 0x220 ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
              memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
              memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))
            (Entails.of_eq hstk_pk.symm))
          (by dsimp only [fsp]; ac_rfl))
      rcases _hparse : S.pksmParse rest with _ | pm
      · (try rw [_hparse] at hga); dsimp only at hga
        refine r3b_sepWPp_weaken_pre ?_
          (r3b_recvP_parse_err_placed meG peerG cw4 hiMe hh hdrop hstk32 hext_le hsub64 hs2
            hx19_2 hx20_2 hx21_2 hx26_2 hx28_2 htr2 hhist2 hga hrej)
        rw [hinp_c, pointsToBytes_cons]
        have hany :
            coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
              SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ⊢ anyHeap :=
          entails_anyHeap _
        exact r3b_perm
          (r3b_perm_post
            (sepConj_mono hany
              (Entails.refl (pksmResAt A (fsp + 0x4d0#64) none ∗
                (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores StoresGhost.opened ∗
                addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
                memRegion fsp 0x220 ∗
                (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                  ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                  ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                memRegion (fsp + 0x240#64) 0x20 ∗
                (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                  ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                  ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
                memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
                memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))))
            (by dsimp only [fsp]; ac_rfl))
          (by dsimp only [fsp, pksmResAt]; ac_rfl)
      · (try rw [_hparse] at hga); dsimp only at hga
        have hdp_ok : S.decPkOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) pm :=
          hdecPkOk pm (by first | exact rfl | exact _hparse)
        have hloc_shuf :
            pksmResAt A (fsp + 0x4d0#64) (some pm) ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
              (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
              addrNameHeap A peerG ∗ addrNameHeap A meG ∗
              memRegion fsp 0x220 ∗
              memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
              memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ⊢
            ∃∗ pmG : PreKeyMsgGhost, ∃∗ w : r3b_W30,
              ∃∗ t0 : r3b_W5, ∃∗ t : r3b_W5, ∃∗ z : r3b_W30, ∃∗ m : r3b_W30,
                ⌜pmG.msg.pqCap.toNat < 2 ^ 63⌝ ∗
                ((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗
                r3b_slot30 (fsp + 0x4d8#64) w ∗
                r3b_slot5 (fsp + 0x2a0#64) t ∗
                r3b_slot30 (fsp + 0x3e0#64) z ∗
                r3b_slot30 (fsp + 0x1750#64) m ∗
                r3b_slot5 fsp t0 ∗
                ((((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w) -∗
                  preKeyMsgAt A pmG (fsp + 0x4d0#64) pm) ∗
                protocolAddressAt A peerG (fsp + 0x220#64) ∗
                protocolAddressAt A meG (fsp + 0x260#64) ∗
                memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                memRegion (fsp + 0x280#64) 0x20 ∗
                memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                memRegion (fsp + 0x320#64) 48 ∗
                memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                anyHeap := by
          dsimp only [pksmResAt]
          have hf0 : memRegion fsp 0x220 =
              memRegion fsp 40 ∗ memRegion (fsp + 0x28#64) (0x220 - 0x28) :=
            ProofLib.memRegion_split' (b := fsp) (n := 40) (k := 0x220 - 0x28)
              (b' := fsp + 0x28#64) rfl (by bv_omega) (by decide)
          have hf280 : memRegion (fsp + 0x280#64) (0x4d0 - 0x280) =
              memRegion (fsp + 0x280#64) 0x20 ∗
                memRegion (fsp + 0x2a0#64) 40 ∗
                memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                memRegion (fsp + 0x320#64) 48 ∗
                memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                memRegion (fsp + 0x3e0#64) 240 := by
            rw [r3b_split_at fsp 0x280 0x20 0x4d0 (by decide) (by decide),
                r3b_split_at fsp 0x2a0 40 0x4d0 (by decide) (by decide),
                r3b_split_at fsp 0x2c8 (0x320 - 0x2c8) 0x4d0 (by decide) (by decide),
                r3b_split_at fsp 0x320 48 0x4d0 (by decide) (by decide),
                r3b_split_at fsp 0x350 (0x3e0 - 0x350) 0x4d0 (by decide) (by decide)]
          have hf5c8 : memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) =
              memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                memRegion (fsp + 0x1750#64) 240 ∗
                memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) := by
            rw [r3b_split_at fsp 0x5c8 (0x1750 - 0x5c8) runLocalBytes (by decide) (by decide),
                r3b_split_at fsp 0x1750 240 runLocalBytes (by decide) (by decide)]
          rw [hf0, hf280, hf5c8]
          have hp_pack := r3b_addr_pack A peerG (fsp + 0x220#64) (fsp + 0x228#64)
            (fsp + 0x230#64) (fsp + 0x238#64) cw4 (by bv_omega) (by bv_omega) (by bv_omega) hdev_cw4
          have hm_pack := r3b_addr_pack A meG (fsp + 0x260#64) (fsp + 0x268#64)
            (fsp + 0x270#64) (fsp + 0x278#64) hiMe (by bv_omega) (by bv_omega) (by bv_omega) hhi
          simp only [sepExists_sepConj_left]
          apply Entails.sepExists_elim; intro pmG
          refine Entails.trans
            (r3b_perm
              (sepConj_mono (r3b_pkm_to_words A pmG (fsp + 0x4d0#64) pm)
                (sepConj_mono (r3b_mem40_to_slot5 fsp)
                  (sepConj_mono (r3b_mem40_to_slot5 (fsp + 0x2a0#64))
                    (sepConj_mono (r3b_mem240_to_slot30 (fsp + 0x3e0#64))
                      (sepConj_mono (r3b_mem240_to_slot30 (fsp + 0x1750#64))
                        (sepConj_mono hp_pack (sepConj_mono hm_pack
                          (Entails.refl (memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                            memRegion (fsp + 0x280#64) 0x20 ∗
                            memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                            memRegion (fsp + 0x320#64) 48 ∗
                            memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                            memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                            memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                            anyHeap)))))))))
              (by ac_rfl)) ?_
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply Entails.sepExists_elim; intro m
          apply Entails.sepExists_elim; intro z
          apply Entails.sepExists_elim; intro t
          apply Entails.sepExists_elim; intro t0
          apply Entails.sepExists_elim; intro w
          simp only [sepConj_assoc]
          apply Entails.pure_left; intro hcap_pm
          have ha4d8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
          rw [ha4d8]
          exact Entails.sepExists_right pmG (Entails.sepExists_right w
            (Entails.sepExists_right t0 (Entails.sepExists_right t
              (Entails.sepExists_right z (Entails.sepExists_right m
                (Entails.pure_right hcap_pm (Entails.of_eq (by ac_rfl))))))))
        apply r3b_sepWPp_weaken_pre
          (r3b_perm
            (sepConj_mono_left
              (Q := (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool ∗
                coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
                SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores StoresGhost.opened ∗
                runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
              hloc_shuf)
            (by dsimp only [fsp]; ac_rfl))
        simp only [sepExists_sepConj_left]
        apply r3b_sepWPp_exists_left; intro pmG
        apply r3b_sepWPp_exists_left; intro w
        apply r3b_sepWPp_exists_left; intro t0
        apply r3b_sepWPp_exists_left; intro t
        apply r3b_sepWPp_exists_left; intro z
        apply r3b_sepWPp_exists_left; intro m
        simp only [sepConj_assoc]
        apply r3b_sepWPp_pure_left; intro hcap_pm
        refine r3b_sepWPp_weaken_pre (Entails.of_eq (by dsimp only [fsp]))
          (r3b_recvP_shuf1_placed pmG.msg.pqCap w t z m _ hs2 hcap_pm hx26_2 hx27_2 ?_)
        intro s3 hs3 hx8_3 hx9_3 hx19_3 hx20_3 hx21_3 hx26_3 hx28_3 htr3 hfs3
        rw [hx19_2] at hx19_3
        rw [hx20_2] at hx20_3
        rw [hx21_2] at hx21_3
        rw [hx26_2] at hx26_3
        rw [hx28_2] at hx28_3
        let shuf2F : SepProp :=
          (((runFsp s0 + 1232#64) ↦₆₄ pmG.msg.pqCap ∗ r3b_slot30 (runFsp s0 + 1240#64) w) -∗
            preKeyMsgAt A pmG (runFsp s0 + 1232#64) pm) ∗
          memRegion (runFsp s0 + 672#64) 40 ∗
          memRegion (runFsp s0 + 5968#64) 240 ∗
          protocolAddressAt A peerG (runFsp s0 + 544#64) ∗
          protocolAddressAt A meG (runFsp s0 + 608#64) ∗
          memRegion (runFsp s0 + 40#64) (544 - 40) ∗
          memRegion (runFsp s0 + 640#64) 32 ∗
          memRegion (runFsp s0 + 712#64) (800 - 712) ∗
          memRegion (runFsp s0 + 800#64) 48 ∗
          memRegion (runFsp s0 + 848#64) (992 - 848) ∗
          memRegion (runFsp s0 + 1480#64) (5968 - 1480) ∗
          memRegion (runFsp s0 + 6208#64) (runLocalBytes - 6208) ∗
          anyHeap ∗
          (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool ∗
          coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          FromRecordCallees.lsLogOff ∗
          memRegion g.res runResSize ∗
          memRegion g.call 56 ∗
          storesAt A g.stores StoresGhost.opened ∗
          runSaved s0 ∗
          memRegion (runFsp s0 + 576#64) 32
        refine r3b_sepWPp_weaken_pre (Entails.of_eq (by dsimp only [fsp, shuf2F]; ac_rfl))
          (r3b_recvP_shuf2_placed g.stores pmG.msg.pqCap t0 w z shuf2F hs3 hx8_3 hx9_3 hx19_3 ?_)
        intro sc hinv_c hpc_c hrun_c hsp_c hsp_al_c hlr_c
          hx0_c hx1_c hx2_c hx3_c hx4_c hx5_c hx6_c hx7_c hx8_c
          hx19_c hx20_c hx21_c hx26_c hx28_c hfp_c hvregs_c htr_c hfs_c
        rw [hx20_3] at hx20_c
        rw [hx21_3] at hx21_c
        rw [hx26_3] at hx26_c
        rw [hx28_3] at hx28_c
        have htr_sc_eq : sc.trace = s2.trace := htr_c.trans htr3
        have hfs_sc_files : sc.fs.files = runFiles g.i :=
          (congrArg FsState.files (hfs_c.trans hfs3)).trans hfs2_files
        have htr_sc : s0.trace <+: sc.trace := htr_sc_eq ▸ htr2
        let dpX : DecPkGhost :=
          { peer := peerG
            peerA := fsp + 0x220#64
            me := meG
            meA := fsp + 0x260#64
            stores := g.stores
            ret := fsp + 0x320#64
            coinsP := g.coins
            F := runFiles g.i
            coins := MainHops.coinsOf g.i
            msgA := fsp + 0x4d0#64
            msgG := pmG
            msg := pm }
        have hdp_slot :
            CalleeSlot.OkPlaced (runProgPlaced H) (lsmpl.base 520)
              (mkSlot (decPkSlotSpecPlacedOf CodeOk A S) needs.decryptPrekey) :=
          hslot_eq ▸ hc.decryptPrekey
        refine r3b_call_raw
          (F := memRegion (fsp + 0x3e0#64) 240 ∗
            memRegion (fsp + 0x2a0#64) 40 ∗
            memRegion (fsp + 0x1750#64) 240 ∗
            memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
            memRegion (fsp + 0x280#64) 0x20 ∗
            memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
            memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
            memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
            memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
            anyHeap ∗
            (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
          (s0 := s0) dpX
          (hdp_slot (resStack - runFrame) hdp_stk hsub63) hinv_c
          hpc_c hrun_c hsp_al_c (retAddr := runPcPlaced 0xb78) hlr_c
          ?_
          (hpanic := fun sf R' _ hp => by
            dsimp only [mkSlot, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced, decPkSlotSpecPlaced,
              LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dpX] at hp
            rw [sepConj_assoc, satisfies_pure_sepConj] at hp
            rcases hp.1 with hnone | halloc
            · rw [hpeer_val, hme_val] at hnone
              apply hpanic sf _ (Or.inl ?_)
              rw [hga, hnone]; rfl
            · exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix htr_sc halloc)))
          (hoom := fun _ _ _ ho => by
            dsimp only [mkSlot, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced, decPkSlotSpecPlaced,
              LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dpX] at ho
            exact (not_satisfies_false_sepConj ho).elim)
          (hnext := fun s4 _ hinv4 hpcm4 hrun4 hsp4 hcsm4 => ?_)
        · dsimp only [mkSlot, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced, decPkSlotSpecPlaced,
            LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, slotFramePlaced, dpX]
          simp only [sepConj_assoc]
          apply Entails.pure_right
          · exact ⟨hx0_c, hx1_c, hx2_c, hx3_c, hx4_c, hx5_c, hx6_c, hx7_c, hx8_c, hfs_sc_files,
              by rw [hpeer_val, hme_val]; exact hfilesOk,
              by rw [hpeer_val, hme_val]; exact hdp_ok,
              hsp_c ▸ hfsp_sub⟩
          apply Entails.pure_right
          · exact hcoins63
          rw [hsp_c]
          have hpkm_restore :
              ((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w ∗
                ((((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w) -∗
                  preKeyMsgAt A pmG (fsp + 0x4d0#64) pm) ⊢
              preKeyMsgAt A pmG (fsp + 0x4d0#64) pm := by
            rw [← sepConj_assoc]
            exact Entails.wand_elim _ _
          exact r3b_perm
            (r3b_perm_post
              (Entails.pure_right hinv_c
                (sepConj_mono hpkm_restore
                  (Entails.refl ((fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                    ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗ ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                    ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                    memRegion (fsp + 0x3e0#64) 240 ∗
                    memRegion (fsp + 0x2a0#64) 40 ∗ memRegion (fsp + 0x1750#64) 240 ∗
                    protocolAddressAt A peerG (fsp + 0x220#64) ∗
                    protocolAddressAt A meG (fsp + 0x260#64) ∗
                    memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                    memRegion (fsp + 0x280#64) 0x20 ∗
                    memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                    memRegion (fsp + 0x320#64) 48 ∗
                    memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                    memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                    memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                    anyHeap ∗
                    (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                    stackAt fsp (resStack - runFrame) ∗ A.pool ∗
                    coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
                    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
                    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                    storesAt A g.stores StoresGhost.opened ∗
                    runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20))))
              (by dsimp only [fsp, shuf2F]; ac_rfl))
            (by dsimp only [fsp, shuf2F]; ac_rfl)
        · dsimp only [mkSlot, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced, decPkSlotSpecPlaced,
            LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dpX]
          simp only [sepExists_sepConj_left]
          apply r3b_sepWPp_exists_left; intro g'
          apply r3b_sepWPp_exists_left; intro e
          simp only [sepConj_assoc]
          apply r3b_sepWPp_pure_left; rintro ⟨⟨htr_dp, hfs_dp, hout_str_dp⟩, hout_dp⟩
          have hs4 : InRunPlaced CodeOk s0 s4 0xb78 :=
            r3b_inRun_step hs3 hpcm4 hrun4 (hsp4.trans (hsp_c.trans hs3.sp.symm))
              (hcsm4.2.2.2.2.2.2.2.2.2.2.1.trans hfp_c) hinv4
              (hcsm4.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_c)
          have htr4 : s0.trace <+: s4.trace := htr_sc.trans htr_dp
          have hhist4 : RunHistOk g.i s0 s4 :=
            ⟨hfs_dp.trans hfs_sc_files, hout_str_dp.trans (htr_sc_eq ▸ htr2_eq ▸ hd.stdout)⟩
          have hx19_4 : s4.readReg64 (.gpr 19#5) = g.stores := hcsm4.1.trans hx19_c
          have hx20_4 : s4.readReg64 (.gpr 20#5) = g.res := hcsm4.2.1.trans hx20_c
          have hx21_4 : s4.readReg64 (.gpr 21#5) = meG.name.cap := hcsm4.2.2.1.trans hx21_c
          have hx26_4 : s4.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
            hcsm4.2.2.2.2.2.2.2.1.trans hx26_c
          have hx28_4 : s4.readReg64 (.gpr 28#5) = meG.name.ptr :=
            hcsm4.2.2.2.2.2.2.2.2.2.1.trans hx28_c
          rw [hsp_c]
          have hpc4 : s4.pc = runPcPlaced 0xb78 := hs4.pc
          change s4.pc = (blkPl_579).base + 0xb78#64 at hpc4
          have hrun4' : s4.status = .Running := hs4.run
          have hsp4' : s4.sp = fsp := hs4.sp
          have hsp4_al : s4.spAligned = true := hs4.spAligned_cur
          apply r3b_seq (mid := (blkPl_555).base) hs4.inv
          wp_steps
          apply SepWP.done
            (by simp only [arm64_norm]; rfl)
            (by simp only [arm64_norm, hrun4'])
          intro hinv_dm
          refine r3b_call_lscro
            (F := storesAt A g.stores g' ∗
              decResAt A (fsp + 0x320#64) e ∗
              protocolAddressAt A peerG (fsp + 0x220#64) ∗
              protocolAddressAt A meG (fsp + 0x260#64) ∗
              (fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
              ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗ ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
              ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
              FromRecordCallees.lsLogOff ∗ anyHeap ∗
              memRegion (fsp + 0x3e0#64) 240 ∗
              memRegion (fsp + 0x2a0#64) 40 ∗
              memRegion (fsp + 0x1750#64) 240 ∗
              memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
              memRegion (fsp + 0x280#64) 0x20 ∗
              memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
              memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
              memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
              memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
              anyHeap ∗
              (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
            (s0 := s0) ⟨fsp + 0x4d0#64, pmG, pm⟩
            (dropPreKeyMsg_placed_ok hh (resStack - runFrame) hstk32 hsub64) hinv_dm
            (by simp only [arm64_norm]; rfl)
            (by simp only [arm64_norm, hrun4'])
            (by simpa only [State.spAligned, arm64_norm] using hsp4_al)
            (retAddr := runPcPlaced 0xb80)
            (by simp only [runPcPlaced_eq, arm64_norm])
            ?_
            (hnext := fun s5 hsteps_dm hinv5 hpcm5 hrun5 hsp5 hcsm5 => ?_)
          · dsimp only [dropPreKeyMsgSpec]
            simp only [sepConj_assoc]
            apply Entails.pure_right
            · dsimp only [fsp]; simp only [arm64_norm]
            simp only [arm64_norm]
            try rw [hsp4']
            exact Entails.of_eq (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
          · dsimp only [dropPreKeyMsgSpec]
            simp only [sepConj_assoc]
            apply r3b_sepWPp_pure_left; intro htr_dm
            have htr5_eq : s5.trace = s4.trace := htr_dm.trans (by simp only [arm64_norm])
            have hfs5_eq : s5.fs.files = s4.fs.files :=
              (r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_dm htr_dm).trans
                (by simp only [arm64_norm])
            have hs5_pre : InRunPlaced CodeOk s0 s5 0xb80 :=
              r3b_inRun_step hs4 hpcm5 hrun5 (hsp5.trans (by simp only [arm64_norm]))
                (hcsm5.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv5
                (hcsm5.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
            have hx19_5 : s5.readReg64 (.gpr 19#5) = g.stores := hcsm5.1.trans (by simp only [arm64_norm, hx19_4])
            have hx20_5 : s5.readReg64 (.gpr 20#5) = g.res := hcsm5.2.1.trans (by simp only [arm64_norm, hx20_4])
            have hx21_5 : s5.readReg64 (.gpr 21#5) = meG.name.cap := hcsm5.2.2.1.trans (by simp only [arm64_norm, hx21_4])
            have hx26_5 : s5.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
              hcsm5.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm]; exact hx26_4)
            have hx28_5 : s5.readReg64 (.gpr 28#5) = meG.name.ptr :=
              hcsm5.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx28_4])
            rw [← hsp5, hs5_pre.sp]
            have hpc5 : s5.pc = runPcPlaced 0xb80 := hs5_pre.pc
            change s5.pc = (blkPl_579).base + 0xb80#64 at hpc5
            have hrun5' : s5.status = .Running := hs5_pre.run
            apply r3b_seq (mid := runPcPlaced 0xd94) hs5_pre.inv
            rw [runPcPlaced_eq]
            wp_steps
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun5'])
            intro hinv6
            have hs6 : InRunPlaced CodeOk s0 (r3b_stOf hinv6) 0xd94 :=
              r3b_inRun_step hs5_pre (by simp only [runPcPlaced_eq, arm64_norm])
                (by simp only [arm64_norm, hrun5']) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) hinv6 (by simp only [calleeSavedVRegs, arm64_norm])
            have htr6_eq : (r3b_stOf hinv6).trace = s4.trace :=
              (by simp only [arm64_norm] : (r3b_stOf hinv6).trace = s5.trace).trans htr5_eq
            have hfs6_eq : (r3b_stOf hinv6).fs.files = s4.fs.files :=
              (by simp only [arm64_norm] : (r3b_stOf hinv6).fs.files = s5.fs.files).trans hfs5_eq
            have htr6 : s0.trace <+: (r3b_stOf hinv6).trace := htr6_eq ▸ htr4
            have hhist6 : RunHistOk g.i s0 (r3b_stOf hinv6) := r3b_hist_of_eq htr6_eq hfs6_eq hhist4
            have hclean6 :
                (memRegion (fsp + 0x4d0#64) 248 ∗
                  (fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                  ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗ ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                  ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                  memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                  memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
                  memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                  memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                  memRegion (fsp + 0x3e0#64) 240 ∗
                  memRegion (fsp + 0x1750#64) 240 ∗
                  memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                  memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840)) ∗
                (FromRecordCallees.lsLogOff ∗ anyHeap ∗ anyHeap) ⊢
                memRegion fsp 0x220 ∗
                  memRegion (fsp + 0x280#64) 0xa0 ∗
                  memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) ∗
                  anyHeap := by
              have h0_220 :
                  (fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                    ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗ ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                    ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                    memRegion (fsp + 0x28#64) (0x220 - 0x28) ⊢
                  memRegion fsp 0x220 := by
                have h40 := r3b_slot5_to_mem40 fsp
                  ⟨lsρ cliPreKeyVtSym, g.stores + 0x50#64, lsρ cliSignedPreKeyVtSym,
                    g.stores + 0x78#64, lsρ cliKyberPreKeyVtSym⟩
                dsimp only [r3b_slot5] at h40
                rw [ProofLib.memRegion_split' (b := fsp) (n := 40) (k := 0x220 - 0x28)
                      (b' := fsp + 0x28#64) rfl (by bv_omega) (by decide)]
                exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h40)
              have h280_a0 :
                  memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
                    memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) =
                  memRegion (fsp + 0x280#64) 0xa0 := by
                rw [r3b_split_at fsp 0x280 0x20 0x320 (by decide) (by decide),
                    r3b_split_at fsp 0x2a0 40 0x320 (by decide) (by decide)]
              have h350_all :
                  memRegion (fsp + 0x4d0#64) 248 ∗
                    memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                    memRegion (fsp + 0x3e0#64) 240 ∗
                    memRegion (fsp + 0x1750#64) 240 ∗
                    memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                    memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) =
                  memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) := by
                rw [r3b_split_at fsp 0x350 (0x3e0 - 0x350) runLocalBytes (by decide) (by decide),
                    r3b_split_at fsp 0x3e0 240 runLocalBytes (by decide) (by decide),
                    r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide),
                    r3b_split_at fsp 0x5c8 (0x1750 - 0x5c8) runLocalBytes (by decide) (by decide),
                    r3b_split_at fsp 0x1750 240 runLocalBytes (by decide) (by decide)]
                ac_rfl
              exact r3b_perm
                (sepConj_mono h0_220
                  (sepConj_mono (Entails.of_eq h280_a0)
                    (sepConj_mono (Entails.of_eq h350_all)
                      (entails_anyHeap (FromRecordCallees.lsLogOff ∗ anyHeap ∗ anyHeap)))))
                (by ac_rfl)
            have hinp_back : (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by
              rw [hinp_c, pointsToBytes_cons]
            cases e with
            | error err =>
              have hans_err : g.a = some none := by
                have hnone := hout_dp.2.2
                rw [hpeer_val, hme_val] at hnone
                rw [hga, hnone]; rfl
              refine r3b_sepWPp_weaken_pre ?_
                (r3b_recvP_dec_err_placed g' err peerG meG hh hdrop hstk32 hext_le hsub64 hs6
                  (by simp only [arm64_norm, hx19_5])
                  (by simp only [arm64_norm, hx20_5])
                  (by simp only [arm64_norm, hx21_5])
                  (by dsimp only [fsp] at hx26_5; simp only [arm64_norm, hx26_5])
                  (by simp only [arm64_norm, hx28_5])
                  htr6 hhist6 hans_err hrej)
              exact r3b_perm
                (r3b_perm_post
                  (sepConj_mono hclean6
                    (sepConj_mono (Entails.of_eq hinp_back)
                      (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                        storesAt A g.stores g' ∗
                        protocolAddressAt A peerG (fsp + 0x220#64) ∗
                        protocolAddressAt A meG (fsp + 0x260#64) ∗
                        runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20 ∗
                        decResAt A (fsp + 0x320#64) (.error err) ∗
                        stackAt fsp (resStack - runFrame) ∗ A.pool))))
                  (by dsimp only [fsp]; ac_rfl))
                (by dsimp only [fsp]; ac_rfl)
            | ok pt =>
              have hout_ok : g.a = some (some (namedWrites g'.writes, pt)) ∧
                  ∀ pw ∈ g'.writes, cliWrOk pw.1 := by
                rcases hout_dp.2.2 with ⟨hsome, hwrok⟩
                rw [hpeer_val, hme_val] at hsome
                exact ⟨by rw [hga, hsome]; rfl, hwrok⟩
              refine r3b_sepWPp_weaken_pre ?_
                (r3b_recvP_dec_ok_placed g' pt peerG meG hh hext_le hsub64 hs6
                  (by simp only [arm64_norm, hx19_5])
                  (by simp only [arm64_norm, hx20_5])
                  (by simp only [arm64_norm, hx21_5])
                  (by simp only [arm64_norm, hx28_5])
                  htr6 hhist6 hout_ok.1 hout_ok.2 hjoin)
              exact r3b_perm
                (r3b_perm_post
                  (sepConj_mono hclean6
                    (sepConj_mono (Entails.of_eq hinp_back)
                      (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                        storesAt A g.stores g' ∗
                        protocolAddressAt A peerG (fsp + 0x220#64) ∗
                        protocolAddressAt A meG (fsp + 0x260#64) ∗
                        runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20 ∗
                        decResAt A (fsp + 0x320#64) (.ok pt) ∗
                        stackAt fsp (resStack - runFrame) ∗ A.pool))))
                  (by dsimp only [fsp]; ac_rfl))
                (by dsimp only [fsp]; ac_rfl)

theorem run_hop_recvP_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopRecvPPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack :=
  run_hop_recvP_of_codeOk rfl rfl

end CryptoVerification.SignalSession.Cli.RunCompose
