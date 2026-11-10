/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpper
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

private def r1b_owned3_placed (A : RustAlloc)
    (kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64)
    (kpkBs spkBs regBs : List (BitVec 8)) : SepProp :=
  ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
  ownedBytes A spkCap spkPtr spkLen spkBs ∗
  ownedBytes A regCap regPtr regLen regBs

private theorem r1b_fold_owned3_placed (A : RustAlloc)
    (kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64)
    (kpkBs spkBs regBs : List (BitVec 8)) (R : SepProp) :
    ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
      ownedBytes A spkCap spkPtr spkLen spkBs ∗
      ownedBytes A regCap regPtr regLen regBs ∗ R =
      r1b_owned3_placed A kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
        kpkBs spkBs regBs ∗ R := by
  dsimp only [r1b_owned3_placed]; simp only [sepConj_assoc]

private def r1b_mid9_placed (fsp spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 : BitVec 64) : SepProp :=
  ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
  memRegion (fsp + 0x178#64) 8 ∗
  ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
  ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
  ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0)

private theorem r1b_fold_mid9_placed
    (fsp spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 : BitVec 64) (R : SepProp) :
    ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (fsp + 0x178#64) 8 ∗
      ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
      ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
      ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗ R =
      r1b_mid9_placed fsp spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 ∗ R := by
  dsimp only [r1b_mid9_placed]; simp only [sepConj_assoc]

private def r1b_mid7_placed (fsp spkPtr spkCap regCap regPtr : BitVec 64) : SepProp :=
  ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
  memRegion (fsp + 0x178#64) 8 ∗
  memRegion (fsp + 0x188#64) 16 ∗
  ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
  memRegion (fsp + 0x1a8#64) 16

private theorem r1b_fold_mid7_placed
    (fsp spkPtr spkCap regCap regPtr : BitVec 64) (R : SepProp) :
    ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (fsp + 0x178#64) 8 ∗
      memRegion (fsp + 0x188#64) 16 ∗
      ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
      memRegion (fsp + 0x1a8#64) 16 ∗ R =
      r1b_mid7_placed fsp spkPtr spkCap regCap regPtr ∗ R := by
  dsimp only [r1b_mid7_placed]; simp only [sepConj_assoc]
private theorem r1b_cleanup_2adc_cap0_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hx1 : s.readReg64 (.gpr 1#5) = 0#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A 0#64 kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  change s.pc = (blkPl_579).base + 0x2adc#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2b24) hinv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b24 := {
    st := {
      pc := by simp only [hsm, arm64_norm]
      run := by simp only [hsm, arm64_norm, hrun]
      sp := by simpa only [hsm, arm64_norm] using hc.st.sp
      fp := by simpa only [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    x19 := by simpa only [hsm, arm64_norm] using hc.x19
    x20 := by simpa only [hsm, arm64_norm] using hc.x20
    x21 := by simpa only [hsm, arm64_norm] using hc.x21
    trace := by simpa only [hsm, arm64_norm] using hc.trace
    hist := ⟨by simpa only [hsm, arm64_norm] using hc.hist.1,
      by simpa only [hsm, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  have hr12 : sm.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by simp only [hsm, arm64_norm]
  have hr10 : sm.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 10#5) := by simp only [hsm, arm64_norm]
  have hr23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm, arm64_norm]
  have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, arm64_norm]
  have hr16 : sm.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by simp only [hsm, arm64_norm]
  have hr14 : sm.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by simp only [hsm, arm64_norm]
  have hr15 : sm.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by simp only [hsm, arm64_norm]
  have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, arm64_norm]
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2b24_placed (v188 := v188) (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen)
      (spkBs := spkBs) (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej)
  rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28]
  dsimp only [r1b_errCommon]; rw [herrCore, r1b_fold_low4]
  dsimp only [fsp]
  have hdrop_kpk : ownedBytes A 0#64 kpkPtr kpkLen kpkBs ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A (s.readReg64 (.gpr 12#5))
      (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
      (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
      (s.readReg64 (.gpr 28#5)) v188 ∗
    ownedBytes A spkCap spkPtr spkLen spkBs ∗
    ownedBytes A regCap regPtr regLen regBs ∗
    (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (ownedBytes A 0#64 kpkPtr kpkLen kpkBs ∗ anyHeap)) ∗
    r1b_errLow4 (runFsp s0) ∗
    ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
    memRegion (runFsp s0 + 0x178#64) 8 ∗
    ((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗ memRegion (runFsp s0 + 0x190#64) 8 ∗
    ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
    memRegion (runFsp s0 + 0x1a8#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hdrop_kpk))))))
set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2adc_capNe_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hx1 : s.readReg64 (.gpr 1#5) = kpkCap)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hcap : kpkCap ≠ 0#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hcap_f : (kpkCap == 0#64) = false := beq_false_of_ne hcap
  rw [ProofLib.memRegion_eight (fsp + 0x190#64), r1b_region16_to_cells (fsp + 0x1a8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v190 => SepWPp.exists_elim fun v1a8 =>
    SepWPp.exists_elim fun v1b0 => ?_
  have ho1b0 : fsp + 0x1a8#64 + 8#64 = fsp + 0x1b0#64 := by bv_omega
  rw [ho1b0]
  change s.pc = (blkPl_579).base + 0x2adc#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hsm_run : sm.status = .Running := by simp only [hsm, arm64_norm, hrun]
  have hsm_sp0 : sm.sp = runFsp s0 := by simpa only [hsm, arm64_norm] using hc.st.sp
  have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
  have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
  have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by simp only [hsm, arm64_norm]
  have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2b08 := by simp only [hsm, arm64_norm]
  have hsm_a0 : sm.readReg64 .x0 = kpkPtr := by simp only [hsm, arm64_norm]
  have hsm_a1 : sm.readReg64 .x1 = kpkCap := by simp only [hsm, arm64_norm, hx1]
  have hsm_a2 : sm.readReg64 .x2 = 1#64 := by simp only [hsm, arm64_norm]
  have hsm_x19 : sm.readReg64 (.gpr 19#5) = g.stores := by simpa only [hsm, arm64_norm] using hc.x19
  have hsm_x20 : sm.readReg64 (.gpr 20#5) = g.res := by simpa only [hsm, arm64_norm] using hc.x20
  have hsm_x21 : sm.readReg64 (.gpr 21#5) = d.meG.name.cap := by simpa only [hsm, arm64_norm] using hc.x21
  have hsm_r22 : sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 16#5) := by simp only [hsm, arm64_norm]
  have hsm_r23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 14#5) := by simp only [hsm, arm64_norm]
  have hsm_r24 : sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 10#5) := by simp only [hsm, arm64_norm]
  have hsm_r25 : sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 12#5) := by simp only [hsm, arm64_norm]
  have hsm_r26 : sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 15#5) := by simp only [hsm, arm64_norm]
  have hsm_r27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, arm64_norm]
  have hsm_r28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, arm64_norm]
  have hsm_fs : sm.fs = s.fs := by simp only [hsm, arm64_norm]
  have hsm_tr : sm.trace = s.trace := by simp only [hsm, arm64_norm]
  clear hsm
  rw [← hfsp_eq]
  refine MainHops.sepWPp_weaken_pre (P' :=
      ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        errCore ∗ anyHeap ∗ r1b_errLow4 (runFsp s0) ∗
        ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (runFsp s0 + 0x178#64) 8 ∗
        ((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗
        ((runFsp s0 + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ∗
        ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 13#5)) ∗
        ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48)) ?_ ?_
  · exact Entails.of_eq (by ac_rfl)
  refine r1b_call_dealloc_ownedBytes_placed (Q := Q) (cap := kpkCap) (ptr := kpkPtr) (len := kpkLen) (bs := kpkBs)
    hh hbnd hinv_m hsm_pc hsm_run
    hsm_sp0 hsm_fp hsm_vr hsp0 hsm_lr
    hsm_a0 hsm_a1 hsm_a2
    hcap hpanic ?_
  intro s1 hin1 hcs1 hfs1 htr1
  rw [hfsp_eq]
  have hpc1 := hin1.pc; have hrun1 := hin1.run
  have hsp1 : s1.sp = fsp := hin1.sp
  have hfp1 := hin1.fp; have hinv1 := hin1.inv; have hvregs1 := hin1.vregs
  change s1.pc = (blkPl_579).base + 0x2b08#64 at hpc1
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2b24) hinv1
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  rcases hcs1 with ⟨hc19, hc20, hc21, hc22, hc24, hc25, hc26, hc27, hc28, hc29, _, _⟩
  have htr2 : sm2.trace = s.trace := by simp only [hsm2, arm64_norm]; exact htr1.trans hsm_tr
  have hfs2 : sm2.fs = s.fs := by simp only [hsm2, arm64_norm]; exact hfs1.trans hsm_fs
  have hc_m2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2b24 := {
    st := {
      pc := by simp only [hsm2, arm64_norm]
      run := by simp only [hsm2, arm64_norm, hrun1]
      sp := by simpa only [hsm2, arm64_norm] using hin1.sp
      fp := by simpa only [hsm2, arm64_norm] using hfp1
      inv := hinv2
      vregs := by simpa only [calleeSavedVRegs, hsm2, arm64_norm] using hvregs1
      spAligned := hsp0
    }
    x19 := by simp only [hsm2, arm64_norm, hc19, hsm_x19]
    x20 := by simp only [hsm2, arm64_norm, hc20, hsm_x20]
    x21 := by simp only [hsm2, arm64_norm, hc21, hsm_x21]
    trace := htr2 ▸ hc.trace
    hist := ⟨by rw [hfs2]; exact hc.hist.1, by rw [htr2]; exact hc.hist.2⟩
    ans := hc.ans
  }
  have hr12 : sm2.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by
    simp only [hsm2, arm64_norm, hc26, hsm_r25]
  have hr10 : sm2.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 10#5) := by
    simp only [hsm2, arm64_norm, hc25, hsm_r24]
  have hr23 : sm2.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm2, arm64_norm]
  have hr27 : sm2.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
    simp only [hsm2, arm64_norm, hc28, hsm_r27]
  have hr16 : sm2.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
    simp only [hsm2, arm64_norm, hc22, hsm_r22]
  have hr14 : sm2.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
    simp only [hsm2, arm64_norm, hc24, hsm_r23]
  have hr15 : sm2.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
    simp only [hsm2, arm64_norm, hc27, hsm_r26]
  have hr28 : sm2.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
    simp only [hsm2, arm64_norm, hc29, hsm_r28]
  clear hsm2
  have hre190 : ((fsp + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ⊢ memRegion (fsp + 0x190#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have hre1a8 : ((fsp + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 13#5)) ∗
      ((fsp + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ⊢ memRegion (fsp + 0x1a8#64) 16 := by
    have ha2 : fsp + 0x1b0#64 = (fsp + 0x1a8#64) + 8#64 := by bv_omega
    rw [ha2]; exact r1b_cells2_to_region16 _ _ _
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2b24_placed (v188 := v188) (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen)
      (spkBs := spkBs) (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m2 hpanic hrej)
  rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28]
  dsimp only [r1b_errCommon]; rw [herrCore, r1b_fold_low4]
  dsimp only [fsp] at hre190 hre1a8 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A (s.readReg64 (.gpr 12#5))
      (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
      (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
      (s.readReg64 (.gpr 28#5)) v188 ∗
    ownedBytes A spkCap spkPtr spkLen spkBs ∗
    ownedBytes A regCap regPtr regLen regBs ∗
    (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) ∗
    r1b_errLow4 (runFsp s0) ∗
    ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
    memRegion (runFsp s0 + 0x178#64) 8 ∗
    ((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗
    ((runFsp s0 + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ∗
    ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
    (((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 13#5)) ∗
      ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5))) ∗
    memRegion (runFsp s0 + 0x4d0#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono hre190
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hre1a8))))))))))))
theorem r1b_cleanup_2adc_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hx1 : s.readReg64 (.gpr 1#5) = kpkCap)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  by_cases hcap : kpkCap = 0#64
  · subst hcap; exact r1b_cleanup_2adc_cap0_placed hh hdrop hbnd hc hx1 hpanic hrej
  · exact r1b_cleanup_2adc_capNe_placed hh hdrop hbnd hc hx1 hx26 hcap hpanic hrej

theorem r1b_cleanup_2abc_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v120 v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2abc)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ v120) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  rw [r1b_fold_owned3_placed]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hal4 : (fsp + 0x11c#64) &&& 3#64 = 0#64 := by bv_bits
  change s.pc = (blkPl_579).base + 0x2abc#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2adc) hinv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := {
    st := {
      pc := by simp only [hsm, arm64_norm]
      run := by simp only [hsm, arm64_norm, hrun]
      sp := by simpa only [hsm, arm64_norm] using hc.st.sp
      fp := by simpa only [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    x19 := by simpa only [hsm, arm64_norm] using hc.x19
    x20 := by simpa only [hsm, arm64_norm] using hc.x20
    x21 := by simpa only [hsm, arm64_norm] using hc.x21
    trace := by simpa only [hsm, arm64_norm] using hc.trace
    hist := ⟨by simpa only [hsm, arm64_norm] using hc.hist.1,
      by simpa only [hsm, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  have hr12 : sm.readReg64 (.gpr 12#5) = v158 := by simp only [hsm, arm64_norm]
  have hr10 : sm.readReg64 (.gpr 10#5) = v11c.zeroExtend 64 := by simp only [hsm, arm64_norm]
  have hr23 : sm.readReg64 (.gpr 23#5) = v1b0 := by simp only [hsm, arm64_norm]
  have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, arm64_norm]
  have hr16 : sm.readReg64 (.gpr 16#5) = v190 := by simp only [hsm, arm64_norm]
  have hr14 : sm.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 24#5) := by simp only [hsm, arm64_norm]
  have hr15 : sm.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm, arm64_norm]
  have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, arm64_norm]
  have hre11c : ((fsp + 0x11c#64) ↦₃₂ v11c) ⊢ memRegion (fsp + 0x11c#64) 4 := by
    rw [ProofLib.memRegion_four]; exact Entails.sepExists_right v11c (Entails.refl _)
  have hre120 : ((fsp + 0x120#64) ↦₆₄ v120) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ⊢
      memRegion (fsp + 0x120#64) 16 := by
    have ha : fsp + 0x128#64 = (fsp + 0x120#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cells2_to_region16 _ _ _
  have hre150 : ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ⊢
      memRegion (fsp + 0x150#64) 16 := by
    have ha : fsp + 0x158#64 = (fsp + 0x150#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cells2_to_region16 _ _ _
  have hre190 : ((fsp + 0x190#64) ↦₆₄ v190) ⊢ memRegion (fsp + 0x190#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have hre1a8 : ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ⊢
      memRegion (fsp + 0x1a8#64) 16 := by
    have ha : fsp + 0x1b0#64 = (fsp + 0x1a8#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cells2_to_region16 _ _ _
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2adc_placed (v188 := v188) (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen)
      (kpkBs := kpkBs) (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm]) hpanic hrej)
  rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28, herrCommon, r1b_fold_owned3_placed]
  dsimp only [fsp] at hre11c hre120 hre150 hre190 hre1a8 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A v158 (v11c.zeroExtend 64) v1b0
      (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
      (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
    r1b_owned3_placed A kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
      kpkBs spkBs regBs ∗
    errCommon ∗
    memRegion (runFsp s0 + 0x110#64) 8 ∗
    ((runFsp s0 + 0x11c#64) ↦₃₂ v11c) ∗
    (((runFsp s0 + 0x120#64) ↦₆₄ v120) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr)) ∗
    (((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ v158)) ∗
    ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
    memRegion (runFsp s0 + 0x178#64) 8 ∗
    ((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗
    ((runFsp s0 + 0x190#64) ↦₆₄ v190) ∗
    ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
    (((runFsp s0 + 0x1a8#64) ↦₆₄ v1a8) ∗ ((runFsp s0 + 0x1b0#64) ↦₆₄ v1b0)) ∗
    memRegion (runFsp s0 + 0x4d0#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hre11c (sepConj_mono hre120 (sepConj_mono hre150
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hre190 (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hre1a8))))))))))))))

private theorem r1b_cleanup_2aa8_cap0_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2aa8)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A 0#64 opkPtr opkLen opkBs ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ 0#64) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq, r1b_fold_owned3_placed, r1b_fold_mid9_placed]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2aa8#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2abc) hinv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2abc := {
    st := {
      pc := by simp only [hsm, arm64_norm]
      run := by simp only [hsm, arm64_norm, hrun]
      sp := by simpa only [hsm, arm64_norm] using hc.st.sp
      fp := by simpa only [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    x19 := by simpa only [hsm, arm64_norm] using hc.x19
    x20 := by simpa only [hsm, arm64_norm] using hc.x20
    x21 := by simpa only [hsm, arm64_norm] using hc.x21
    trace := by simpa only [hsm, arm64_norm] using hc.trace
    hist := ⟨by simpa only [hsm, arm64_norm] using hc.hist.1,
      by simpa only [hsm, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, arm64_norm]
  have hr24 : sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := by simp only [hsm, arm64_norm]
  have hr23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm, arm64_norm]
  have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, arm64_norm]
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2abc_placed (v11c := v11c) (v120 := opkPtr) (v158 := v158) (v188 := v188)
      (v190 := v190) (v1a8 := v1a8) (v1b0 := v1b0)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej)
  rw [hr27, hr24, hr23, hr28]
  dsimp only [r1b_errCommon]; rw [herrCore]
  dsimp only [fsp]
  rw [r1b_fold_owned3_placed, r1b_fold_mid9_placed]
  have hdrop_opk : ownedBytes A 0#64 opkPtr opkLen opkBs ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
  have hre110 : ((runFsp s0 + 0x110#64) ↦₆₄ 0#64) ⊢ memRegion (runFsp s0 + 0x110#64) 8 :=
    pointsTo64_entails_memRegion _ _
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A v158 (v11c.zeroExtend 64) v1b0
      (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
      (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
    r1b_owned3_placed A kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
      kpkBs spkBs regBs ∗
    (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (ownedBytes A 0#64 opkPtr opkLen opkBs ∗ anyHeap)) ∗
    ((runFsp s0 + 0x110#64) ↦₆₄ 0#64) ∗ ((runFsp s0 + 0x11c#64) ↦₃₂ v11c) ∗
    ((runFsp s0 + 0x120#64) ↦₆₄ opkPtr) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr) ∗
    ((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ v158) ∗
    r1b_mid9_placed (runFsp s0) spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 ∗
    memRegion (runFsp s0 + 0x4d0#64) 48 by dsimp only [r1b_owned3_placed]; ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hdrop_opk)))
      (sepConj_mono_left hre110)))

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2aa8_capNe_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2aa8)
    (hcap : opkCap ≠ 0#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A opkCap opkPtr opkLen opkBs ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq, r1b_fold_owned3_placed, r1b_fold_mid9_placed]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hcap_f : (opkCap == 0#64) = false := beq_false_of_ne hcap
  change s.pc = (blkPl_579).base + 0x2aa8#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hsm_sp0 : sm.sp = runFsp s0 := by simpa only [hsm, arm64_norm] using hc.st.sp
  have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
  have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
  have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by simp only [hsm, arm64_norm]
  have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2abc := by simp only [hsm, arm64_norm]
  have hsm_run : sm.status = .Running := by simp only [hsm, arm64_norm, hrun]
  have hsm_a0 : sm.readReg64 .x0 = opkPtr := by simp only [hsm, arm64_norm]
  have hsm_a1 : sm.readReg64 .x1 = opkCap := by simp only [hsm, arm64_norm]
  have hsm_a2 : sm.readReg64 .x2 = 1#64 := by simp only [hsm, arm64_norm]
  have hsm_x19 : sm.readReg64 (.gpr 19#5) = g.stores := by simpa only [hsm, arm64_norm] using hc.x19
  have hsm_x20 : sm.readReg64 (.gpr 20#5) = g.res := by simpa only [hsm, arm64_norm] using hc.x20
  have hsm_x21 : sm.readReg64 (.gpr 21#5) = d.meG.name.cap := by simpa only [hsm, arm64_norm] using hc.x21
  have hsm_r23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm, arm64_norm]
  have hsm_r24 : sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := by simp only [hsm, arm64_norm]
  have hsm_r27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, arm64_norm]
  have hsm_r28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, arm64_norm]
  have hsm_fs : sm.fs = s.fs := by simp only [hsm, arm64_norm]
  have hsm_tr : sm.trace = s.trace := by simp only [hsm, arm64_norm]
  clear hsm
  rw [← hfsp_eq]
  refine MainHops.sepWPp_weaken_pre (P' :=
      ownedBytes A opkCap opkPtr opkLen opkBs ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (r1b_SpePayload A v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        r1b_owned3_placed A kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
          kpkBs spkBs regBs ∗
        errCore ∗ anyHeap ∗
        ((runFsp s0 + 0x110#64) ↦₆₄ opkCap) ∗ ((runFsp s0 + 0x11c#64) ↦₃₂ v11c) ∗
        ((runFsp s0 + 0x120#64) ↦₆₄ opkPtr) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ v158) ∗
        r1b_mid9_placed (runFsp s0) spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 ∗
        memRegion (runFsp s0 + 0x4d0#64) 48)) ?_ ?_
  · exact Entails.of_eq (by dsimp only [r1b_owned3_placed]; ac_rfl)
  refine r1b_call_dealloc_ownedBytes_placed (Q := Q) (cap := opkCap) (ptr := opkPtr) (len := opkLen) (bs := opkBs)
    hh hbnd hinv_m hsm_pc hsm_run
    hsm_sp0 hsm_fp hsm_vr hsp0 hsm_lr
    hsm_a0 hsm_a1 hsm_a2
    hcap hpanic ?_
  intro s1 hin1 hcs1 hfs1 htr1
  rcases hcs1 with ⟨hc19, hc20, hc21, hc22, hc24, hc25, hc26, hc27, hc28, hc29, _, _⟩
  have htr1' : s1.trace = s.trace := htr1.trans hsm_tr
  have hfs1' : s1.fs = s.fs := hfs1.trans hsm_fs
  have hc_f : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s1 0x2abc := {
    st := hin1
    x19 := hc19.trans hsm_x19
    x20 := hc20.trans hsm_x20
    x21 := hc21.trans hsm_x21
    trace := htr1' ▸ hc.trace
    hist := ⟨by rw [hfs1']; exact hc.hist.1, by rw [htr1']; exact hc.hist.2⟩
    ans := hc.ans
  }
  have hr27 : s1.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := hc28.trans hsm_r27
  have hr24 : s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := hc25.trans hsm_r24
  have hr23 : s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := hc24.trans hsm_r23
  have hr28 : s1.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := hc29.trans hsm_r28
  have hre110 : ((runFsp s0 + 0x110#64) ↦₆₄ opkCap) ⊢ memRegion (runFsp s0 + 0x110#64) 8 :=
    pointsTo64_entails_memRegion _ _
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2abc_placed (v11c := v11c) (v120 := opkPtr) (v158 := v158) (v188 := v188)
      (v190 := v190) (v1a8 := v1a8) (v1b0 := v1b0)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_f hpanic hrej)
  rw [hr27, hr24, hr23, hr28]
  dsimp only [r1b_errCommon]; rw [herrCore, r1b_fold_owned3_placed, r1b_fold_mid9_placed]
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A v158 (v11c.zeroExtend 64) v1b0
      (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
      (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
    r1b_owned3_placed A kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
      kpkBs spkBs regBs ∗
    (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) ∗
    ((runFsp s0 + 0x110#64) ↦₆₄ opkCap) ∗ ((runFsp s0 + 0x11c#64) ↦₃₂ v11c) ∗
    ((runFsp s0 + 0x120#64) ↦₆₄ opkPtr) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr) ∗
    ((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ v158) ∗
    r1b_mid9_placed (runFsp s0) spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 ∗
    memRegion (runFsp s0 + 0x4d0#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left hre110)))

theorem r1b_cleanup_2aa8_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v11c : BitVec 32}
    {v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2aa8)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A v158 (v11c.zeroExtend 64) v1b0
          (s.readReg64 (.gpr 27#5)) v190 (s.readReg64 (.gpr 24#5))
          (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A opkCap opkPtr opkLen opkBs ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  by_cases hcap : opkCap = 0#64
  · subst hcap; exact r1b_cleanup_2aa8_cap0_placed hh hdrop hbnd hc hpanic hrej
  · exact r1b_cleanup_2aa8_capNe_placed hh hdrop hbnd hc hcap hpanic hrej
theorem r1b_cleanup_2a8c_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a8c)
    (hi : RunDrop.PlainSpeTag i)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A opkCap opkPtr opkLen opkBs ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  rw [r1b_fold_owned3_placed, ProofLib.memRegion_four (fsp + 0x11c#64),
    r1b_region16_to_cells (fsp + 0x188#64),
    r1b_region16_to_cells (fsp + 0x1a8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun (v1b0 : BitVec 64) =>
    SepWPp.exists_elim fun (v1a8 : BitVec 64) => SepWPp.exists_elim fun (v190 : BitVec 64) =>
    SepWPp.exists_elim fun (v188 : BitVec 64) => SepWPp.exists_elim fun (v11c : BitVec 32) => ?_
  have ho190 : fsp + 0x188#64 + 8#64 = fsp + 0x190#64 := by bv_omega
  have ho1b0 : fsp + 0x1a8#64 + 8#64 = fsp + 0x1b0#64 := by bv_omega
  rw [ho190, ho1b0]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hal4 : (fsp + 0x11c#64) &&& 3#64 = 0#64 := by bv_bits
  change s.pc = (blkPl_579).base + 0x2a8c#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2aa8) hinv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2aa8 := {
    st := {
      pc := by simp only [hsm, arm64_norm]
      run := by simp only [hsm, arm64_norm, hrun]
      sp := by simpa only [hsm, arm64_norm] using hc.st.sp
      fp := by simpa only [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    x19 := by simpa only [hsm, arm64_norm] using hc.x19
    x20 := by simpa only [hsm, arm64_norm] using hc.x20
    x21 := by simpa only [hsm, arm64_norm] using hc.x21
    trace := by simpa only [hsm, arm64_norm] using hc.trace
    hist := ⟨by simpa only [hsm, arm64_norm] using hc.hist.1,
      by simpa only [hsm, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, arm64_norm]
  have hr24 : sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := by simp only [hsm, arm64_norm]
  have hr23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm, arm64_norm]
  have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, arm64_norm]
  let w32 : BitVec 32 :=
    BitVec.truncate 32 (s.readReg64 (Reg.gpr 8#5)) |||
      (BitVec.truncate 32 (s.readReg64 (Reg.gpr 9#5)) &&& 255#32)
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2aa8_placed
      (v11c := w32) (v158 := speWord i)
      (v188 := BitVec.zeroExtend 64 w32) (v190 := BitVec.zeroExtend 64 w32)
      (v1a8 := v1b0) (v1b0 := s.readReg64 (Reg.gpr 8#5) >>> 32)
      (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := opkLen) (opkBs := opkBs)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej)
  dsimp only [w32]
  rw [hr27, hr24, hr23, hr28, herrCommon]
  dsimp only [fsp, r1b_owned3_placed]
  rw [← emp_sepConj (ownedBytes A opkCap opkPtr opkLen opkBs ∗ _)]
  refine Entails.trans ?_
    (sepConj_mono_left (r1b_SpePayload_plain A hi _ _ _ _ _ _ _ _))
  exact Entails.of_eq (by ac_rfl)
theorem r1b_cleanup_2a88_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a88)
    (hi : RunDrop.PlainSpeTag i)
    (hx9 : s.readReg64 (.gpr 9#5) = speWord i)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A opkCap opkPtr opkLen opkBs ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  rw [r1b_fold_owned3_placed, r1b_fold_mid7_placed, ProofLib.memRegion_eight (fsp + 0x158#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v158 => ?_
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2a88#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2a8c) hinv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2a8c := {
    st := {
      pc := by simp only [hsm, arm64_norm]
      run := by simp only [hsm, arm64_norm, hrun]
      sp := by simpa only [hsm, arm64_norm] using hc.st.sp
      fp := by simpa only [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    x19 := by simpa only [hsm, arm64_norm] using hc.x19
    x20 := by simpa only [hsm, arm64_norm] using hc.x20
    x21 := by simpa only [hsm, arm64_norm] using hc.x21
    trace := by simpa only [hsm, arm64_norm] using hc.trace
    hist := ⟨by simpa only [hsm, arm64_norm] using hc.hist.1,
      by simpa only [hsm, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2a8c_placed
      (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := opkLen) (opkBs := opkBs)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m hi hpanic hrej)
  rw [herrCommon]
  dsimp only [fsp, r1b_owned3_placed, r1b_mid7_placed]
  exact Entails.of_eq (by ac_rfl)
theorem r1b_cleanup_2a78_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a78)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A opkCap opkPtr opkLen opkBs ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  rw [r1b_fold_owned3_placed, r1b_fold_mid7_placed, ProofLib.memRegion_eight (fsp + 0x158#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v158 => ?_
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2a78#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2a8c) hinv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2a8c := {
    st := {
      pc := by simp only [hsm, arm64_norm]
      run := by simp only [hsm, arm64_norm, hrun]
      sp := by simpa only [hsm, arm64_norm] using hc.st.sp
      fp := by simpa only [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    x19 := by simpa only [hsm, arm64_norm] using hc.x19
    x20 := by simpa only [hsm, arm64_norm] using hc.x20
    x21 := by simpa only [hsm, arm64_norm] using hc.x21
    trace := by simpa only [hsm, arm64_norm] using hc.trace
    hist := ⟨by simpa only [hsm, arm64_norm] using hc.hist.1,
      by simpa only [hsm, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2a8c_placed (i := 10)
      (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := opkLen) (opkBs := opkBs)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m (by decide) hpanic hrej)
  rw [herrCommon]
  dsimp only [fsp, speWord, r1b_owned3_placed, r1b_mid7_placed]
  exact Entails.of_eq (by ac_rfl)
theorem r1b_cleanup_2a60_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {opkCap opkPtr opkLen kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2a60)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A opkCap opkPtr opkLen opkBs ∗
        ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hsplit4d0 : memRegion (fsp + 0x4d0#64) 48 =
      memRegion (fsp + 0x4d0#64) 9 ∗ (∃∗ b4d9 : BitVec 8, (fsp + 0x4d9#64) ↦₈ b4d9) ∗
        memRegion (fsp + 0x4da#64) 38 := by
    rw [show (48 : Nat) = 9 + 39 from rfl,
      ProofLib.memRegion_split (fsp + 0x4d0#64) 9 39 (by decide),
      show fsp + 0x4d0#64 + 9#64 = fsp + 0x4d9#64 from by bv_omega,
      show (39 : Nat) = 1 + 38 from rfl,
      ProofLib.memRegion_split (fsp + 0x4d9#64) 1 38 (by decide),
      show fsp + 0x4d9#64 + 1#64 = fsp + 0x4da#64 from by bv_omega,
      ProofLib.memRegion_one (fsp + 0x4d9#64)]
  rw [r1b_fold_owned3_placed, r1b_fold_mid7_placed, ProofLib.memRegion_eight (fsp + 0x158#64), hsplit4d0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun (b4d9 : BitVec 8) => SepWPp.exists_elim fun (v158 : BitVec 64) => ?_
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2a60#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2a8c) hinv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2a8c := {
    st := {
      pc := by simp only [hsm, arm64_norm]
      run := by simp only [hsm, arm64_norm, hrun]
      sp := by simpa only [hsm, arm64_norm] using hc.st.sp
      fp := by simpa only [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    x19 := by simpa only [hsm, arm64_norm] using hc.x19
    x20 := by simpa only [hsm, arm64_norm] using hc.x20
    x21 := by simpa only [hsm, arm64_norm] using hc.x21
    trace := by simpa only [hsm, arm64_norm] using hc.trace
    hist := ⟨by simpa only [hsm, arm64_norm] using hc.hist.1,
      by simpa only [hsm, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  have hre4d0 : memRegion (fsp + 0x4d0#64) 9 ∗ ((fsp + 0x4d9#64) ↦₈ b4d9) ∗
      memRegion (fsp + 0x4da#64) 38 ⊢ memRegion (fsp + 0x4d0#64) 48 := by
    rw [hsplit4d0]
    exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right b4d9 (Entails.refl _)))
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2a8c_placed (i := 8)
      (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := opkLen) (opkBs := opkBs)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m (by decide) hpanic hrej)
  rw [herrCommon]
  dsimp only [fsp, r1b_owned3_placed, r1b_mid7_placed] at hre4d0 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (runFsp s0 + 0x4d0#64) 9 ∗ ((runFsp s0 + 0x4d9#64) ↦₈ b4d9) ∗
      memRegion (runFsp s0 + 0x4da#64) 38) ∗
    (ownedBytes A opkCap opkPtr opkLen opkBs ∗
      ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
      ownedBytes A spkCap spkPtr spkLen spkBs ∗
      ownedBytes A regCap regPtr regLen regBs ∗
      errCommon ∗
      ((runFsp s0 + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
      ((runFsp s0 + 0x120#64) ↦₆₄ opkPtr) ∗ ((runFsp s0 + 0x128#64) ↦₆₄ kpkPtr) ∗
      ((runFsp s0 + 0x150#64) ↦₆₄ kpkCap) ∗ ((runFsp s0 + 0x158#64) ↦₆₄ speWord 8) ∗
      ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (runFsp s0 + 0x178#64) 8 ∗
      memRegion (runFsp s0 + 0x188#64) 16 ∗
      ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
      memRegion (runFsp s0 + 0x1a8#64) 16) by ac_rfl))
    (Entails.trans (sepConj_mono_left hre4d0) (Entails.of_eq (by ac_rfl)))

end CryptoVerification.SignalSession.Cli.RunCompose
