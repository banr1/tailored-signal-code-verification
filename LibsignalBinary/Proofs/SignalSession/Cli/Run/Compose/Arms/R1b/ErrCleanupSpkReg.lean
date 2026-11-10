/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

private theorem r1b_rejoin_188 (fsp regCap regPtr : BitVec 64) :
    memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
      ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ⊢
      memRegion (fsp + 0x188#64) 48 := by
  have h1a0 : ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ⊢
      memRegion (fsp + 0x1a0#64) 24 := by
    have ha : fsp + 0x1a8#64 = (fsp + 0x1a0#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cell64_cons regPtr (by decide)
  have h198 : ((fsp + 0x198#64) ↦₆₄ regCap) ∗ memRegion (fsp + 0x1a0#64) 24 ⊢
      memRegion (fsp + 0x198#64) 32 := by
    have ha : fsp + 0x1a0#64 = (fsp + 0x198#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cell64_cons regCap (by decide)
  have h188 : memRegion (fsp + 0x188#64) 16 ∗ memRegion (fsp + 0x198#64) 32 ⊢
      memRegion (fsp + 0x188#64) 48 := by
    have ha : fsp + 0x198#64 = (fsp + 0x188#64) + 16#64 := by bv_omega
    rw [ha, show (48 : Nat) = 16 + 32 from rfl,
      ProofLib.memRegion_split (fsp + 0x188#64) 16 32 (by decide)]
    exact Entails.refl _
  exact Entails.trans (sepConj_mono_right (Entails.trans (sepConj_mono_right h1a0) h198)) h188

private theorem r1b_rejoin_168 (fsp spkPtr spkCap : BitVec 64) :
    ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (fsp + 0x178#64) 8 ⊢ memRegion (fsp + 0x168#64) 24 := by
  have ha8 : fsp + 0x170#64 = (fsp + 0x168#64) + 8#64 := by bv_omega
  have ha16 : fsp + 0x178#64 = (fsp + 0x168#64) + 16#64 := by bv_omega
  rw [ha8, ha16]
  exact r1b_cells2_region8_to_24 (fsp + 0x168#64) spkPtr spkCap

def r1b_errLow4 (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
  memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16

theorem r1b_fold_low4 (fsp : BitVec 64) (R : SepProp) :
    memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
      memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗ R =
      r1b_errLow4 fsp ∗ R := by
  dsimp only [r1b_errLow4]; simp only [sepConj_assoc]

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2b78_cap0 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regPtr regLen : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2b78)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A 0#64 regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2b78 8
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2be8 8
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2bf0#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm2 hsm2 hinv_m2 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hc_m : r1b_ErrCtx img ext g d s0 sm2 0x2bf0 := {
    st := {
      pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm2, arm64_norm]
      run := by simp only [hsm2, arm64_norm, hrun]
      sp := by simpa only [hsm2, arm64_norm] using hsp
      fp := by simpa only [hsm2, arm64_norm] using hfp
      inv := hinv_m2
      vregs := by simpa only [calleeSavedVRegs, hsm2, arm64_norm] using hvregs
      spAligned := hsp0
    }
    x19 := by simpa only [hsm2, arm64_norm] using hc.x19
    x20 := by simpa only [hsm2, arm64_norm] using hc.x20
    x21 := by simpa only [hsm2, arm64_norm] using hc.x21
    trace := by simpa only [hsm2, arm64_norm] using hc.trace
    hist := ⟨by simpa only [hsm2, arm64_norm] using hc.hist.1,
      by simpa only [hsm2, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  have hsm_r12 : sm2.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by simp only [hsm2, arm64_norm]
  have hsm_r9 : sm2.readReg64 (.gpr 9#5) = ((s.readReg64 (.gpr 10#5)).truncate 32).zeroExtend 64 := by
    simp only [hsm2, arm64_norm]
  have hsm_r23 : sm2.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm2, arm64_norm]
  have hsm_r27 : sm2.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm2, arm64_norm]
  have hsm_r16 : sm2.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by simp only [hsm2, arm64_norm]
  have hsm_r14 : sm2.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by simp only [hsm2, arm64_norm]
  have hsm_r15 : sm2.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by simp only [hsm2, arm64_norm]
  have hsm_r28 : sm2.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm2, arm64_norm]
  have hsm_r22 : sm2.readReg64 (.gpr 22#5) = ((s.readReg64 (.gpr 2#5)).truncate 32).zeroExtend 64 := by
    simp only [hsm2, arm64_norm]
  refine MainHops.sepWPp_weaken_pre ?_ (r1b_cleanup_2bf0 hh hdrop hbnd hc_m hpanic hrej)
  rw [hsm_r12, hsm_r9, hsm_r23, hsm_r27, hsm_r16, hsm_r14, hsm_r15, hsm_r28, hsm_r22]
  dsimp only [r1b_errCommon]; rw [herrCore, r1b_fold_low4]
  dsimp only [fsp]
  have hdrop_reg : ownedBytes A 0#64 regPtr regLen regBs ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A (s.readReg64 (.gpr 12#5))
      (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
      (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
      (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
    (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (ownedBytes A 0#64 regPtr regLen regBs ∗ anyHeap)) ∗
    r1b_errLow4 (runFsp s0) ∗
    memRegion (runFsp s0 + 0x168#64) 24 ∗
    (memRegion (runFsp s0 + 0x188#64) 16 ∗ ((runFsp s0 + 0x198#64) ↦₆₄ 0#64) ∗
      ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (runFsp s0 + 0x1a8#64) 16) ∗
    memRegion (runFsp s0 + 0x4d0#64) 48 by ac_rfl)) ?_
  exact sepConj_mono r1b_SpePayload_zext_r9_r22
    (sepConj_mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hdrop_reg)))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (r1b_rejoin_188 (runFsp s0) 0#64 regPtr)))))

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2b78_capNe {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr regLen : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2b78)
    (hcap : regCap ≠ 0#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2b78 120
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hcap_f : (regCap == 0#64) = false := beq_false_of_ne hcap
  have hsplit168 : memRegion (fsp + 0x168#64) 24 =
      memRegion (fsp + 0x168#64) 16 ∗ ∃∗ v178 : BitVec 64, (fsp + 0x178#64) ↦₆₄ v178 := by
    rw [show (24 : Nat) = 16 + 8 from rfl, ProofLib.memRegion_split (fsp + 0x168#64) 16 8 (by decide),
      show fsp + 0x168#64 + 16#64 = fsp + 0x178#64 from by bv_omega, ProofLib.memRegion_eight]
  rw [hsplit168, sepExists_sepConj_right,
    r1b_region16_to_cells (fsp + 0x188#64), r1b_region16_to_cells (fsp + 0x1a8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v178 => SepWPp.exists_elim fun v188 =>
    SepWPp.exists_elim fun v190 => SepWPp.exists_elim fun v1a8 =>
    SepWPp.exists_elim fun v1b0 => ?_
  have ho190 : fsp + 0x188#64 + 8#64 = fsp + 0x190#64 := by bv_omega
  have ho1b0 : fsp + 0x1a8#64 + 8#64 = fsp + 0x1b0#64 := by bv_omega
  rw [ho190, ho1b0]
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run")) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hsm_run : sm.status = .Running := by simp only [hsm, arm64_norm, hrun]
  have hsm_sp0 : sm.sp = runFsp s0 := by simpa only [hsm, arm64_norm] using hsp
  have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
  have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
  have hsm_pc : sm.pc = (mProg img ext).fnAddr runName +
      bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run") := by
    dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
  have hsm_lr : sm.readReg64 .lr = runPc img ext 0x2bb8 := by
    dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
  have hsm_a0 : sm.readReg64 .x0 = regPtr := by simp only [hsm, arm64_norm]
  have hsm_a1 : sm.readReg64 .x1 = regCap := by simp only [hsm, arm64_norm]
  have hsm_a2 : sm.readReg64 .x2 = 1#64 := by simp only [hsm, arm64_norm]
  have hsm_x19 : sm.readReg64 (.gpr 19#5) = g.stores := by simpa only [hsm, arm64_norm] using hc.x19
  have hsm_x20 : sm.readReg64 (.gpr 20#5) = g.res := by simpa only [hsm, arm64_norm] using hc.x20
  have hsm_r21 : sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, arm64_norm]
  have hsm_r23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 14#5) := by simp only [hsm, arm64_norm]
  have hsm_r25 : sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 12#5) := by simp only [hsm, arm64_norm]
  have hsm_r26 : sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm, arm64_norm]
  have hsm_r27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 16#5) := by simp only [hsm, arm64_norm]
  have hsm_r28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 15#5) := by simp only [hsm, arm64_norm]
  have hsm_fs : sm.fs = s.fs := by simp only [hsm, arm64_norm]
  have hsm_tr : sm.trace = s.trace := by simp only [hsm, arm64_norm]
  clear hsm
  rw [← hfsp_eq]
  refine MainHops.sepWPp_weaken_pre (P' :=
      ownedBytes A regCap regPtr regLen regBs ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        errCore ∗ anyHeap ∗ r1b_errLow4 (runFsp s0) ∗
        memRegion (runFsp s0 + 0x168#64) 16 ∗ ((runFsp s0 + 0x178#64) ↦₆₄ s.readReg64 (.gpr 10#5)) ∗
        ((runFsp s0 + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗ ((runFsp s0 + 0x190#64) ↦₆₄ v1a8) ∗
        ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
        ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48)) ?_ ?_
  · exact Entails.of_eq (by ac_rfl)
  refine r1b_call_dealloc_ownedBytes (Q := Q) (cap := regCap) (ptr := regPtr) (len := regLen) (bs := regBs)
    hh hbnd hinv_m hsm_pc hsm_run
    hsm_sp0 hsm_fp hsm_vr hsp0 hsm_lr
    hsm_a0 hsm_a1 hsm_a2
    hcap hpanic ?_
  intro s1 hin1 hcs1 hfs1 htr1
  rw [hfsp_eq]
  have hpc1 := hin1.pc; have hrun1 := hin1.run
  have hsp1 : s1.sp = fsp := hin1.sp
  have hfp1 := hin1.fp; have hinv1 := hin1.inv; have hvregs1 := hin1.vregs
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
  rw [heq_fnBase] at hpc1
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2bf0#64) hinv1
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  rcases hcs1 with ⟨hc19, hc20, hc21, hc22, hc24, hc25, hc26, hc27, hc28, hc29, _, _⟩
  have htr2 : sm2.trace = s.trace := by simp only [hsm2, arm64_norm]; exact htr1.trans hsm_tr
  have hfs2 : sm2.fs = s.fs := by simp only [hsm2, arm64_norm]; exact hfs1.trans hsm_fs
  have hc_m2 : r1b_ErrCtx img ext g d s0 sm2 0x2bf0 := {
    st := {
      pc := by
        dsimp only [runPc, mProg, tripleRatchetProgAtExt]
        rw [heq_fnBase]; simp only [hsm2, arm64_norm]
      run := by simp only [hsm2, arm64_norm, hrun1]
      sp := by simpa only [hsm2, arm64_norm] using hin1.sp
      fp := by simpa only [hsm2, arm64_norm] using hfp1
      inv := hinv2
      vregs := by simpa only [calleeSavedVRegs, hsm2, arm64_norm] using hvregs1
      spAligned := hsp0
    }
    x19 := by simp only [hsm2, arm64_norm, hc19, hsm_x19]
    x20 := by simp only [hsm2, arm64_norm, hc20, hsm_x20]
    x21 := by simp only [hsm2, arm64_norm]; exact hc.x21
    trace := htr2 ▸ hc.trace
    hist := ⟨by rw [hfs2]; exact hc.hist.1, by rw [htr2]; exact hc.hist.2⟩
    ans := hc.ans
  }
  have hr12 : sm2.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by
    simp only [hsm2, arm64_norm, hc26, hsm_r25]
  have hr9 : sm2.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 10#5) := by simp only [hsm2, arm64_norm]
  have hr23 : sm2.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm2, arm64_norm]
  have hr27 : sm2.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
    simp only [hsm2, arm64_norm, hc21, hsm_r21]
  have hr16 : sm2.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
    simp only [hsm2, arm64_norm, hc28, hsm_r27]
  have hr14 : sm2.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
    simp only [hsm2, arm64_norm, hc24, hsm_r23]
  have hr15 : sm2.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
    simp only [hsm2, arm64_norm, hc29, hsm_r28]
  have hr28 : sm2.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
    simp only [hsm2, arm64_norm, hc27, hsm_r26]
  have hr22 : sm2.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 2#5) := by simp only [hsm2, arm64_norm]
  clear hsm2
  have hre168 : memRegion (fsp + 0x168#64) 16 ∗ ((fsp + 0x178#64) ↦₆₄ s.readReg64 (.gpr 10#5)) ⊢
      memRegion (fsp + 0x168#64) 24 := by
    rw [show (24 : Nat) = 16 + 8 from rfl, ProofLib.memRegion_split (fsp + 0x168#64) 16 8 (by decide),
      show fsp + 0x168#64 + 16#64 = fsp + 0x178#64 from by bv_omega]
    exact sepConj_mono_right (pointsTo64_entails_memRegion _ _)
  have hre188 : ((fsp + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗ ((fsp + 0x190#64) ↦₆₄ v1a8) ∗
      ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
      ((fsp + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
      ((fsp + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ⊢ memRegion (fsp + 0x188#64) 48 := by
    have ha1 : fsp + 0x190#64 = (fsp + 0x188#64) + 8#64 := by bv_omega
    have ha2 : fsp + 0x1b0#64 = (fsp + 0x1a8#64) + 8#64 := by bv_omega
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗ ((fsp + 0x190#64) ↦₆₄ v1a8)) ∗
      ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
      (((fsp + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
        ((fsp + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5))) by ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (by rw [ha1]; exact r1b_cells2_to_region16 _ _ _)
        (sepConj_mono_right (sepConj_mono_right
          (by rw [ha2]; exact r1b_cells2_to_region16 _ _ _))))
      (r1b_rejoin_188 fsp regCap regPtr)
  refine MainHops.sepWPp_weaken_pre ?_ (r1b_cleanup_2bf0 hh hdrop hbnd hc_m2 hpanic hrej)
  rw [hr12, hr9, hr23, hr27, hr16, hr14, hr15, hr28, hr22]
  dsimp only [r1b_errCommon]; rw [herrCore, r1b_fold_low4]
  dsimp only [fsp] at hre168 hre188 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A (s.readReg64 (.gpr 12#5))
      (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
      (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
      (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
    (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) ∗
    r1b_errLow4 (runFsp s0) ∗
    (memRegion (runFsp s0 + 0x168#64) 16 ∗ ((runFsp s0 + 0x178#64) ↦₆₄ s.readReg64 (.gpr 10#5))) ∗
    (((runFsp s0 + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗ ((runFsp s0 + 0x190#64) ↦₆₄ v1a8) ∗
      ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
      ((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
      ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5))) ∗
    memRegion (runFsp s0 + 0x4d0#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hre168 (sepConj_mono_left hre188))))

theorem r1b_cleanup_2b78 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr regLen : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2b78)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  by_cases hcap : regCap = 0#64
  · subst hcap; exact r1b_cleanup_2b78_cap0 hh hdrop hbnd hc hpanic hrej
  · exact r1b_cleanup_2b78_capNe hh hdrop hbnd hc hcap hpanic hrej

private theorem r1b_cleanup_2b28_cap0 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2b28)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A 0#64 spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ 0#64) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2b28 8
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2b78#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2b78 := {
    st := {
      pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
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
  have hr2 : sm.readReg64 (.gpr 2#5) = s.readReg64 (.gpr 2#5) := by simp only [hsm, arm64_norm]
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2b78 (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej)
  rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28, hr2]
  dsimp only [r1b_errCommon]; rw [herrCore, r1b_fold_low4]
  dsimp only [fsp]
  have hdrop_spk : ownedBytes A 0#64 spkPtr spkLen spkBs ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A (s.readReg64 (.gpr 12#5))
      (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
      (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
      (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
    ownedBytes A regCap regPtr regLen regBs ∗
    (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (ownedBytes A 0#64 spkPtr spkLen spkBs ∗ anyHeap)) ∗
    r1b_errLow4 (runFsp s0) ∗
    (((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ 0#64) ∗
      memRegion (runFsp s0 + 0x178#64) 8) ∗
    memRegion (runFsp s0 + 0x188#64) 16 ∗ ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗
    ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (runFsp s0 + 0x1a8#64) 16 ∗
    memRegion (runFsp s0 + 0x4d0#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hdrop_spk)))
      (sepConj_mono_right (sepConj_mono_left (r1b_rejoin_168 (runFsp s0) spkPtr 0#64)))))

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2b28_capNe {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2b28)
    (hcap : spkCap ≠ 0#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2b28 80
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hcap_f : (spkCap == 0#64) = false := beq_false_of_ne hcap
  rw [r1b_region16_to_cells (fsp + 0x188#64), r1b_region16_to_cells (fsp + 0x1a8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v188 => SepWPp.exists_elim fun v190 =>
    SepWPp.exists_elim fun v1a8 => SepWPp.exists_elim fun v1b0 => ?_
  have ho190 : fsp + 0x188#64 + 8#64 = fsp + 0x190#64 := by bv_omega
  have ho1b0 : fsp + 0x1a8#64 + 8#64 = fsp + 0x1b0#64 := by bv_omega
  rw [ho1b0]; rw [ho190]
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run")) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hsm_run : sm.status = .Running := by simp only [hsm, arm64_norm, hrun]
  have hsm_sp0 : sm.sp = runFsp s0 := by simpa only [hsm, arm64_norm] using hc.st.sp
  have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
  have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
  have hsm_pc : sm.pc = (mProg img ext).fnAddr runName +
      bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run") := by
    dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
  have hsm_lr : sm.readReg64 .lr = runPc img ext 0x2b58 := by
    dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
  have hsm_a0 : sm.readReg64 .x0 = spkPtr := by simp only [hsm, arm64_norm]
  have hsm_a1 : sm.readReg64 .x1 = spkCap := by simp only [hsm, arm64_norm]
  have hsm_a2 : sm.readReg64 .x2 = 1#64 := by simp only [hsm, arm64_norm]
  have hsm_x19 : sm.readReg64 (.gpr 19#5) = g.stores := by simpa only [hsm, arm64_norm] using hc.x19
  have hsm_x20 : sm.readReg64 (.gpr 20#5) = g.res := by simpa only [hsm, arm64_norm] using hc.x20
  have hsm_x21 : sm.readReg64 (.gpr 21#5) = d.meG.name.cap := by simpa only [hsm, arm64_norm] using hc.x21
  have hsm_r22 : sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 10#5) := by simp only [hsm, arm64_norm]
  have hsm_r23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 14#5) := by simp only [hsm, arm64_norm]
  have hsm_r25 : sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 12#5) := by simp only [hsm, arm64_norm]
  have hsm_r26 : sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 16#5) := by simp only [hsm, arm64_norm]
  have hsm_r27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp only [hsm, arm64_norm]
  have hsm_r28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 15#5) := by simp only [hsm, arm64_norm]
  have hsm_fs : sm.fs = s.fs := by simp only [hsm, arm64_norm]
  have hsm_tr : sm.trace = s.trace := by simp only [hsm, arm64_norm]
  clear hsm
  rw [← hfsp_eq]
  refine MainHops.sepWPp_weaken_pre (P' :=
      ownedBytes A spkCap spkPtr spkLen spkBs ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        errCore ∗ anyHeap ∗ r1b_errLow4 (runFsp s0) ∗
        ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (runFsp s0 + 0x178#64) 8 ∗
        ((runFsp s0 + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗
        ((runFsp s0 + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ∗
        ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
        ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48)) ?_ ?_
  · exact Entails.of_eq (by ac_rfl)
  refine r1b_call_dealloc_ownedBytes (Q := Q) (cap := spkCap) (ptr := spkPtr) (len := spkLen) (bs := spkBs)
    hh hbnd hinv_m hsm_pc hsm_run
    hsm_sp0 hsm_fp hsm_vr hsp0 hsm_lr
    hsm_a0 hsm_a1 hsm_a2
    hcap hpanic ?_
  intro s1 hin1 hcs1 hfs1 htr1
  rw [hfsp_eq]
  have hpc1 := hin1.pc; have hrun1 := hin1.run
  have hsp1 : s1.sp = fsp := hin1.sp
  have hfp1 := hin1.fp; have hinv1 := hin1.inv; have hvregs1 := hin1.vregs
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
  rw [heq_fnBase] at hpc1
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2b78#64) hinv1
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  rcases hcs1 with ⟨hc19, hc20, hc21, hc22, hc24, hc25, hc26, hc27, hc28, hc29, _, _⟩
  have htr2 : sm2.trace = s.trace := by simp only [hsm2, arm64_norm]; exact htr1.trans hsm_tr
  have hfs2 : sm2.fs = s.fs := by simp only [hsm2, arm64_norm]; exact hfs1.trans hsm_fs
  have hc_m2 : r1b_ErrCtx img ext g d s0 sm2 0x2b78 := {
    st := {
      pc := by
        dsimp only [runPc, mProg, tripleRatchetProgAtExt]
        rw [heq_fnBase]; simp only [hsm2, arm64_norm]
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
    simp only [hsm2, arm64_norm, hc22, hsm_r22]
  have hr23 : sm2.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by simp only [hsm2, arm64_norm]
  have hr27 : sm2.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
    simp only [hsm2, arm64_norm, hc28, hsm_r27]
  have hr16 : sm2.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
    simp only [hsm2, arm64_norm, hc27, hsm_r26]
  have hr14 : sm2.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
    simp only [hsm2, arm64_norm, hc24, hsm_r23]
  have hr15 : sm2.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
    simp only [hsm2, arm64_norm, hc29, hsm_r28]
  have hr28 : sm2.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp only [hsm2, arm64_norm]
  have hr2 : sm2.readReg64 (.gpr 2#5) = s.readReg64 (.gpr 2#5) := by simp only [hsm2, arm64_norm]
  clear hsm2
  have hre188 : ((fsp + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗
      ((fsp + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ⊢ memRegion (fsp + 0x188#64) 16 := by
    have ha1 : fsp + 0x190#64 = (fsp + 0x188#64) + 8#64 := by bv_omega
    rw [ha1]; exact r1b_cells2_to_region16 _ _ _
  have hre1a8 : ((fsp + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
      ((fsp + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ⊢ memRegion (fsp + 0x1a8#64) 16 := by
    have ha2 : fsp + 0x1b0#64 = (fsp + 0x1a8#64) + 8#64 := by bv_omega
    rw [ha2]; exact r1b_cells2_to_region16 _ _ _
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2b78 (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m2 hpanic hrej)
  rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28, hr2]
  dsimp only [r1b_errCommon]; rw [herrCore, r1b_fold_low4]
  dsimp only [fsp] at hre188 hre1a8 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A (s.readReg64 (.gpr 12#5))
      (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
      (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
      (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
    ownedBytes A regCap regPtr regLen regBs ∗
    (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) ∗
    r1b_errLow4 (runFsp s0) ∗
    (((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (runFsp s0 + 0x178#64) 8) ∗
    (((runFsp s0 + 0x188#64) ↦₆₄ s.readReg64 (.gpr 2#5)) ∗
      ((runFsp s0 + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5))) ∗
    ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
    (((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
      ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5))) ∗
    memRegion (runFsp s0 + 0x4d0#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (r1b_rejoin_168 (runFsp s0) spkPtr spkCap)
      (sepConj_mono hre188
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hre1a8))))))))

theorem r1b_cleanup_2b28 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2b28)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 2#5)) ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  by_cases hcap : spkCap = 0#64
  · subst hcap; exact r1b_cleanup_2b28_cap0 hh hdrop hbnd hc hpanic hrej
  · exact r1b_cleanup_2b28_capNe hh hdrop hbnd hc hcap hpanic hrej

theorem r1b_cleanup_2b24 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2b24)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
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
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  rw [r1b_fold_low4]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2b24 4
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2b28#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2b28 := {
    st := {
      pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
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
  have hr2 : sm.readReg64 (.gpr 2#5) = v188 := by simp only [hsm, arm64_norm]
  have hre : ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ⊢
      memRegion (fsp + 0x188#64) 16 := by
    have ha : fsp + 0x190#64 = (fsp + 0x188#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cell64_cons v188 (by decide)
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2b28 (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej)
  rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28, hr2, herrCommon, r1b_fold_low4]
  dsimp only [fsp] at hre ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    r1b_SpePayload A (s.readReg64 (.gpr 12#5))
      (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
      (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
      (s.readReg64 (.gpr 28#5)) v188 ∗
    ownedBytes A spkCap spkPtr spkLen spkBs ∗
    ownedBytes A regCap regPtr regLen regBs ∗
    errCommon ∗
    r1b_errLow4 (runFsp s0) ∗
    ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
    memRegion (runFsp s0 + 0x178#64) 8 ∗
    (((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗ memRegion (runFsp s0 + 0x190#64) 8) ∗
    ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
    memRegion (runFsp s0 + 0x1a8#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hre))))))))

end CryptoVerification.SignalSession.Cli.RunCompose
