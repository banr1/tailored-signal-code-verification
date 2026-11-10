/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpk
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import all Init.Data.String.Defs

/-!
# Relocatable Stage 2 (`kyber-pre-key` Read and `split_signed`) of Arm `R1b`

Relocatable (`[LibsignalPlacement]`) counterparts of `R1b.ReadKpk` (`0x1260 → 0x12dc`) on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
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
theorem r1b_err_1aa8_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr spkCap spkPtr regCap regPtr : BitVec 64}
    {eBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1aa8)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx9 : s.readReg64 (.gpr 9#5) = eCap)
    (hx26 : s.readReg64 (.gpr 26#5) = ePtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 eBs.length)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx12; let _ := hx9; let _ := hx26; let _ := hx2
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hsplit16 := r1b_region16_to_cells (fsp + 0x4f0#64)
  have h4f8 : (fsp + 0x4f0#64) + 8#64 = fsp + 0x4f8#64 := by bv_omega
  rw [h4f8] at hsplit16
  rw [hsplit16]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 0x1aa8#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2b28) hst.inv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b28 := hc.of_step
    { pc := by simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hst.run]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hst.fp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
      spAligned := hst.spAligned }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  have h4d0 :
      ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord 1) eCap ePtr
        (BitVec.ofNat 64 eBs.length) w4 w5
  have hpay : ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (sm.readReg64 (.gpr 2#5)) := by
    simp only [hsm, arm64_norm]
    try rw [hx12]
    try rw [hx2]
    r1b_prove_spe_str
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2b28_placed (spkCap := spkCap) (spkPtr := spkPtr)
      (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej)
  rw [herrCommon]
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono hpay h4d0) (by r1b_ac)
theorem r1b_err_1b60_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr kpkCap kpkPtr spkCap spkPtr regCap regPtr v188_in : BitVec 64}
    {eBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1b60)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx10 : s.readReg64 (.gpr 10#5) = eCap)
    (hx9 : s.readReg64 (.gpr 9#5) = ePtr)
    (hx23 : s.readReg64 (.gpr 23#5) = ((BitVec.ofNat 64 eBs.length).truncate 32).zeroExtend 64)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx12; let _ := hx10; let _ := hx9; let _ := hx23; let _ := hx26
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hsplit16 := r1b_region16_to_cells (fsp + 0x4f0#64)
  have h4f8 : (fsp + 0x4f0#64) + 8#64 = fsp + 0x4f8#64 := by bv_omega
  rw [h4f8] at hsplit16
  have he8 : ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) =
      ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
        ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) := by
    have hz := r1b_u64_split32 (fsp + 0x4e8#64) (BitVec.ofNat 64 eBs.length)
    have ha : (fsp + 0x4e8#64) + 4#64 = fsp + 0x4ec#64 := by bv_omega
    rwa [ha] at hz
  rw [he8, hsplit16]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 0x1b60#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2adc) hst.inv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := hc.of_step
    { pc := by simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hst.run]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hst.fp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
      spAligned := hst.spAligned }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  have h4d0 :
      ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        (((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
          ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32)) ∗
        ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
    rw [← he8]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord 1) eCap ePtr
        (BitVec.ofNat 64 eBs.length) w4 w5
  have h150 : ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ⊢
      memRegion (fsp + 0x150#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cell64_cons (a := fsp + 0x150#64) kpkCap (n := 8) (by decide)
  have hpay : ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (sm.readReg64 (.gpr 9#5)) := by
    simp only [hsm, arm64_norm]
    try rw [hx12]
    try rw [hx10]
    r1b_prove_spe_str
  rw [show ((fsp + 0x188#64) ↦₆₄ ((BitVec.ofNat 64 eBs.length).truncate 32).zeroExtend 64) =
    ((fsp + 0x188#64) ↦₆₄ sm.readReg64 (.gpr 9#5)) by
    simp only [hsm, arm64_norm]]
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2adc_placed (v188 := sm.readReg64 (.gpr 9#5))
      (kpkCap := kpkCap) (kpkPtr := kpkPtr)
      (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr)
      (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
      hh hdrop hbnd hc_m
      (by simp [hsm, arm64_norm])
      (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx26)
      hpanic hrej)
  rw [herrCommon]
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono hpay (sepConj_mono h4d0 h150)) (by r1b_ac)
private theorem r1b_utf8_kpk_len_placed : (utf8 "kyber-pre-key").length = 13 := by
  rfl_kernel

set_option maxHeartbeats 600000 in
theorem r1b_step_kpk_placed [LibsignalPlacement] {S : RunSem} {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {regCap regPtr spkCap spkPtr : BitVec 64}
    {spkBs spkKey spkSig : List (BitVec 8)} {spkId : BitVec 32}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hc : RunCalleesPlaced A H B σ)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1b_CodeOk S g s0)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x1260)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hspk_sp : splitSigned spkBs = some (spkId, spkKey, spkSig))
    (hx10 : s.readReg64 (.gpr 10#5) = spkPtr + 4#64)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length)
    (hx2 : s.readReg64 .x2 = spkId.zeroExtend 64)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp)
    (hk : ∀ (sf : State) (kpkCap kpkPtr : BitVec 64)
        (kpkBs kpkKey kpkSig : List (BitVec 8)) (kpkId : BitVec 32),
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x12dc →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs →
      splitSigned kpkBs = some (kpkId, kpkKey, kpkSig) →
      sf.readReg64 (.gpr 25#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      sf.readReg64 (.gpr 26#5) = kpkPtr →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 (.gpr 9#5) = BitVec.ofNat 64 kpkKey.length →
      sf.readReg64 (.gpr 10#5) = kpkPtr + 4#64 →
      sf.readReg64 (.gpr 8#5) = kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗
          memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 24 ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
        ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
        memRegion (fsp + 0x4d0#64) 32 ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCore_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hreg_rd; let _ := hspk_rd; let _ := hspk_sp
  let _ := hx10; let _ := hx27; let _ := hx2; let _ := hx26; let _ := hx28
  generalize hinvCore : r1b_invCore_placed A g d s0 = invCore at *
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have ⟨hdir32, hpaths⟩ := r1b_init_path_facts_placed he hok.callEq
  have ⟨hkpk_ok, _⟩ := hpaths "kyber-pre-key" (by simp [bundleNames])
  have hdir_nat : (BitVec.ofNat 64 d.dir.length).toNat = d.dir.length := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [r1b_split_region fsp 0x150 8 8,
    ProofLib.memRegion_eight (fsp + 0x158#64),
    ProofLib.memRegion_eight (fsp + 0x178#64),
    ProofLib.memRegion_eight (fsp + 0x188#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v158 => SepWPp.exists_elim fun v178 =>
    SepWPp.exists_elim fun v188 => ?_
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 0x1260#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 563) hst.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have h4d0_48 :
      memRegion (fsp + 0x4d0#64) 32 ∗
        ((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
        ((fsp + 0x4f8#64) ↦₆₄ 64#64) ⊢ memRegion (fsp + 0x4d0#64) 48 := by
    refine Entails.trans (sepConj_mono_right (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cells2_to_region16 (fsp + 0x4f0#64)
          (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length) 64#64)) ?_
    rw [r1b_join_region fsp 0x4d0 32 16]; exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) h4d0_48 (by r1b_ac) ?_
  refine r1b_call_frame <|
    r1b_call_bundleRead_ro_placed (ret := fsp + 0x4d0#64) (dirCap := d.dirCap) (dirPtr := d.dirPtr) (dir := d.dir)
      hh hc hbnd hinv1 r1b_ro_kpk_placed
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run])
      (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x1294)
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp only [hsm1, arm64_norm]; exact hdir_nat)
      (by simp only [hsm1, arm64_norm]; rfl)
      (by simp [hsm1, arm64_norm, r1b_utf8_kpk_len_placed])
      hdir32 (by rw [r1b_utf8_kpk_len_placed]; decide) hkpk_ok
      (by simpa [hsm1, arm64_norm] using hok.trace) hpanic
      (fun sf1 eCap ePtr eBs hin1 hcs1 hout1 => ?_)
      (fun sf1 kpkCap kpkPtr kpkBs hin1 hcs1 hkpk_rd_sf hfs1 htr1 => ?_)
  · have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x1294 :=
      hok.after_readErr
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        hin1 hcs1 hout1 r1b_none_kpk_rd
    try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
    try rw [← BitVec.add_assoc spkPtr 4#64]
    dsimp only [speWord]
    have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 0x1294#64 at hpc
    have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x1aa8) hin1.inv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    try rw [← BitVec.add_assoc spkPtr 4#64]
    have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x1aa8 := hc1.of_step
      { pc := by simp [hsm2, arm64_norm]
        run := by simp [hsm2, arm64_norm, hin1.run]
        sp := by simpa [hsm2, arm64_norm] using hin1.sp
        fp := by simpa [hsm2, arm64_norm] using hin1.fp
        inv := hinv2
        vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs
        spAligned := hst.spAligned }
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm])
    try rw [hx10]
    try rw [show s.readReg64 (.gpr 2#5) = spkId.zeroExtend 64 from hx2]
    try rw [hx2]
    have h150 :
        memRegion (fsp + 0x150#64) 8 ∗
          ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ⊢
          memRegion (fsp + 0x150#64) 16 := by
      refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
      rw [r1b_join_region fsp 0x150 8 8]; exact Entails.refl _
    have h178 : ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ⊢ memRegion (fsp + 0x178#64) 8 :=
      pointsTo64_entails_memRegion _ _
    generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
    have hst_err :
        invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ⊢
          errCommon ∗ memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
      rw [← hinvCore, ← herrCommon]
      exact r1b_stage_to_err_placed A g d s0 resStack (ofLe32 r0 r1 r2 r3)
    have h188 : ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ memRegion (fsp + 0x190#64) 8 ⊢
        memRegion (fsp + 0x188#64) 16 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x188#64) (spkId.zeroExtend 64) (n := 8) (by decide)
    have hex :
        (((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗
          (invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
            memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
            ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
            ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
            ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
            ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
            memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool)) ⊢
          errCommon ∗
            memRegion (fsp + 0x188#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16 :=
      Entails.trans (sepConj_mono_right hst_err)
        (r1b_entails_frame (by r1b_ac) h188 (by r1b_ac))
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_1aa8_placed (eCap := eCap) (ePtr := ePtr) (eBs := eBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
        hh hdrop hbnd hc2
        (by simp [hsm2, arm64_norm, speWord])
        (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm])
        hpanic hrej)
    rw [herrCommon]
    exact r1b_entails_frame (by r1b_ac) (sepConj_mono h150 (sepConj_mono h178 hex)) (by r1b_ac)
  · have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x1294 := hok.after_call
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      hin1 hcs1 hfs1 htr1
    have hkpk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") =
        .ok kpkBs := by
      rwa [← hok.fs, ← show sm1.fs.files = s.fs.files by simp [hsm1, arm64_norm]]
    have hx23_1 : sf1.readReg64 (.gpr 23#5) = 64#64 :=
      hcs1.2.2.2.2.1.trans (by simp [hsm1, arm64_norm])
    have hx25_1 : sf1.readReg64 (.gpr 25#5) = d.dirPtr :=
      hcs1.2.2.2.2.2.2.1.trans (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx26)
    have hx27_1 : sf1.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length :=
      hcs1.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx27)
    have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx28)
    rw [r1b_split_region fsp 0x130 24 8,
      ProofLib.memRegion_eight (fsp + 0x148#64),
      ProofLib.memRegion_eight (fsp + 0x150#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    try rw [← BitVec.add_assoc spkPtr 4#64]
    refine SepWPp.exists_elim fun v148 => SepWPp.exists_elim fun v150 =>
      r1b_call_frame <| r1b_sepWPp_borrow_core A (cap := kpkCap) (ptr := kpkPtr)
        (len := BitVec.ofNat 64 kpkBs.length) (bs := kpkBs)
        fun ⟨_, hkpk_le, hkpk_lt, hkpk_ne⟩ => ?_
    have hkpk_nat : (BitVec.ofNat 64 kpkBs.length).toNat = kpkBs.length := by
      simp only [BitVec.toNat_ofNat]; omega
    dsimp only [okTagVec]
    have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 0x1294#64 at hpc
    have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 592) hin1.inv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have h4d0_48 :
        ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((fsp + 0x4d8#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x4e0#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 kpkBs.length) ∗
          memRegion (fsp + 0x4f0#64) 16 ⊢ memRegion (fsp + 0x4d0#64) 48 := by
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4e8#64) (BitVec.ofNat 64 kpkBs.length) (n := 16) (by decide))))) ?_
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4e0#64) kpkPtr (n := 24) (by decide)))) ?_
      refine Entails.trans (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4d8#64) kpkCap (n := 32) (by decide))) ?_
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 40) (by decide)
    refine r1b_sepWPp_frame (by r1b_ac) h4d0_48 (by r1b_ac) ?_
    refine r1b_call_frame <|
      r1b_call_splitSigned_placed hh hc hbnd hinv2
        (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm, hin1.run])
        (by simpa [hsm2, arm64_norm] using hin1.sp)
        (by simpa [hsm2, arm64_norm] using hin1.fp)
        (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
        hst.spAligned (retOff := 0x12bc)
        (by simp [hsm2, arm64_norm])
        (ret := fsp + 0x4d0#64) (fp := kpkPtr) (file := kpkBs)
        (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using congrArg (· + 0x4d0#64) hin1.sp)
        (by simp [hsm2, arm64_norm])
        (by simp only [hsm2, arm64_norm]; exact hkpk_nat)
        (by simpa [hsm2, arm64_norm] using hok1.trace) hpanic
        (fun sf2 eCap ePtr eBs hin2 hcs2 hsp_none hfs2 htr2 => ?_)
        (fun sf2 kpkId kpkKey kpkSig hin2 hcs2 hsp_ok hfs2 htr2 => ?_)
    · have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf2 0x12bc := hok1.after_call
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        hin2 hcs2 hfs2 htr2
      have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x12bc :=
        hok2.to_err (r1b_none_kpk_split hkpk_rd hsp_none)
      have hx26_2 : sf2.readReg64 (.gpr 26#5) = kpkPtr :=
        hcs2.2.2.2.2.2.2.2.1.trans (by simp [hsm2, arm64_norm])
      have hrejoin := r1b_ownedBytes_rejoin A kpkCap kpkPtr kpkBs hkpk_le hkpk_lt hkpk_ne
      refine r1b_sepWPp_frame (by r1b_ac) hrejoin (by r1b_ac) ?_
      have he8 : ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) =
          ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
            ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) := by
        have hz := r1b_u64_split32 (fsp + 0x4e8#64) (BitVec.ofNat 64 eBs.length)
        have ha : (fsp + 0x4e8#64) + 4#64 = fsp + 0x4ec#64 := by bv_omega
        rwa [ha] at hz
      try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
      try rw [← BitVec.add_assoc spkPtr 4#64]
      rw [he8]
      try simp only [sepConj_assoc]
      dsimp only [speWord]
      have hpc := hin2.pc; change sf2.pc = (blkPl_579).base + 0x12bc#64 at hpc
      have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x1b60) hin2.inv
      rw [runPcPlaced_eq]
      (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      try rw [← BitVec.add_assoc spkPtr 4#64]
      have hc3 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm3 0x1b60 := hc2.of_step
        { pc := by simp [hsm3, arm64_norm]
          run := by simp [hsm3, arm64_norm, hin2.run]
          sp := by simpa [hsm3, arm64_norm] using hin2.sp
          fp := by simpa [hsm3, arm64_norm] using hin2.fp
          inv := hinv3
          vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs
          spAligned := hst.spAligned }
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm])
      try rw [hx23_1]
      try rw [hx10]
      try rw [show s.readReg64 (.gpr 2#5) = spkId.zeroExtend 64 from hx2]
      try rw [hx2]
      have he8' : ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
          ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) ⊢
          ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) := by
        rw [← he8]; exact Entails.refl _
      have h130 :
          memRegion (fsp + 0x130#64) 24 ∗ ((fsp + 0x148#64) ↦₆₄ 64#64) ⊢
            memRegion (fsp + 0x130#64) 0x20 := by
        refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
        rw [r1b_join_region fsp 0x130 24 8]; exact Entails.refl _
      have h158 :
          ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ⊢
            memRegion (fsp + 0x158#64) 8 :=
        pointsTo64_entails_memRegion _ _
      have h178 : ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ⊢
          memRegion (fsp + 0x178#64) 8 :=
        pointsTo64_entails_memRegion _ _
      refine r1b_sepWPp_frame (by r1b_ac)
        (sepConj_mono he8' (sepConj_mono h130 (sepConj_mono h158 h178)))
        (by r1b_ac) ?_
      generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
      have hst_err :
          invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
            memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
            ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
            ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
            ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
            ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
            memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ⊢
            errCommon ∗ memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
        rw [← hinvCore, ← herrCommon]
        exact r1b_stage_to_err_placed A g d s0 resStack (ofLe32 r0 r1 r2 r3)
      refine MainHops.sepWPp_weaken_pre ?_
        (r1b_err_1b60_placed (v188_in := spkId.zeroExtend 64) (eCap := eCap) (ePtr := ePtr) (eBs := eBs)
          (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkBs := kpkBs)
          (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
          (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
          hh hdrop hbnd hc3
          (by simp [hsm3, arm64_norm, speWord])
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm])
          (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx26_2)
          hpanic hrej)
      rw [herrCommon]
      exact r1b_entails_frame (by r1b_ac) hst_err (by r1b_ac)
    · have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf2 0x12bc := hok1.after_call
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        hin2 hcs2 hfs2 htr2
      have hx25_2 : sf2.readReg64 (.gpr 25#5) = d.dirPtr :=
        hcs2.2.2.2.2.2.2.1.trans (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx25_1)
      have hx26_2 : sf2.readReg64 (.gpr 26#5) = kpkPtr :=
        hcs2.2.2.2.2.2.2.2.1.trans (by simp [hsm2, arm64_norm])
      have hx27_2 : sf2.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length :=
        hcs2.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx27_1)
      have hx28_2 : sf2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
        hcs2.2.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx28_1)
      have hrejoin := r1b_ownedBytes_rejoin A kpkCap kpkPtr kpkBs hkpk_le hkpk_lt hkpk_ne
      refine r1b_sepWPp_frame (by r1b_ac) hrejoin (by r1b_ac) ?_
      try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
      try rw [← BitVec.add_assoc spkPtr 4#64]; try rw [← BitVec.add_assoc kpkPtr 4#64]
      dsimp only [splitOkTag]
      have hpc := hin2.pc; change sf2.pc = (blkPl_579).base + 0x12bc#64 at hpc
      have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x12dc) hin2.inv
      rw [runPcPlaced_eq]
      (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      try rw [← BitVec.add_assoc spkPtr 4#64]; try rw [← BitVec.add_assoc kpkPtr 4#64]
      have hok3 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm3 0x12dc := hok2.of_step
        { pc := by simp [hsm3, arm64_norm]
          run := by simp [hsm3, arm64_norm, hin2.run]
          sp := by simpa [hsm3, arm64_norm] using hin2.sp
          fp := by simpa [hsm3, arm64_norm] using hin2.fp
          inv := hinv3
          vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs
          spAligned := hst.spAligned }
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
      try rw [hx23_1]
      try rw [hx10]
      try rw [show s.readReg64 (.gpr 2#5) = spkId.zeroExtend 64 from hx2]
      try rw [hx2]
      have h4d0_48 :
          ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
            ((fsp + 0x4d8#64) ↦₆₄ (kpkPtr + 4#64)) ∗
            ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
            ((fsp + 0x4e8#64) ↦₃₂ kpkId) ∗
            memRegion (fsp + 0x4ec#64) 4 ∗
            ((fsp + 0x4f0#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
            ((fsp + 0x4f8#64) ↦₆₄ 64#64) ⊢ memRegion (fsp + 0x4d0#64) 48 := by
        have h4d0_32 :
            ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
              ((fsp + 0x4d8#64) ↦₆₄ (kpkPtr + 4#64)) ∗
              ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
              (((fsp + 0x4e8#64) ↦₃₂ kpkId) ∗ memRegion (fsp + 0x4ec#64) 4) ⊢
              memRegion (fsp + 0x4d0#64) 32 := by
          refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))) ?_
          rw [r1b_join_region fsp 0x4e8 4 4]
          refine Entails.trans (sepConj_mono_right (sepConj_mono_right (by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cell64_cons (a := fsp + 0x4e0#64) (BitVec.ofNat 64 kpkKey.length) (n := 8) (by decide)))) ?_
          refine Entails.trans (sepConj_mono_right (by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cell64_cons (a := fsp + 0x4d8#64) (kpkPtr + 4#64) (n := 16) (by decide))) ?_
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 24) (by decide)
        have h4f0_16 :
            ((fsp + 0x4f0#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
              ((fsp + 0x4f8#64) ↦₆₄ 64#64) ⊢ memRegion (fsp + 0x4f0#64) 16 := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cells2_to_region16 (fsp + 0x4f0#64)
              (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length) 64#64
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
            ((fsp + 0x4d8#64) ↦₆₄ (kpkPtr + 4#64)) ∗
            ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
            (((fsp + 0x4e8#64) ↦₃₂ kpkId) ∗ memRegion (fsp + 0x4ec#64) 4)) ∗
          (((fsp + 0x4f0#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
            ((fsp + 0x4f8#64) ↦₆₄ 64#64)) by r1b_ac)) ?_
        rw [← r1b_join_region fsp 0x4d0 32 16]
        exact sepConj_mono h4d0_32 h4f0_16
      refine MainHops.sepWPp_weaken_pre ?_
        (hk sm3 kpkCap kpkPtr kpkBs kpkKey kpkSig kpkId hok3 hkpk_rd hsp_ok
          (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx25_2)
          (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx28_2)
          (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx26_2)
          (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx27_2)
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm])
          (by simp only [hsm3, arm64_norm]; try rw [← BitVec.add_assoc]; try rfl)
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm]))
      exact r1b_entails_frame (by r1b_ac) h4d0_48 (by r1b_ac)

end CryptoVerification.SignalSession.Cli.RunCompose
