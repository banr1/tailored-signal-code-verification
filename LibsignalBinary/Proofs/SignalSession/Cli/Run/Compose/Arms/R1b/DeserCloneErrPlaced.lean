/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneErr
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

/-!
# Relocatable Stage 4a Deserialization Error Cleanup for Arm `R1b`

Relocatable (`[LibsignalPlacement]`) counterparts of `R1b.DeserCloneErr` on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open BitVec
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

theorem r1b_spk_err_at_2adc_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat} {v188 kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hi : RunDrop.PlainSpeTag i)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord i)
    (hx1 : s.readReg64 (.gpr 1#5) = kpkCap)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
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
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2adc_placed (v188 := v188)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc hx1 hx26 hpanic hrej)
  conv => lhs; rw [← emp_sepConj (ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗ _)]
  rw [hx12]
  exact sepConj_mono_left (r1b_SpePayload_plain A hi _ _ _ _ _ _ _ _)
set_option maxHeartbeats 600000 in
/-- Relocatable error exit from `<PublicKey>::deserialize` on `spkKey` (`0x24fc → 0x2adc`). -/
theorem r1b_spk_err_24fc_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr v188_in : BitVec 64}
    {kpkBs spkBs spkKey regBs : List (BitVec 8)}
    {e : SignalProtocolError}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x24fc)
    (_hd : PublicKey.deserialize spkKey = .error e)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (Wire.deserializeResult33At (fsp + 0x4d0#64) (.error e) ∗
        memRegion (fsp + 0x4f1#64) 15 ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal4e0 : (fsp + 0x4e0#64) &&& 7#64 = 0#64 := by bv_bits
  let _ := hal; let _ := hal4e0
  have hpc0 := hst.pc
  change s.pc = (blkPl_579).base + 0x24fc#64 at hpc0
  have h120_join : ∀ v : BitVec 64,
      memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ v) ⊢
        memRegion (fsp + 0x120#64) 16 := fun v => by
    refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
    rw [r1b_join_region fsp 0x120 8 8]; exact Entails.refl _
  have h150_join : ∀ v : BitVec 64,
      ((fsp + 0x150#64) ↦₆₄ v) ∗ memRegion (fsp + 0x158#64) 8 ⊢
        memRegion (fsp + 0x150#64) 16 := fun v => by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
    rw [r1b_join_region fsp 0x150 8 8]; exact Entails.refl _
  cases e with
  | noKeyTypeIdentifier =>
    dsimp only [Wire.deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2adc) hst.inv
    rw [runPcPlaced_eq]
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := hc.of_step
      { pc := by rw [runPcPlaced_eq]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
          ((fsp + 0x4d8#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x4d9#64) 24 ∗
          memRegion (fsp + 0x4f1#64) 15 ⊢ memRegion (fsp + 0x4d0#64) 48 := by
      have h33 := Wire.memRegion33_of_err_base (fsp + 0x4d0#64) 0#8
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
      refine Entails.trans (r1b_entails_frame (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    exact MainHops.sepWPp_weaken_pre
      (r1b_entails_frame (by r1b_ac)
        (sepConj_mono h4d0 (sepConj_mono (h120_join kpkPtr) (h150_join kpkCap))) (by r1b_ac))
      (r1b_spk_err_at_2adc_placed (i := 7) (v188 := 0#64)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide)
        (by simp [hsm, arm64_norm, speWord])
        (by simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm])
        hpanic hrej)
  | badKeyType t =>
    dsimp only [Wire.deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2adc) hst.inv
    rw [runPcPlaced_eq]
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := hc.of_step
      { pc := by rw [runPcPlaced_eq]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
          ((fsp + 0x4d8#64) ↦₈ 1#8) ∗ ((fsp + 0x4d9#64) ↦₈ t) ∗
          memRegion (fsp + 0x4da#64) 23 ∗ memRegion (fsp + 0x4f1#64) 15 ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
      have h33 := Wire.memRegion33_of_err_badKeyType (fsp + 0x4d0#64) t
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
      refine Entails.trans (r1b_entails_frame (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    exact MainHops.sepWPp_weaken_pre
      (r1b_entails_frame (by r1b_ac)
        (sepConj_mono h4d0 (sepConj_mono (h120_join kpkPtr) (h150_join kpkCap))) (by r1b_ac))
      (r1b_spk_err_at_2adc_placed (i := 8) (v188 := 0#64)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide)
        (by simp [hsm, arm64_norm, speWord])
        (by simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm])
        hpanic hrej)
  | badKeyLength n =>
    dsimp only [Wire.deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2adc) hst.inv
    rw [runPcPlaced_eq]
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := hc.of_step
      { pc := by rw [runPcPlaced_eq]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
          ((fsp + 0x4d8#64) ↦₈ 2#8) ∗ memRegion (fsp + 0x4d9#64) 7 ∗
          ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (fsp + 0x4e8#64) 9 ∗
          memRegion (fsp + 0x4f1#64) 15 ⊢ memRegion (fsp + 0x4d0#64) 48 := by
      have h33 := Wire.memRegion33_of_err_badKeyLength (fsp + 0x4d0#64) n
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
      refine Entails.trans (r1b_entails_frame (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    exact MainHops.sepWPp_weaken_pre
      (r1b_entails_frame (by r1b_ac)
        (sepConj_mono h4d0 (sepConj_mono (h120_join kpkPtr) (h150_join kpkCap))) (by r1b_ac))
      (r1b_spk_err_at_2adc_placed (i := 9) (v188 := BitVec.ofNat 64 n &&& -256#64)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide)
        (by simp [hsm, arm64_norm, speWord])
        (by simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm])
        hpanic hrej)
  | _ =>
    dsimp only [Wire.deserializeResult33At]
    exact SepWPp.pure_elim False.elim
set_option maxHeartbeats 400000 in
/-- Relocatable `kem::Key::deserialize` error cleanup (`0x2654 → 0x2adc`) freeing `spkSigPtr` for plain `SignalProtocolError` tag `i`. -/
theorem r1b_kem_err_2654_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {spkW0 : BitVec 64} {spkW8 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {r0 r1 r2 r3 : BitVec 8} {v11c : BitVec 32}
    {spkSigPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {v130 v138 w4d8 w4e0 v188_in : BitVec 64}
    {spkSig kpkBs spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2654)
    (hi : RunDrop.PlainSpeTag i)
    (hspk_ptr : spkSigPtr ≠ 0)
    (hspk_sig : spkSig.length = 64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x4d8#64) ↦₆₄ w4d8) ∗
        ((fsp + 0x4e0#64) ↦₆₄ w4e0) ∗
        memRegion (fsp + 0x4e8#64) 24 ∗
        A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ v130) ∗ ((fsp + 0x138#64) ↦₆₄ v138) ∗
        ((fsp + 0x140#64) ↦₆₄ w4e0) ∗ ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ w4d8) ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal150 : (fsp + 0x150#64) &&& 7#64 = 0#64 := by bv_bits
  let _ := hal; let _ := hal150
  rw [r1b_split_region fsp 0x4e8 8 16, r1b_split_region fsp 0x4f0 8 8,
    ProofLib.memRegion_eight (fsp + 0x4e8#64),
    ProofLib.memRegion_eight (fsp + 0x4f0#64),
    ProofLib.memRegion_eight (fsp + 0x4f8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4f8 => SepWPp.exists_elim fun w4f0 =>
    SepWPp.exists_elim fun w4e8 => ?_
  refine r1b_sepWPp_frame (by r1b_ac)
    (r1b_sig64_to_ownedBytes A spkSigPtr spkSig hspk_ptr hspk_sig) (by r1b_ac) ?_
  have hpc := hst.pc
  change s.pc = (blkPl_579).base + 0x2654#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
    (mid := lsρ lsRustDeallocSymCli) hst.inv
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_dealloc_ownedBytes_placed (cap := 64#64) (ptr := spkSigPtr) (len := 64#64) (bs := spkSig)
      hh hbnd hinv1
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run])
      (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x26a0)
      (by rw [runPcPlaced_eq]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by decide) hpanic
      (fun sf1 hin1 hcs1 hfs1 htr1 => ?_)
  have hpc := hin1.pc
  change sf1.pc = (blkPl_579).base + 0x26a0#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2adc) hin1.inv
  rw [runPcPlaced_eq]
  have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have htr_tot : sm2.trace = s.trace := by
    simp only [hsm2, arm64_norm]
    exact htr1.trans (by simp [hsm1, arm64_norm])
  have hfs_tot : sm2.fs.files = s.fs.files := by
    simp only [hsm2, arm64_norm]
    exact (congrArg FsState.files hfs1).trans (by simp [hsm1, arm64_norm])
  have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2adc := hc.of_step
    { pc := by rw [runPcPlaced_eq]; simp [hsm2, arm64_norm]
      run := by simp [hsm2, arm64_norm, hin1.run]
      sp := by simpa [hsm2, arm64_norm] using hin1.sp
      fp := by simpa [hsm2, arm64_norm] using hin1.fp
      inv := hinv2
      vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs
      spAligned := hst.spAligned }
    (by simpa [hsm2, arm64_norm] using hcs1.1.trans (by simp [hsm1, arm64_norm]))
    (by simpa [hsm2, arm64_norm] using hcs1.2.1.trans (by simp [hsm1, arm64_norm]))
    (by simpa [hsm2, arm64_norm] using hcs1.2.2.1.trans (by simp [hsm1, arm64_norm]))
    htr_tot hfs_tot
  have h4d0 :
      ((fsp + 0x4d0#64) ↦₆₄ speWord i) ∗ ((fsp + 0x4d8#64) ↦₆₄ w4d8) ∗
        ((fsp + 0x4e0#64) ↦₆₄ w4e0) ∗ ((fsp + 0x4e8#64) ↦₆₄ w4e8) ∗
        ((fsp + 0x4f0#64) ↦₆₄ w4f0) ∗ ((fsp + 0x4f8#64) ↦₆₄ w4f8) ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord i) w4d8 w4e0 w4e8 w4f0 w4f8
  have h110 : ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ⊢ memRegion (fsp + 0x110#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have h11c : ((fsp + 0x11c#64) ↦₃₂ v11c) ⊢ memRegion (fsp + 0x11c#64) 4 :=
    pointsTo32_entails_memRegion _ _
  have h120 :
      ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ⊢
        memRegion (fsp + 0x120#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cells2_to_region16 (fsp + 0x120#64) 64#64 kpkPtr
  have h130 :
      ((fsp + 0x130#64) ↦₆₄ v130) ∗ ((fsp + 0x138#64) ↦₆₄ v138) ∗
        ((fsp + 0x140#64) ↦₆₄ w4e0) ∗ ((fsp + 0x148#64) ↦₆₄ 64#64) ⊢
        memRegion (fsp + 0x130#64) 0x20 := by
    refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _)))) ?_
    rw [r1b_join_region fsp 0x140 8 8, r1b_join_region fsp 0x138 8 16,
      r1b_join_region fsp 0x130 8 24]
    exact Entails.refl _
  have h150 :
      ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ speWord i) ⊢
        memRegion (fsp + 0x150#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cells2_to_region16 (fsp + 0x150#64) kpkCap (speWord i)
  have h178 : ((fsp + 0x178#64) ↦₆₄ w4d8) ⊢ memRegion (fsp + 0x178#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have h1a8 :
      ((fsp + 0x1a8#64) ↦₆₄ w4f8) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ⊢ memRegion (fsp + 0x1a8#64) 16 := by
    refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo32_entails_memRegion _ _))) ?_
    rw [r1b_join_region fsp 0x1b0 4 4, r1b_join_region fsp 0x1a8 8 8]
    exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac)
    (sepConj_mono
      (r1b_opkStage1Spk_to_regions fsp spkW0 spkW8 spkW16 spkW24
        b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31)
      (sepConj_mono h4d0 (sepConj_mono h110 (sepConj_mono h11c
        (sepConj_mono h120 (sepConj_mono h130 (sepConj_mono h150 (sepConj_mono h178 h1a8))))))))
    (by r1b_ac) ?_
  have hinv_rejoin :
      r1b_invCoreBase_placed A g d s0 ∗
        memRegion (fsp + 0x1d0#64) 0x90 ∗ memRegion (fsp + 0x2c0#64) 0x210 ⊢
      r1b_invCore_placed A g d s0 :=
    Entails.of_eq (r1b_invCore_split_mid_placed A g d s0).symm
  refine r1b_sepWPp_frame (by r1b_ac) hinv_rejoin (by r1b_ac) ?_
  have h164 : ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ⊢ memRegion (fsp + 0x164#64) 4 :=
    pointsTo32_entails_memRegion _ _
  have h190 : ((fsp + 0x190#64) ↦₆₄ d.ikW3) ⊢ memRegion (fsp + 0x190#64) 8 :=
    pointsTo64_entails_memRegion _ _
  refine r1b_sepWPp_frame (by r1b_ac) (sepConj_mono h164 h190) (by r1b_ac) ?_
  have herr_c := r1b_invCore_to_errCommon_placed A g d s0 resStack
  dsimp only at herr_c
  refine r1b_sepWPp_frame (by r1b_ac) herr_c (by r1b_ac) ?_
  exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
    (r1b_spk_err_at_2adc_placed (i := i) (v188 := w4e8)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := [r0, r1, r2, r3])
      hh hdrop hbnd hc2 hi
      (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm])
      hpanic hrej)

end CryptoVerification.SignalSession.Cli.RunCompose
