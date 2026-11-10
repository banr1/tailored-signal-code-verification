/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.RoFramePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpk
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

/-!
# Relocatable Stage 1 (`registration-id` and `signed-pre-key`) Helpers of Arm `R1b`

Relocatable (`[LibsignalPlacement]`) counterparts of `R1b.ReadRegSpk` on Block `579`.
-/

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

set_option maxHeartbeats 400000 in
private theorem r1b_err_13bc_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr spkCap spkPtr regCap regPtr : BitVec 64}
    {eBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x13bc)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx10 : s.readReg64 (.gpr 10#5) = eCap)
    (hx27 : s.readReg64 (.gpr 27#5) = ePtr)
    (hx2 : s.readReg64 .x2 = ((BitVec.ofNat 64 eBs.length).truncate 32).zeroExtend 64)
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
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst := hc.st
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hfp := hst.fp; have hinv := hst.inv; have hvregs := hst.vregs; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
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
  change s.pc = (blkPl_579).base + 0x13bc#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2b28) hinv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b28 := hc.of_step
    { pc := by simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hrun], sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hfp, inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs, spAligned := hsp0 }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  refine MainHops.sepWPp_weaken_pre ?_
    (herrCommon ▸ r1b_cleanup_2b28_placed (spkCap := spkCap) (spkPtr := spkPtr)
      (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs) hh hdrop hbnd hc_m hpanic hrej)
  have h4d0 :
      ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        (((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
          ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32)) ∗
        ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
    rw [← he8]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord 1) eCap ePtr (BitVec.ofNat 64 eBs.length) w4 w5
  have hpay : ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (sm.readReg64 (.gpr 2#5)) := by
    simp only [hsm, arm64_norm, hx12, hx10, hx27, hx2]; r1b_prove_spe_str
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono hpay h4d0) (by r1b_ac)


set_option maxHeartbeats 400000 in
private theorem r1b_err_1384_tail_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sm : State} {resStack : Nat}
    {buf d2 pCap v188 regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {errCommon : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack) (hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b78)
    (herrCommon : r1b_errCommon A g d s0 resStack = errCommon)
    (hbuf : buf ≠ 0#64)
    (hpay : ∀ eBs, ownedBytes A 22#64 buf 22#64 eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5)) (sm.readReg64 (.gpr 23#5))
        (sm.readReg64 (.gpr 27#5)) (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5)) (sm.readReg64 (.gpr 2#5)))
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sm
      (((fsp + 0x170#64) ↦₆₄ 22#64) ∗ ((fsp + 0x188#64) ↦₆₄ v188) ∗
        A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗ errCommon ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_owned A buf d2 hbuf) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun eBs => r1b_sepWPp_pure_left fun _ => ?_
  refine MainHops.sepWPp_weaken_pre ?_
    (herrCommon ▸ r1b_cleanup_2b78_placed (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs) hh hdrop hbnd hc_m hpanic hrej)
  (try dsimp +zetaDelta only)
  generalize runFsp s0 = fsp0
  have h4d0 : ((fsp0 + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp0 + 0x4d8#64) 40 ⊢ memRegion (fsp0 + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1b_cell64_cons (a := fsp0 + 0x4d0#64) pCap (n := 40) (by decide)
  have h168 : memRegion (fsp0 + 0x168#64) 8 ∗ ((fsp0 + 0x170#64) ↦₆₄ 22#64) ∗ memRegion (fsp0 + 0x178#64) 8 ⊢
      memRegion (fsp0 + 0x168#64) 24 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))) ?_
    rw [r1b_join_region fsp0 0x170 8 8, r1b_join_region fsp0 0x168 8 16]; exact Entails.refl _
  have h188 : ((fsp0 + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp0 + 0x190#64) 8 ⊢ memRegion (fsp0 + 0x188#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1b_cell64_cons (a := fsp0 + 0x188#64) v188 (n := 8) (by decide)
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono (hpay eBs) (sepConj_mono h4d0 (sepConj_mono h168 h188))) (by r1b_ac)

private theorem r1b_err_1384_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {buf d2 pCap v188 regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack) (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1384) (hbuf : buf ≠ 0#64)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1) (_hx9 : s.readReg64 (.gpr 9#5) = buf)
    (hx2 : s.readReg64 .x2 = 22#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 8 ∗ ((fsp + 0x170#64) ↦₆₄ 22#64) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  change s.pc = (blkPl_579).base + 0x1384#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2b78) hst.inv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b78 := hc.of_step
    { pc := by simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hst.run], sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hst.fp, inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs, spAligned := hst.spAligned }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  have hpay : ∀ eBs, ownedBytes A 22#64 buf 22#64 eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5)) (sm.readReg64 (.gpr 23#5))
        (sm.readReg64 (.gpr 27#5)) (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5)) (sm.readReg64 (.gpr 2#5)) := fun eBs => by
    simp only [hsm, arm64_norm, hx12, hx2]; r1b_prove_spe_str
  exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by (try dsimp +zetaDelta only); generalize runFsp s0 = fsp0; r1b_ac))
    (r1b_err_1384_tail_placed hh hdrop hbnd hc_m herrCommon hbuf hpay hpanic hrej)


set_option maxHeartbeats 400000 in
private theorem r1b_err_11c4_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sf2 : State} {resStack : Nat}
    {buf pCap pPtr regCap regPtr : BitVec 64} {pBs regBs : List (BitVec 8)}
    {errCore : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (hbnd : r1b_StackBounds B resStack)
    (herrCore : r1b_errCore A g d s0 = errCore)
    (hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x11c4)
    (hx0_buf : sf2.readReg64 .x0 = buf) (hbuf : buf ≠ 0#64)
    (hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf2
      (A.live buf 22 1 ∗ memRegion buf 22 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        errCore ∗ anyHeap ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗ memRegion (fsp + 0x120#64) 16 ∗
        memRegion (fsp + 0x150#64) 16 ∗ memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  have hin2 := hc2.st
  have hbuf_f : (buf == 0#64) = false := beq_false_of_ne hbuf
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin2.sp hin2.spAligned
  have hpc2_in := hin2.pc; change sf2.pc = (blkPl_579).base + 0x11c4#64 at hpc2_in
  have hrun2_in := hin2.run
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x11d0) hin2.inv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm_a hsm_a hinv_a => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hin2 : InRunPlaced r1b_CodeOk s0 sm_a 0x11d0 :=
    { pc := by simp [hsm_a, arm64_norm]
      run := by simp [hsm_a, arm64_norm, hin2.run], sp := by simpa [hsm_a, arm64_norm] using hin2.sp
      fp := by simpa [hsm_a, arm64_norm] using hin2.fp, inv := hinv_a
      vregs := by simpa [calleeSavedVRegs, hsm_a, arm64_norm] using hin2.vregs, spAligned := hin2.spAligned }
  have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm_a 0x11d0 := hc2.of_step hin2
    (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
    (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
  have hx0_buf : sm_a.readReg64 .x0 = buf := by simpa [hsm_a, arm64_norm] using hx0_buf
  have hx23_2 : sm_a.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm_a, arm64_norm] using hx23_2
  have hx27_2 : sm_a.readReg64 (.gpr 27#5) = pPtr := by simpa [hsm_a, arm64_norm] using hx27_2
  have hx8_ro : sm_a.readReg64 (.gpr 8#5) = lsρ r1b_unreadSym := by
    simp only [hsm_a, arm64_norm]
  refine r1b_sepWPp_with_ro_placed hin2.inv r1b_ro_unreadable_placed ?_
  obtain ⟨ro0, ro1, ro2, roRem, hroEq⟩ := r1b_ro_split22 (sm_a.readReg64 (.gpr 8#5))
  conv at hroEq => lhs; rw [hx8_ro]
  clear hsm_a hx8_ro
  rw [hroEq, r1b_buf22_split1 buf, ProofLib.memRegion_eight (fsp + 0x170#64), ProofLib.memRegion_eight (fsp + 0x188#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun v170 => SepWPp.exists_elim fun v188 => ?_
  have hpc2 := hin2.pc; change sm_a.pc = (blkPl_579).base + 0x11d0#64 at hpc2
  have hrun2 := hin2.run; have hsp2 : sm_a.sp = fsp := hin2.sp
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x11e8) hin2.inv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left ?_
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_realign buf _ _) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun d2 => ?_
  by_cases hpCap : pCap = 0#64
  · subst hpCap
    have hpc3 : sm3.pc = (blkPl_579).base + 0x11e8#64 := by simp [hsm3, arm64_norm]
    have hrun3 : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hsp3 : sm3.sp = fsp := by simpa [hsm3, arm64_norm] using hin2.sp
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    have hr23 : sm3.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm3, arm64_norm] using hx23_2
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x1384) hinv3
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm4 0x1384 := hc2.of_step
      { pc := by simp [hsm4, arm64_norm]
        run := by simp [hsm4, arm64_norm, hin2.run], sp := by simpa [hsm4, arm64_norm] using hin2.sp
        fp := by simpa [hsm4, arm64_norm] using hin2.fp, inv := hinv4
        vregs := by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin2.vregs, spAligned := hin2.spAligned }
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
    refine r1b_sepWPp_frame (by r1b_ac) (r1b_ownedBytes_zero A pPtr (BitVec.ofNat 64 pBs.length) pBs) (by r1b_ac) ?_
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_1384_placed (d2 := ro2) (pCap := 0#64) (v188 := d0)
        (regCap := regCap) (regPtr := regPtr) (regBs := regBs) hh hdrop hbnd hc4 hbuf
        (by simp [hsm4, arm64_norm, speWord])
        (by simp [hsm4, arm64_norm])
        (by simp [hsm4, arm64_norm]) hpanic hrej)
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)
  · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
    have hpc3 : sm3.pc = (blkPl_579).base + 0x11e8#64 := by simp [hsm3, arm64_norm]
    have hrun3 : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hsp3 : sm3.sp = fsp := by simpa [hsm3, arm64_norm] using hin2.sp
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hinv3
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hx0_sm4 : sm4.readReg64 .x0 = pPtr := by simp [hsm4, arm64_norm]
    refine r1b_call_frame <| r1b_call_dealloc_ownedBytes_placed (bs := pBs) hh hbnd hinv4
      (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm, hin2.run]) (by simpa [hsm4, arm64_norm] using hin2.sp)
      (by simpa [hsm4, arm64_norm] using hin2.fp) (by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin2.vregs)
      hin2.spAligned (retOff := 0x121c)
      (by simp [hsm4, arm64_norm]) hx0_sm4
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      hpCap hpanic fun sf4 hin4 hcs4 hfs4 htr4 => ?_
    have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf4 0x121c := hc2.after_call
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) hin4 hcs4 (congrArg FsState.files hfs4) htr4
    have hx23_4 : sf4.readReg64 (.gpr 23#5) = 22#64 := hcs4.2.2.2.2.1.trans (by simp [hsm4, arm64_norm])
    have hx26_4 : sf4.readReg64 (.gpr 26#5) = speWord 1 :=
      hcs4.2.2.2.2.2.2.2.1.trans (by simp [hsm4, arm64_norm, speWord])
    have hx27_4 : sf4.readReg64 (.gpr 27#5) = buf :=
      hcs4.2.2.2.2.2.2.2.2.1.trans (by simp [hsm4, arm64_norm])
    have hpc4 := hin4.pc; change sf4.pc = (blkPl_579).base + 0x121c#64 at hpc4
    have hrun4 := hin4.run; have hsp4 : sf4.sp = fsp := hin4.sp
    have hv188 : sm3.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm3, arm64_norm] using hx23_2
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x1384) hin4.inv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm5 hsm5 hinv5 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc5 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm5 0x1384 := hc4.of_step
      { pc := by simp [hsm5, arm64_norm]
        run := by simp [hsm5, arm64_norm, hin4.run], sp := by simpa [hsm5, arm64_norm] using hin4.sp
        fp := by simpa [hsm5, arm64_norm] using hin4.fp, inv := hinv5
        vregs := by simpa [calleeSavedVRegs, hsm5, arm64_norm] using hin4.vregs, spAligned := hin2.spAligned }
      (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
      (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_1384_placed (d2 := ro2) (pCap := pCap) (v188 := 0xffffffffffffffff#64)
        (regCap := regCap) (regPtr := regPtr) (regBs := regBs) hh hdrop hbnd hc5 hbuf
        (by simp [hsm5, arm64_norm, speWord])
        (by simp [hsm5, arm64_norm])
        (by simp [hsm5, arm64_norm]) hpanic hrej)
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)


theorem r1b_err_11b4_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {pCap pPtr regCap regPtr : BitVec 64} {pBs regBs : List (BitVec 8)} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x11b4)
    (hx23 : s.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64) (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗ r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗ memRegion (fsp + 0x120#64) 16 ∗
        memRegion (fsp + 0x150#64) 16 ∗ memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp; dsimp only [r1b_errCommon]; generalize herrCore : r1b_errCore A g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  change s.pc = (blkPl_579).base + 0x11b4#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hst.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_call_frame <| r1b_call_shim_placed hh hbnd hinv1
    (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm, hst.run]) (by simpa [hsm1, arm64_norm] using hst.sp)
    (by simpa [hsm1, arm64_norm] using hst.fp) (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
    hst.spAligned (retOff := 0x11b8)
    (by simp [hsm1, arm64_norm])
    hpanic fun sf1 hin1 hcs1 hfs1 htr1 => ?_
  have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x11b8 := hc.after_call
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) hin1 hcs1 (congrArg FsState.files hfs1) htr1
  have hx23_1 : sf1.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
    hcs1.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx23)
  have hx27_1 : sf1.readReg64 (.gpr 27#5) = pPtr :=
    hcs1.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx27)
  have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x11b8#64 at hpc1
  have hrun1 := hin1.run
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustAllocSymCli) hin1.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_call_frame <| r1b_call_alloc_placed (size := 22) (align := 1) hh hbnd hinv2
    (by simp [hsm2, arm64_norm])
    (by simp [hsm2, arm64_norm, hin1.run]) (by simpa [hsm2, arm64_norm] using hin1.sp)
    (by simpa [hsm2, arm64_norm] using hin1.fp) (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
    hst.spAligned (retOff := 0x11c4)
    (by simp [hsm2, arm64_norm])
    (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by decide) (r1b_layout1 22) hpanic
    (fun sf2 hin2 _ hx0_0 _ htr_null => ?_) (fun sf2 buf hin2 hcs2 hx0_buf hbuf hfs2 htr2 => ?_)
  · have hpc2 := hin2.pc; change sf2.pc = (blkPl_579).base + 0x11c4#64 at hpc2
    have hrun2 := hin2.run
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2d68) hin2.inv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
    exact r1b_oom_2d68_placed hh
      { pc := by simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hin2.run], sp := by simpa [hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm3, arm64_norm] using hin2.fp, inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
      hpanic (r1b_allocFailedIn_mono
        (r1b_allocFailed_of_null (by simpa [hsm2, arm64_norm] using hc1.trace) htr_null) (by simp [hsm3, arm64_norm]))
  · have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x11c4 := hc1.after_call
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) hin2 hcs2 (congrArg FsState.files hfs2) htr2
    have hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
      hcs2.2.2.2.2.1.trans (by simpa [hsm2, arm64_norm] using hx23_1)
    have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
      hcs2.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm2, arm64_norm] using hx27_1)
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
      (r1b_err_11c4_placed hh hdrop hbnd herrCore hc2 hx0_buf hbuf hx23_2 hx27_2 hpanic hrej)


theorem r1b_err_0df0_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x0df0)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  change s.pc = (blkPl_579).base + 0x0df0#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hst.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_shim_placed hh hbnd hinv1
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run]) (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x0df4)
      (by simp [hsm1, arm64_norm])
      hpanic fun sf1 hin1 hcs1 hfs1 htr1 => ?_
  have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x0df4 := hc.after_call
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    hin1 hcs1 (congrArg FsState.files hfs1) htr1
  have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x0df4#64 at hpc1
  have hrun1 := hin1.run
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustAllocSymCli) hin1.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_alloc_placed (size := 14) (align := 1) hh hbnd hinv2
      (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm, hin1.run]) (by simpa [hsm2, arm64_norm] using hin1.sp)
      (by simpa [hsm2, arm64_norm] using hin1.fp)
      (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
      hst.spAligned (retOff := 0x0e00)
      (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by decide) (r1b_layout1 14) hpanic
      (fun sf2 hin2 _ hx0_0 _ htr_null => ?_)
      (fun sf2 buf hin2 hcs2 hx0_buf hbuf hfs2 htr2 => ?_)
  · have hpc2 := hin2.pc; change sf2.pc = (blkPl_579).base + 0x0e00#64 at hpc2
    have hrun2 := hin2.run
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2d44) hin2.inv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
    exact r1b_oom_2d44_placed hh
      { pc := by simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hin2.run], sp := by simpa [hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm3, arm64_norm] using hin2.fp, inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
      hpanic (r1b_allocFailedIn_mono
        (r1b_allocFailed_of_null (by simpa [hsm2, arm64_norm] using hc1.trace) htr_null)
        (by simp [hsm3, arm64_norm]))
  · have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x0e00 := hc1.after_call
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      hin2 hcs2 (congrArg FsState.files hfs2) htr2
    have hbuf_f : (buf == 0#64) = false := beq_false_of_ne hbuf
    have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin2.sp hst.spAligned
    have hpc2_in := hin2.pc; change sf2.pc = (blkPl_579).base + 0x0e00#64 at hpc2_in
    have hrun2_in := hin2.run
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x0e0c) hin2.inv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm_a hsm_a hinv_a => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hin2 : InRunPlaced r1b_CodeOk s0 sm_a 0x0e0c :=
      { pc := by simp [hsm_a, arm64_norm]
        run := by simp [hsm_a, arm64_norm, hin2.run], sp := by simpa [hsm_a, arm64_norm] using hin2.sp
        fp := by simpa [hsm_a, arm64_norm] using hin2.fp, inv := hinv_a
        vregs := by simpa [calleeSavedVRegs, hsm_a, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
    have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm_a 0x0e0c := hc2.of_step hin2
      (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
      (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
    have hx0_buf : sm_a.readReg64 .x0 = buf := by simpa [hsm_a, arm64_norm] using hx0_buf
    have hx8_ro : sm_a.readReg64 (.gpr 8#5) = lsρ r1b_malfSym := by
      simp only [hsm_a, arm64_norm]
    refine r1b_sepWPp_with_ro_placed hin2.inv r1b_ro_malformed_placed ?_
    obtain ⟨ro0, ro1, roRem, hroEq⟩ := r1b_ro_split14 (sm_a.readReg64 (.gpr 8#5))
    conv at hroEq => lhs; rw [hx8_ro]
    clear hsm_a hx8_ro
    rw [hroEq, r1b_buf14_split1 buf]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun d0 => ?_
    have hpc2 := hin2.pc; change sm_a.pc = (blkPl_579).base + 0x0e0c#64 at hpc2
    have hrun2 := hin2.run; have hsp2 : sm_a.sp = fsp := hin2.sp
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x0e34) hin2.inv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    refine r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left ?_
    refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf14_realign buf _) (by r1b_ac) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun d1 => ?_
    have hpc : sm3.pc = (blkPl_579).base + 0x0e34#64 := by simp [hsm3, arm64_norm]
    have hrun : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2b78) hinv3
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm4 0x2b78 := hc2.of_step
      { pc := by simp [hsm4, arm64_norm]
        run := by simp [hsm4, arm64_norm, hin2.run], sp := by simpa [hsm4, hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm4, hsm3, arm64_norm] using hin2.fp, inv := hinv4
        vregs := by simpa [calleeSavedVRegs, hsm4, hsm3, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
    refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf14_owned A buf _ hbuf) (by r1b_ac) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun eBs => r1b_sepWPp_pure_left fun _ => ?_
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_cleanup_2b78_placed (regCap := regCap) (regPtr := regPtr)
        (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs) hh hdrop hbnd hc4 hpanic hrej)
    have hpay : ownedBytes A 14#64 buf 14#64 eBs ⊢
        r1b_SpePayload A (sm4.readReg64 (.gpr 12#5)) (sm4.readReg64 (.gpr 10#5))
          (sm4.readReg64 (.gpr 23#5)) (sm4.readReg64 (.gpr 27#5))
          (sm4.readReg64 (.gpr 16#5)) (sm4.readReg64 (.gpr 14#5))
          (sm4.readReg64 (.gpr 15#5)) (sm4.readReg64 (.gpr 28#5))
          (sm4.readReg64 (.gpr 2#5)) := by
      simp only [hsm4, arm64_norm]; r1b_prove_spe_str
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0
    exact r1b_entails_frame (by r1b_ac) hpay (by r1b_ac)


private theorem r1b_err_0cec_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {buf d2 pCap : BitVec 64} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack) (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x0cec) (hbuf : buf ≠ 0#64)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1) (_hx25 : s.readReg64 (.gpr 25#5) = 22#64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ 22#64) ∗ ((fsp + 0x1a0#64) ↦₆₄ buf) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  change s.pc = (blkPl_579).base + 0x0cec#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2bf0) hst.inv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2bf0 := hc.of_step
    { pc := by simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hst.run], sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hst.fp, inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs, spAligned := hst.spAligned }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_owned A buf d2 hbuf) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun eBs => r1b_sepWPp_pure_left fun _ => ?_
  refine MainHops.sepWPp_weaken_pre ?_ (herrCommon ▸ r1b_cleanup_2bf0_placed hh hdrop hbnd hc_m hpanic hrej)
  have hpay : ownedBytes A 22#64 buf 22#64 eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 9#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (sm.readReg64 (.gpr 22#5)) := by
    simp only [hsm, arm64_norm, hx12]; r1b_prove_spe_str
  have h4d0 : ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ⊢
      memRegion (fsp + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cell64_cons (a := fsp + 0x4d0#64) pCap (n := 40) (by decide)
  have h188 : memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ 22#64) ∗
      ((fsp + 0x1a0#64) ↦₆₄ buf) ∗ memRegion (fsp + 0x1a8#64) 16 ⊢
      memRegion (fsp + 0x188#64) 48 := by
    rw [← sepConj_assoc ((fsp + 0x198#64) ↦₆₄ 22#64)]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cells2_to_region16 (fsp + 0x198#64) 22#64 buf))) ?_
    rw [r1b_join_region fsp 0x198 16 16, r1b_join_region fsp 0x188 16 32]; exact Entails.refl _
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono hpay (sepConj_mono h4d0 h188)) (by r1b_ac)


set_option maxHeartbeats 400000 in
private theorem r1b_err_0c24_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sf2 : State} {resStack : Nat}
    {buf pCap pPtr : BitVec 64} {pBs : List (BitVec 8)}
    {errCore : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (herrCore : r1b_errCore A g d s0 = errCore)
    (hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x0c24)
    (hx0_buf : sf2.readReg64 .x0 = buf) (hbuf : buf ≠ 0#64)
    (hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf2
      (A.live buf 22 1 ∗ memRegion buf 22 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        errCore ∗ anyHeap ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        memRegion (fsp + 0x198#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  have hin2 := hc2.st
  have hbuf_f : (buf == 0#64) = false := beq_false_of_ne hbuf
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin2.sp hin2.spAligned
  have hpc2_in := hin2.pc; change sf2.pc = (blkPl_579).base + 0x0c24#64 at hpc2_in
  have hrun2_in := hin2.run
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x0c30) hin2.inv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm_a hsm_a hinv_a => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hin2 : InRunPlaced r1b_CodeOk s0 sm_a 0x0c30 :=
    { pc := by simp [hsm_a, arm64_norm]
      run := by simp [hsm_a, arm64_norm, hin2.run], sp := by simpa [hsm_a, arm64_norm] using hin2.sp
      fp := by simpa [hsm_a, arm64_norm] using hin2.fp, inv := hinv_a
      vregs := by simpa [calleeSavedVRegs, hsm_a, arm64_norm] using hin2.vregs, spAligned := hin2.spAligned }
  have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm_a 0x0c30 := hc2.of_step hin2
    (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
    (by simp [hsm_a, arm64_norm]) (by simp [hsm_a, arm64_norm])
  have hx0_buf : sm_a.readReg64 .x0 = buf := by simpa [hsm_a, arm64_norm] using hx0_buf
  have hx23_2 : sm_a.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm_a, arm64_norm] using hx23_2
  have hx27_2 : sm_a.readReg64 (.gpr 27#5) = pPtr := by simpa [hsm_a, arm64_norm] using hx27_2
  have hx8_ro : sm_a.readReg64 (.gpr 8#5) = lsρ r1b_unreadSym := by
    simp only [hsm_a, arm64_norm]
  refine r1b_sepWPp_with_ro_placed hin2.inv r1b_ro_unreadable_placed ?_
  obtain ⟨ro0, ro1, ro2, roRem, hroEq⟩ := r1b_ro_split22 (sm_a.readReg64 (.gpr 8#5))
  conv at hroEq => lhs; rw [hx8_ro]
  clear hsm_a hx8_ro
  have h198 := r1b_region16_to_cells (fsp + 0x198#64)
  have ha1a0 : (fsp + 0x198#64) + 8#64 = fsp + 0x1a0#64 := by bv_omega
  rw [ha1a0] at h198
  rw [hroEq, r1b_buf22_split1 buf, h198]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun v198 => SepWPp.exists_elim fun v1a0 => ?_
  have hpc2 := hin2.pc; change sm_a.pc = (blkPl_579).base + 0x0c30#64 at hpc2
  have hrun2 := hin2.run; have hsp2 : sm_a.sp = fsp := hin2.sp
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x0c44) hin2.inv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <|
    r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left ?_
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_realign buf _ _) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun d2 => ?_
  by_cases hpCap : pCap = 0#64
  · subst hpCap
    have hpc : sm3.pc = (blkPl_579).base + 0x0c44#64 := by simp [hsm3, arm64_norm]
    have hrun : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hsp : sm3.sp = fsp := by simpa [hsm3, arm64_norm] using hin2.sp
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    have hr23 : sm3.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by simpa [hsm3, arm64_norm] using hx23_2
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x0cec) hinv3
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm4 0x0cec := hc2.of_step
      { pc := by simp [hsm4, arm64_norm]
        run := by simp [hsm4, arm64_norm, hin2.run], sp := by simpa [hsm4, arm64_norm] using hin2.sp
        fp := by simpa [hsm4, arm64_norm] using hin2.fp, inv := hinv4
        vregs := by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin2.vregs, spAligned := hin2.spAligned }
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
    refine r1b_sepWPp_frame (by r1b_ac)
      (r1b_ownedBytes_zero A pPtr (BitVec.ofNat 64 pBs.length) pBs)
      (by r1b_ac) ?_
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_0cec_placed (d2 := ro2) (pCap := 0#64) hh hdrop hbnd hc4 hbuf
        (by simp [hsm4, arm64_norm, speWord]) (by simp [hsm4, arm64_norm]) hpanic hrej)
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)
  · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
    have hpc : sm3.pc = (blkPl_579).base + 0x0c44#64 := by simp [hsm3, arm64_norm]
    have hrun : sm3.status = .Running := by simp [hsm3, arm64_norm, hin2.run]
    have hsp : sm3.sp = fsp := by simpa [hsm3, arm64_norm] using hin2.sp
    have hr0 : sm3.readReg64 .x0 = buf := by simpa [hsm3, arm64_norm] using hx0_buf
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hinv3
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hx0_sm4 : sm4.readReg64 .x0 = pPtr := by simp [hsm4, arm64_norm]
    refine r1b_call_frame <|
      r1b_call_dealloc_ownedBytes_placed (bs := pBs) hh hbnd hinv4
        (by simp [hsm4, arm64_norm])
        (by simp [hsm4, arm64_norm, hin2.run]) (by simpa [hsm4, arm64_norm] using hin2.sp)
        (by simpa [hsm4, arm64_norm] using hin2.fp)
        (by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin2.vregs)
        hin2.spAligned (retOff := 0x0c68)
        (by simp [hsm4, arm64_norm]) hx0_sm4
        (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) hpCap hpanic
        fun sf4 hin4 hcs4 hfs4 htr4 => ?_
    have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf4 0x0c68 := hc2.after_call
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      hin4 hcs4 (congrArg FsState.files hfs4) htr4
    have hx23_4 : sf4.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
      hcs4.2.2.2.2.1.trans (by simpa [hsm4, arm64_norm] using hx23_2)
    have hx25_4 : sf4.readReg64 (.gpr 25#5) = 22#64 :=
      hcs4.2.2.2.2.2.2.1.trans (by simp [hsm4, arm64_norm])
    have hx27_4 : sf4.readReg64 (.gpr 27#5) = speWord 1 :=
      hcs4.2.2.2.2.2.2.2.2.1.trans (by simp [hsm4, arm64_norm, speWord])
    have hpc4 := hin4.pc; change sf4.pc = (blkPl_579).base + 0x0c68#64 at hpc4
    have hrun4 := hin4.run
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x0cec) hin4.inv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm5 hsm5 hinv5 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc5 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm5 0x0cec := hc4.of_step
      { pc := by simp [hsm5, arm64_norm]
        run := by simp [hsm5, arm64_norm, hin4.run], sp := by simpa [hsm5, arm64_norm] using hin4.sp
        fp := by simpa [hsm5, arm64_norm] using hin4.fp, inv := hinv5
        vregs := by simpa [calleeSavedVRegs, hsm5, arm64_norm] using hin4.vregs, spAligned := hin2.spAligned }
      (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
      (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_0cec_placed (d2 := ro2) (pCap := pCap) hh hdrop hbnd hc5 hbuf
        (by simp [hsm5, arm64_norm, speWord])
        (by simpa [hsm5, arm64_norm] using hx25_4) hpanic hrej)
    subst herrCore; dsimp only [r1b_errCommon]; (try dsimp +zetaDelta only)
    generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)


theorem r1b_err_0c14_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {pCap pPtr : BitVec 64} {pBs : List (BitVec 8)} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack) (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x0c14)
    (hx23 : s.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        memRegion (fsp + 0x198#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  change s.pc = (blkPl_579).base + 0x0c14#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hst.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_shim_placed hh hbnd hinv1
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run]) (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x0c18)
      (by simp [hsm1, arm64_norm])
      hpanic fun sf1 hin1 hcs1 htr_fs1 htr1 => ?_
  have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x0c18 := hc.after_call
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    hin1 hcs1 (congrArg FsState.files htr_fs1) htr1
  have hx23_1 : sf1.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
    hcs1.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx23)
  have hx27_1 : sf1.readReg64 (.gpr 27#5) = pPtr :=
    hcs1.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx27)
  have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x0c18#64 at hpc1
  have hrun1 := hin1.run
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustAllocSymCli) hin1.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_alloc_placed (size := 22) (align := 1) hh hbnd hinv2
      (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm, hin1.run]) (by simpa [hsm2, arm64_norm] using hin1.sp)
      (by simpa [hsm2, arm64_norm] using hin1.fp)
      (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
      hst.spAligned (retOff := 0x0c24)
      (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by decide) (r1b_layout1 22) hpanic
      (fun sf2 hin2 _ hx0_0 _ htr_null => ?_)
      (fun sf2 buf hin2 hcs2 hx0_buf hbuf hfs2 htr2 => ?_)
  · have hpc2 := hin2.pc; change sf2.pc = (blkPl_579).base + 0x0c24#64 at hpc2
    have hrun2 := hin2.run
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2d68) hin2.inv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
    exact r1b_oom_2d68_placed hh
      { pc := by simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hin2.run], sp := by simpa [hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm3, arm64_norm] using hin2.fp, inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs, spAligned := hst.spAligned }
      hpanic (r1b_allocFailedIn_mono
        (r1b_allocFailed_of_null (by simpa [hsm2, arm64_norm] using hc1.trace) htr_null)
        (by simp [hsm3, arm64_norm]))
  · have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x0c24 := hc1.after_call
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      hin2 hcs2 (congrArg FsState.files hfs2) htr2
    have hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
      hcs2.2.2.2.2.1.trans (by simpa [hsm2, arm64_norm] using hx23_1)
    have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
      hcs2.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm2, arm64_norm] using hx27_1)
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
      (r1b_err_0c24_placed hh hdrop hbnd herrCore hc2 hx0_buf hbuf hx23_2 hx27_2 hpanic hrej)


/-! ## `split_signed` Sub-Step (`0x1230 → 0x1260`) -/

set_option maxHeartbeats 800000 in
private theorem r1b_after_spk_dealloc_err_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sf1 : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {eCap ePtr regCap regPtr spkCap spkPtr : BitVec 64} {eBs spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack) (hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x1248)
    (hspk_le : spkBs.length ≤ spkCap.toNat) (hspk_lt : spkCap.toNat < 2 ^ 63) (hspk_ne : spkPtr ≠ 0)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf1
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d0#64 + 8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4d0#64 + 16#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4d0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4d0#64 + 32#64) 16 ∗
        ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        (spkPtr ↦ₛ spkBs) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        (r1b_ownedRest A spkCap spkPtr spkBs.length ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
          ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
          ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24))
      Q Qp (runOom s0) := by
  intro fsp
  generalize hinvCore : r1b_invCore_placed A g d s0 = invCore
  have hin1 := hc1.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin1.sp hin1.spAligned
  have hrejoin := r1b_ownedBytes_rejoin A spkCap spkPtr spkBs hspk_le hspk_lt hspk_ne
  have he8 : ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) =
      ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
        ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) := by
    have hz := r1b_u64_split32 (fsp + 0x4e8#64) (BitVec.ofNat 64 eBs.length)
    have ha : (fsp + 0x4e8#64) + 4#64 = fsp + 0x4ec#64 := by bv_omega
    rwa [ha] at hz
  refine r1b_sepWPp_frame (by r1b_ac) hrejoin (by r1b_ac) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [he8]; simp only [sepConj_assoc]; dsimp only [speWord]
  have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x1248#64 at hpc1
  have hrun1 := hin1.run; have hsp1 : sf1.sp = fsp := hin1.sp
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x13bc) hin1.inv
  rw [runPcPlaced_eq]
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x13bc := hc1.of_step
    { pc := by simp [hsm2, arm64_norm]
      run := by simp [hsm2, arm64_norm, hin1.run], sp := by simpa [hsm2, arm64_norm] using hin1.sp
      fp := by simpa [hsm2, arm64_norm] using hin1.fp, inv := hinv2
      vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs, spAligned := hin1.spAligned }
    (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
    (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
  have he8' : ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
      ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) ⊢
      ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) := by
    rw [← he8]; exact Entails.refl _
  generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon
  have hst_err :
      (invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗ ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool) ⊢
        errCommon ∗ memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
    rw [← hinvCore, ← herrCommon]
    exact r1b_stage_to_err_placed A g d s0 resStack (ofLe32 r0 r1 r2 r3)
  have h188 : memRegion (fsp + 0x188#64) 8 ∗ memRegion (fsp + 0x190#64) 8 ⊢
      memRegion (fsp + 0x188#64) 16 := by
    rw [r1b_join_region fsp 0x188 8 8]; exact Entails.refl _
  have hex :
      (memRegion (fsp + 0x188#64) 8 ∗
        (invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗ ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)) ⊢
        errCommon ∗ memRegion (fsp + 0x188#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16 :=
    Entails.trans (sepConj_mono_right hst_err)
      (r1b_entails_frame (by r1b_ac) h188 (by r1b_ac))
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_err_13bc_placed (eCap := eCap) (ePtr := ePtr) (eBs := eBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3]) hh hdrop hbnd hc2
      (by simp [hsm2, arm64_norm, speWord]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) hpanic hrej)
  rw [herrCommon]
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono he8' hex) (by r1b_ac)


set_option maxHeartbeats 600000 in
theorem r1b_after_spk_dealloc_placed [LibsignalPlacement] {S : RunSem} {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {regCap regPtr spkCap spkPtr : BitVec 64} {spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hc : RunCalleesPlaced A H B σ)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack) (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x1230)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hx23 : s.readReg64 (.gpr 23#5) = spkCap) (hx9 : s.readReg64 (.gpr 9#5) = spkPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 spkBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp)
    (hk : ∀ (sf : State) (spkId : BitVec 32) (spkKey spkSig : List (BitVec 8)),
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x1260 →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
          ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
          ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCore_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        memRegion (fsp + 0x168#64) 8 ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
        ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hreg_rd
  generalize hinvCore : r1b_invCore_placed A g d s0 = invCore at *
  have hst := hok.st; have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  rw [ProofLib.memRegion_eight (fsp + 0x168#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v168 =>
    r1b_call_frame <| r1b_sepWPp_borrow_core A (cap := spkCap) (ptr := spkPtr)
      (len := BitVec.ofNat 64 spkBs.length) (bs := spkBs)
      fun ⟨_, hspk_le, hspk_lt, hspk_ne⟩ => ?_
  have hcmn_f : (spkCap + 1#64 == 0#64) = false := beq_false_of_ne (r1b_cmn1_false_of_lt63 hspk_lt)
  have hlen_nat : (BitVec.ofNat 64 spkBs.length).toNat = spkBs.length := by
    simp only [BitVec.toNat_ofNat]; omega
  change s.pc = (blkPl_579).base + 0x1230#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 592) hst.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_splitSigned_placed (ret := fsp + 0x4d0#64) (fp := spkPtr) (file := spkBs) hh hc hbnd hinv1
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run]) (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x1248)
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp only [hsm1, arm64_norm, hx2]; exact hlen_nat)
      (by simpa [hsm1, arm64_norm] using hok.trace) hpanic
      (fun sf1 eCap ePtr eBs hin1 hcs1 hsp_none hfs1 htr1 => ?_)
      (fun sf1 spkId spkKey spkSig hin1 hcs1 hsp_ok hfs1 htr1 => ?_)
  · have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x1248 := hok.after_call
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      hin1 hcs1 hfs1 htr1
    have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x1248 :=
      hok1.to_err (r1b_none_spk_split hspk_rd hsp_none)
    refine MainHops.sepWPp_weaken_pre ?_
      (hinvCore ▸ r1b_after_spk_dealloc_err_placed (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
        (eCap := eCap) (ePtr := ePtr) (regCap := regCap) (regPtr := regPtr)
        (spkCap := spkCap) (spkPtr := spkPtr) (eBs := eBs) (spkBs := spkBs)
        hh hdrop hbnd hc1 hspk_le hspk_lt hspk_ne hpanic hrej)
    exact Entails.of_eq (by r1b_ac)
  · have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x1248 := hok.after_call
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      hin1 hcs1 hfs1 htr1
    have hx26_1 : sf1.readReg64 (.gpr 26#5) = d.dirPtr :=
      hcs1.2.2.2.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx26)
    have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simpa [hsm1, arm64_norm] using hx28)
    have hrejoin := r1b_ownedBytes_rejoin A spkCap spkPtr spkBs hspk_le hspk_lt hspk_ne
    refine r1b_sepWPp_frame (by r1b_ac) hrejoin (by r1b_ac) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; dsimp only [splitOkTag]
    have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x1248#64 at hpc1
    have hrun1 := hin1.run; have hsp1 : sf1.sp = fsp := hin1.sp
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x1260) hin1.inv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm2 0x1260 := hok1.of_step
      { pc := by simp [hsm2, arm64_norm]
        run := by simp [hsm2, arm64_norm, hin1.run], sp := by simpa [hsm2, arm64_norm] using hin1.sp
        fp := by simpa [hsm2, arm64_norm] using hin1.fp, inv := hinv2
        vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs, spAligned := hst.spAligned }
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ (spkPtr + 4#64)) ∗
          ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 spkKey.length) ∗
          (((fsp + 0x4e8#64) ↦₃₂ spkId) ∗ memRegion (fsp + 0x4ec#64) 4) ⊢
          memRegion (fsp + 0x4d0#64) 32 := by
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))) ?_
      rw [r1b_join_region fsp 0x4e8 4 4]
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4e0#64) (BitVec.ofNat 64 spkKey.length) (n := 8) (by decide)))) ?_
      refine Entails.trans (sepConj_mono_right
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4d8#64) (spkPtr + 4#64) (n := 16) (by decide))) ?_
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 24) (by decide)
    refine MainHops.sepWPp_weaken_pre ?_
      (hk sm2 spkId spkKey spkSig hok2 hsp_ok
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simpa [hsm2, arm64_norm] using hx26_1) (by simpa [hsm2, arm64_norm] using hx28_1))
    exact r1b_entails_frame (by r1b_ac) h4d0 (by r1b_ac)

end CryptoVerification.SignalSession.Cli.RunCompose
