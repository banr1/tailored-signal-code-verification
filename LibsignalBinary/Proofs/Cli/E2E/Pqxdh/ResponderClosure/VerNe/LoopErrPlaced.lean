/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErr
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrDefsPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable Previous-Session Version-Skip Tail Proof (`+0x1fd4 → +0x2cfc`)

Relocatable (`[LibsignalPlacement]`) basic-block and composition proofs for the version-skip tail
(`(blkPl_518).base + 0x1fd4 → (blkPl_518).base + 0x2cfc`) on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cond_ne_subs32_4_of_ne_pl {v : BitVec 32} (h : v ≠ 4#32) :
    ConditionHolds CondCode.NE (subsPState32 4#32 v) = true := by
  unfold subsPState32
  rw [conditionHolds_ne_subs32, bne_iff_ne]
  exact Ne.symm h

/-- Segment `(blkPl_518).base + 0x1fd4 → lsρ pqxdhLogClosureSym` on `lsProg_518 ext`. -/
theorem over_prev_err_seg1_cli_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (prevPtr ua90 : BitVec 64) (msgVer ua98 : BitVec 32)
    (hver_ne : msgVer ≠ 4#32)
    (hpc : s.pc = (blkPl_518).base + 0x1fd4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 4#64)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 519) s
      (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xa90#64) ↦₆₄ ua90) ∗
       ((s.sp + 0xa98#64) ↦₃₂ ua98))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xa90#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((s.sp + 0xa98#64) ↦₃₂ msgVer)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x27 = prevPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x20b4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ver := cond_ne_subs32_4_of_ne_pl hver_ne
  have hx8_32 : s.readReg32 (Reg.gpr 8#5) = 4#32 := by simp [State.readReg32, hx8]
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment `(blkPl_518).base + 0x20b4 → lsmpl.base 512` on `lsProg_518 ext`. -/
theorem over_prev_err_seg2_cli_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (prevPtr errsPtr errTag e1 e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x20b4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 512) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
       ((s.sp + 0xa98#64) ↦₆₄ e1) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ e2) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ e3) ∗
       ((s.sp + 0xab0#64) ↦₆₄ e4) ∗
       ((s.sp + 0xab8#64) ↦₆₄ e5) ∗
       ((errsPtr + 48#64) ↦₆₄ u_e0) ∗
       ((errsPtr + 56#64) ↦₆₄ u_e1) ∗
       ((errsPtr + 64#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 72#64) ↦₆₄ u_e3) ∗
       ((errsPtr + 80#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 88#64) ↦₆₄ u_e5))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
          ((s.sp + 0xa98#64) ↦₆₄ e1) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ e2) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ e3) ∗
          ((s.sp + 0xab0#64) ↦₆₄ e4) ∗
          ((s.sp + 0xab8#64) ↦₆₄ e5) ∗
          ((errsPtr + 48#64) ↦₆₄ errTag) ∗
          ((errsPtr + 56#64) ↦₆₄ e1) ∗
          ((errsPtr + 64#64) ↦₆₄ e2) ∗
          ((errsPtr + 72#64) ↦₆₄ e3) ∗
          ((errsPtr + 80#64) ↦₆₄ e4) ∗
          ((errsPtr + 88#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x930#64 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x27 = prevPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x20fc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  have herr1 : 1#64 * 0x30#64 + errsPtr = errsPtr + 48#64 := by bv_arith
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment `(blkPl_518).base + 0x20fc → (blkPl_518).base + 0x2cfc` on `lsProg_518 ext`. -/
theorem over_prev_err_seg3_cli_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (prevPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x20fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
      (((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64))) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## Spatial helpers and log-closure contract -/

private theorem spA90_344_ver_split_eq_pl (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 344 = (∃∗ e5 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e3 : BitVec 64,
      ∃∗ e2 : BitVec 64, ∃∗ ua9c : BitVec 32, ∃∗ ua98 : BitVec 32, ∃∗ ua90 : BitVec 64,
      ((sp + 0xa90#64) ↦₆₄ ua90) ∗ ((sp + 0xa98#64) ↦₃₂ ua98) ∗ ((sp + 0xa9c#64) ↦₃₂ ua9c) ∗
      ((sp + 0xaa0#64) ↦₆₄ e2) ∗ ((sp + 0xaa8#64) ↦₆₄ e3) ∗
      ((sp + 0xab0#64) ↦₆₄ e4) ∗ ((sp + 0xab8#64) ↦₆₄ e5) ∗
      memRegion (sp + 0xac0#64) 296) := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 8) (k := 336) (b' := sp + 0xa98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa98#64) (n := 4) (k := 332) (b' := sp + 0xa9c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa9c#64) (n := 4) (k := 328) (b' := sp + 0xaa0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa0#64) (n := 8) (k := 320) (b' := sp + 0xaa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa8#64) (n := 8) (k := 312) (b' := sp + 0xab0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab0#64) (n := 8) (k := 304) (b' := sp + 0xab8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab8#64) (n := 8) (k := 296) (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0xa90#64), ProofLib.memRegion_four (sp + 0xa98#64),
      ProofLib.memRegion_four (sp + 0xa9c#64), ProofLib.memRegion_eight (sp + 0xaa0#64),
      ProofLib.memRegion_eight (sp + 0xaa8#64), ProofLib.memRegion_eight (sp + 0xab0#64),
      ProofLib.memRegion_eight (sp + 0xab8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem pointsTo32_pair_spA98_pl (sp : BitVec 64) (lo hi : BitVec 32) :
    (((sp + 0xa98#64) ↦₃₂ lo) ∗ ((sp + 0xa9c#64) ↦₃₂ hi)) = ((sp + 0xa98#64) ↦₆₄ (hi ++ lo)) := by
  have h : sp + 0xa9c#64 = (sp + 0xa98#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair]

private theorem spA90_344_fold_pl (sp w0 w1 e2 e3 e4 e5 : BitVec 64) :
    ((sp + 0xa90#64) ↦₆₄ w0) ∗ ((sp + 0xa98#64) ↦₆₄ w1) ∗ ((sp + 0xaa0#64) ↦₆₄ e2) ∗
    ((sp + 0xaa8#64) ↦₆₄ e3) ∗ ((sp + 0xab0#64) ↦₆₄ e4) ∗ ((sp + 0xab8#64) ↦₆₄ e5) ∗
    memRegion (sp + 0xac0#64) 296 ⊢
    memRegion (sp + 0xa90#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 8) (k := 336) (b' := sp + 0xa98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa98#64) (n := 8) (k := 328) (b' := sp + 0xaa0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa0#64) (n := 8) (k := 320) (b' := sp + 0xaa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa8#64) (n := 8) (k := 312) (b' := sp + 0xab0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab0#64) (n := 8) (k := 304) (b' := sp + 0xab8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab8#64) (n := 8) (k := 296) (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))))

private theorem errs144_split_eq_at48_pl (errsPtr : BitVec 64) :
    memRegion (errsPtr + 48#64) 144 = (∃∗ u_e5 : BitVec 64, ∃∗ u_e4 : BitVec 64, ∃∗ u_e3 : BitVec 64,
      ∃∗ u_e2 : BitVec 64, ∃∗ u_e1 : BitVec 64, ∃∗ u_e0 : BitVec 64,
      ((errsPtr + 48#64) ↦₆₄ u_e0) ∗ ((errsPtr + 56#64) ↦₆₄ u_e1) ∗
      ((errsPtr + 64#64) ↦₆₄ u_e2) ∗ ((errsPtr + 72#64) ↦₆₄ u_e3) ∗
      ((errsPtr + 80#64) ↦₆₄ u_e4) ∗ ((errsPtr + 88#64) ↦₆₄ u_e5) ∗
      memRegion (errsPtr + 96#64) 96) := by
  rw [ProofLib.memRegion_split' (b := errsPtr + 48#64) (n := 8) (k := 136) (b' := errsPtr + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 56#64) (n := 8) (k := 128) (b' := errsPtr + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 64#64) (n := 8) (k := 120) (b' := errsPtr + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 72#64) (n := 8) (k := 112) (b' := errsPtr + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 80#64) (n := 8) (k := 104) (b' := errsPtr + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 88#64) (n := 8) (k := 96) (b' := errsPtr + 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (errsPtr + 48#64), ProofLib.memRegion_eight (errsPtr + 56#64),
      ProofLib.memRegion_eight (errsPtr + 64#64), ProofLib.memRegion_eight (errsPtr + 72#64),
      ProofLib.memRegion_eight (errsPtr + 80#64), ProofLib.memRegion_eight (errsPtr + 88#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem errs48_fold_ver_at48_pl (errsPtr e2 e3 e4 e5 : BitVec 64) (msgVer ua9c : BitVec 32) :
    ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 56#64) ↦₆₄ (ua9c ++ msgVer)) ∗
    ((errsPtr + 64#64) ↦₆₄ e2) ∗ ((errsPtr + 72#64) ↦₆₄ e3) ∗ ((errsPtr + 80#64) ↦₆₄ e4) ∗
    ((errsPtr + 88#64) ↦₆₄ e5) ⊢
    ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
    memRegion (errsPtr + 60#64) 36 := by
  have hpair : ((errsPtr + 56#64) ↦₆₄ (ua9c ++ msgVer)) =
      ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ ((errsPtr + 60#64) ↦₃₂ ua9c) := by
    have h60 : errsPtr + 60#64 = (errsPtr + 56#64) + 4#64 := by bv_omega
    rw [h60, ← pointsTo32_pair]
  rw [hpair, sepConj_assoc,
      ProofLib.memRegion_split' (b := errsPtr + 60#64) (n := 4) (k := 32) (b' := errsPtr + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 64#64) (n := 8) (k := 24) (b' := errsPtr + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 72#64) (n := 8) (k := 16) (b' := errsPtr + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 80#64) (n := 8) (k := 8) (b' := errsPtr + 88#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))

/-- Relocatable `[LibsignalPlacement]` spec for `pqxdh_log_closure` (Block `519`). -/
def pqxdhLogClosurePlacedSpec [LibsignalPlacement] : Spec Unit where
  pre := fun _ s =>
    ⌜True⌝ ∗ pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack
  post := fun _ s sf =>
    ⌜sf.trace = s.trace⌝ ∗ pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack

/-! ## `LibsignalCodeRoLoaded` composition -/

private theorem bind_sepWP_cro_frame [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm (hcro.of_keepsFrozen hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem call_raw_nopanic_cro [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcro.1, hm⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · dsimp only [withLsCodeLoaded] at _hoom_post; rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm
        (hcro.of_keepsFrozen hsteps.keepsFrozen) R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

set_option maxHeartbeats 1000000 in
/-- Pointwise `LibsignalCodeRoLoaded`-threaded proof of `OverPrevErr`
(`(blkPl_518).base + 0x1fd4 → (blkPl_518).base + 0x2cfc`) on `lsProg_518 ext`. -/
theorem overPrevErr_cro_placed_at [LibsignalPlacement]
    {A : RustAlloc} (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (prevPtr errsPtr : BitVec 64) (msgVer : BitVec 32)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hver_ne : msgVer ≠ 4#32)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1fd4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = 4#64)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
      (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       memRegion (errsPtr + 48#64) 144 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗
       sessionStateAt A (s.sp + 0x930#64) G st ∗
       pqLogLevelCellPlaced ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 60#64) 36 ∗
          memRegion (errsPtr + 96#64) 96 ∗
          memRegion (s.sp + 0xa90#64) 344 ∗
          memRegion (s.sp + 0x930#64) 344 ∗
          pqLogLevelCellPlaced ∗
          A.pool ∗
          stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem)
      (PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (spA90_344_ver_split_eq_pl s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e5 => SepWPp.exists_elim fun e4 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun ua9c => SepWPp.exists_elim fun ua98 => SepWPp.exists_elim fun ua90 => ?_
  refine bind_sepWP_cro_frame hL hcro
    (over_prev_err_seg1_cli_placed_wp ext s prevPtr ua90 msgVer ua98
      hver_ne hpc hrun hsp_align hx8 hx27)
    (by sep_focus)
    fun s1 hpc1 hrun1 hL1 hcro1 ⟨hsp1, htr1, hx19_1, hx20_1, hx27_1, hx29_1, hlr1, hvregs1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_raw_nopanic_cro
    (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack)
    hL1 hcro1 hLogClosure hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1])
    trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hL2 hcro2 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hstack_restore2 :
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore2 (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, _, _, _, _, _, _, hx27_cs2, _, hx29_cs2, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = s.readReg64 .x19 := hx19_cs2.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = s.readReg64 .x20 := hx20_cs2.trans hx20_1
  have hx27_2 : s2.readReg64 .x27 = prevPtr := hx27_cs2.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo32_pair_spA98_pl s.sp msgVer ua9c)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs144_split_eq_at48_pl errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hseg2 := over_prev_err_seg2_cli_placed_wp ext s2 prevPtr errsPtr
    0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc2 hrun2 hsp2_align hx27_2
  rw [hsp2] at hseg2
  refine bind_sepWP_cro_frame hL2 hcro2 hseg2 (by sep_focus)
    fun s3 hpc3 hrun3 hL3 hcro3 ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx20_3, hx27_3, hx29_3, hlr3, hvregs3⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (errs48_fold_ver_at48_pl errsPtr e2 e3 e4 e5 msgVer ua9c) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (spA90_344_fold_pl s.sp 0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_raw_nopanic_cro
    (spec := dropSessionStructureLocal2Spec A)
    (x := (⟨s.sp + 0x930#64, G, st⟩ : DropSessionStructureGhost))
    (φ := s3.readReg64 .x0 = s.sp + 0x930#64)
    (T := sessionStateAt A (s.sp + 0x930#64) G st ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hL3 hcro3 hDropSS3 hpc3 hrun3 hsp3_al hlr3
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp3])
    hx0_3 (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hL4 hcro4 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp3, sepConj_assoc]
  refine SepWPp.pure_elim fun htr4_3 => ?_
  have hstack_restore4 :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore4 (by sep_focus) ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, hx20_cs4, _, _, _, _, _, _, hx27_cs4, _, hx29_cs4, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = s.readReg64 .x19 := hx19_cs4.trans (hx19_3.trans hx19_2)
  have hx20_4 : s4.readReg64 .x20 = s.readReg64 .x20 := hx20_cs4.trans (hx20_3.trans hx20_2)
  have hx27_4 : s4.readReg64 .x27 = prevPtr := hx27_cs4.trans hx27_3
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hx29_cs4.trans (hx29_3.trans hx29_2)
  have hseg3 := over_prev_err_seg3_cli_placed_wp ext s4 prevPtr hpc4 hrun4 hsp4_align hx27_4
  rw [hsp4] at hseg3
  refine bind_sepWP_cro_frame hL4 hcro4 hseg3 (by sep_focus)
    fun sf hpcf hrunf hLf hcrof ⟨hspf_4, htrf_4, hx19_f, hx20_f, hx29_f, hvregsf⟩ => ?_
  have htrf : sf.trace = s0.trace := by rw [htrf_4, htr4_3, htr3_2, htr2_1, htr1, htr]
  have hx19f : sf.readReg64 .x19 = s.readReg64 .x19 := hx19_f.trans hx19_4
  have hx20f : sf.readReg64 .x20 = s.readReg64 .x20 := hx20_f.trans hx20_4
  have hx29f : sf.readReg64 .x29 = s.readReg64 .x29 := hx29_f.trans hx29_4
  have hvregsf_s : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf, hvregs_cs4, hvregs3, hvregs_cs2, hvregs1]
  refine SepWPp.done hpcf hrunf
    ⟨Entails.of_eq (by ac_rfl), hspf_4, htrf, hx19f, hx20f, hx29f, hvregsf_s, hcrof, hLf⟩

/-! ## `LibsignalFrozen` / `[LibsignalFullPlacement]` corollaries -/

/-- Lift Block `519` (`VerNe.pqxdhLogClosurePlacedSpec`) to any `callerProg`
under `[LibsignalFullPlacement]`. -/
theorem pqxdh_log_closure_verNe_frozen_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 519)
      (withLsFrozen lsmpl pqxdhLogClosurePlacedSpec) := by
  refine subroutine_ok_outcome_intro fun x F s0 hpc hrun hm hsp hL => ?_
  have hm' : s0.mem ⊨ (withLsFrozen lsmpl Matched.pqxdhLogClosurePlacedSpec).pre x s0 ∗ F := by
    dsimp only [withLsFrozen, pqxdhLogClosurePlacedSpec, Matched.pqxdhLogClosurePlacedSpec,
      pqLogLevelCellPlaced, FromRecordCallees.lsLogOff] at hm ⊢
    simpa only [pure_true, emp_sepConj] using hm
  exact subroutine_ok_apply_outcome
    (Matched.pqxdh_log_closure_frozen_placed_ok_of_block (callerProg := callerProg))
    x F hpc hrun hm' hsp hL

theorem bind_sepWP_fr_frame [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → LibsignalFrozen lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm (libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem call_raw_nopanic_fr [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsFrozen lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem → LibsignalFrozen lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  have hm' : s.mem ⊨ (withLsFrozen lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsFrozen]; rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalFrozen lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hfr, hm⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · dsimp only [withLsFrozen] at _hoom_post; rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [withLsFrozen] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm
        (libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen) R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsFrozen] at hpost; rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsFrozen] at hpost; rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

set_option maxHeartbeats 1000000 in
/-- Pointwise `LibsignalFrozen`-discharged proof of `OverPrevErr`
(`(blkPl_518).base + 0x1fd4 → (blkPl_518).base + 0x2cfc`) on `lsProg_518 ext`
under `[LibsignalFullPlacement]`. -/
theorem overPrevErr_frozen_placed_at [LibsignalFullPlacement]
    {A : RustAlloc} (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (prevPtr errsPtr : BitVec 64) (msgVer : BitVec 32)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hver_ne : msgVer ≠ 4#32)
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1fd4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = 4#64)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
      (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       memRegion (errsPtr + 48#64) 144 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗
       sessionStateAt A (s.sp + 0x930#64) G st ∗
       pqLogLevelCellPlaced ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 60#64) 36 ∗
          memRegion (errsPtr + 96#64) 96 ∗
          memRegion (s.sp + 0xa90#64) 344 ∗
          memRegion (s.sp + 0x930#64) 344 ∗
          pqLogLevelCellPlaced ∗
          A.pool ∗
          stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem)
      (PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (spA90_344_ver_split_eq_pl s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e5 => SepWPp.exists_elim fun e4 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun ua9c => SepWPp.exists_elim fun ua98 => SepWPp.exists_elim fun ua90 => ?_
  refine bind_sepWP_fr_frame hL hfr
    (over_prev_err_seg1_cli_placed_wp ext s prevPtr ua90 msgVer ua98
      hver_ne hpc hrun hsp_align hx8 hx27)
    (by sep_focus)
    fun s1 hpc1 hrun1 hL1 hfr1 ⟨hsp1, htr1, hx19_1, hx20_1, hx27_1, hx29_1, hlr1, hvregs1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_raw_nopanic_fr
    (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack)
    hL1 hfr1 (pqxdh_log_closure_verNe_frozen_placed_ok_of_block (callerProg := lsProg_518 ext))
    hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1])
    trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hL2 hfr2 => ?_)
  have hcro2 : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem := Matched.lscro_of_frozen hfr2
  dsimp only [pqxdhLogClosurePlacedSpec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hstack_restore2 :
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore2 (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, _, _, _, _, _, _, hx27_cs2, _, hx29_cs2, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = s.readReg64 .x19 := hx19_cs2.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = s.readReg64 .x20 := hx20_cs2.trans hx20_1
  have hx27_2 : s2.readReg64 .x27 = prevPtr := hx27_cs2.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo32_pair_spA98_pl s.sp msgVer ua9c)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs144_split_eq_at48_pl errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hseg2 := over_prev_err_seg2_cli_placed_wp ext s2 prevPtr errsPtr
    0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc2 hrun2 hsp2_align hx27_2
  rw [hsp2] at hseg2
  refine bind_sepWP_cro_frame hL2 hcro2 hseg2 (by sep_focus)
    fun s3 hpc3 hrun3 hL3 hcro3 ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx20_3, hx27_3, hx29_3, hlr3, hvregs3⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (errs48_fold_ver_at48_pl errsPtr e2 e3 e4 e5 msgVer ua9c) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (spA90_344_fold_pl s.sp 0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_raw_nopanic_cro
    (spec := dropSessionStructureLocal2Spec A)
    (x := (⟨s.sp + 0x930#64, G, st⟩ : DropSessionStructureGhost))
    (φ := s3.readReg64 .x0 = s.sp + 0x930#64)
    (T := sessionStateAt A (s.sp + 0x930#64) G st ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hL3 hcro3 hDropSS3 hpc3 hrun3 hsp3_al hlr3
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp3])
    hx0_3 (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hL4 hcro4 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp3, sepConj_assoc]
  refine SepWPp.pure_elim fun htr4_3 => ?_
  have hstack_restore4 :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore4 (by sep_focus) ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, hx20_cs4, _, _, _, _, _, _, hx27_cs4, _, hx29_cs4, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = s.readReg64 .x19 := hx19_cs4.trans (hx19_3.trans hx19_2)
  have hx20_4 : s4.readReg64 .x20 = s.readReg64 .x20 := hx20_cs4.trans (hx20_3.trans hx20_2)
  have hx27_4 : s4.readReg64 .x27 = prevPtr := hx27_cs4.trans hx27_3
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hx29_cs4.trans (hx29_3.trans hx29_2)
  have hseg3 := over_prev_err_seg3_cli_placed_wp ext s4 prevPtr hpc4 hrun4 hsp4_align hx27_4
  rw [hsp4] at hseg3
  refine bind_sepWP_cro_frame hL4 hcro4 hseg3 (by sep_focus)
    fun sf hpcf hrunf hLf hcrof ⟨hspf_4, htrf_4, hx19_f, hx20_f, hx29_f, hvregsf⟩ => ?_
  have htrf : sf.trace = s0.trace := by rw [htrf_4, htr4_3, htr3_2, htr2_1, htr1, htr]
  have hx19f : sf.readReg64 .x19 = s.readReg64 .x19 := hx19_f.trans hx19_4
  have hx20f : sf.readReg64 .x20 = s.readReg64 .x20 := hx20_f.trans hx20_4
  have hx29f : sf.readReg64 .x29 = s.readReg64 .x29 := hx29_f.trans hx29_4
  have hvregsf_s : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf, hvregs_cs4, hvregs3, hvregs_cs2, hvregs1]
  refine SepWPp.done hpcf hrunf
    ⟨Entails.of_eq (by ac_rfl), hspf_4, htrf, hx19f, hx20f, hx29f, hvregsf_s, hcrof, hLf⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
