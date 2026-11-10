/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.Base
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import all Init.Data.String.Defs

/-!
# Relocatable `signal_session::public::split_signed` (Block `592`)

Verifies `splitSignedSpecPlaced` on Block `592` under `[LibsignalPlacement]`, with cross-block caller
transfer.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.SplitSigned.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

private theorem bind_sepWPp_state_p {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : let st := s; SepWPp prog ret st P Q Qp) :
    SepWPp prog ret s P Q Qp := h

private theorem bind_sepWP_state_p {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

private theorem sepWPp_pull_pure3_p {prog : Program} {ret : BitVec 64} {s : State}
    {A1 A2 : SepProp} {φ : Prop} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A1 ∗ A2 ∗ Rest) Q Qp) :
    SepWPp prog ret s (A1 ∗ A2 ∗ ⌜φ⌝ ∗ Rest) Q Qp :=
  SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWPp.pure_elim h)

private theorem sepWPp_realign_buf14_p {prog : Program} {ret : BitVec 64} {s : State}
    {A1 A2 A3 Rest : SepProp} {buf : BitVec 64} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s
      (A1 ∗ A2 ∗ A3 ∗ (buf ↦ₛ malfHead6) ∗ (∃∗ w1 : BitVec 64, (buf + 6#64) ↦₆₄ w1) ∗ Rest)
      Q Qp) :
    SepWPp prog ret s
      (A1 ∗ A2 ∗ A3 ∗ (buf ↦₆₄ malfLo) ∗ memRegion (buf + 8#64) 6 ∗ Rest) Q Qp := by
  refine SepWPp.weaken_pre ?_ h
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
      (Entails.trans (sepConj_mono_left (buf14_realign buf))
        (Entails.of_eq (sepConj_assoc _ _ _))))))

@[simp, arm64_norm]
private theorem ssg_sub_add_p (a k m : BitVec 64) : a - k + m = a - (k - m) := by
  bv_omega

@[simp, arm64_norm]
private theorem add64_sub64_64_p (a : BitVec 64) :
    (a + 64#64) - 64#64 = a := by
  bv_omega

@[simp, arm64_norm]
private theorem awc_sub64_fst_p (a : BitVec 64) :
    (AddWithCarry64 (a + 64#64) (~~~64#64) true).1 = a := by
  simp only [AddWithCarry64]
  bv_bits

@[simp, arm64_norm]
private theorem add64_add_neg64_p (a : BitVec 64) :
    (a + 64#64) + bv% (2 ^ 64 - 64) = a := by
  bv_omega

@[simp, arm64_norm]
private theorem zext32_trunc32_p (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

@[simp, arm64_norm]
private theorem append64_extract_lo_p (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[simp, arm64_norm]
private theorem append64_extract_hi_p (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[simp, arm64_norm]
private theorem sp_restore_96_p (sp0 : BitVec 64) :
    sp0 - 96#64 + 96#64 = sp0 := by
  bv_bits

private theorem cs_lt64_raw_p {u : BitVec 64} (hu : u.toNat < 64) :
    ConditionHolds CondCode.CS (AddWithCarry64 u (~~~64#64) true).2 = false := by
  simp only [ConditionHolds, AddWithCarry64]
  bv_bits

private theorem ule_lt64_false_p {u : BitVec 64} (hu : u.toNat < 64) :
    BitVec.ule 64#64 u = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

private theorem ult_lt64_true_p {u : BitVec 64} (hu : u.toNat < 64) :
    BitVec.ult u 64#64 = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

private theorem cs_ge64_raw_p {u : BitVec 64} (hu : 64 ≤ u.toNat) :
    ConditionHolds CondCode.CS (AddWithCarry64 u (~~~64#64) true).2 = true := by
  simp only [ConditionHolds, AddWithCarry64]
  bv_bits

private theorem ule_ge64_true_p {u : BitVec 64} (hu : 64 ≤ u.toNat) :
    BitVec.ule 64#64 u = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

private theorem ult_ge64_false_p {u : BitVec 64} (hu : 64 ≤ u.toNat) :
    BitVec.ult u 64#64 = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

abbrev ssgMalfSym : String := "libsignal_cli:.rodata..Lanon.67"
abbrev ssgBundleSym : String := "libsignal_cli:.rodata..Lanon.64"

theorem speAt_invalidState_intro_p (A : RustAlloc) (bundlePtr dst buf : BitVec 64)
    (hbuf : buf ≠ 0#64) :
    ((dst ↦₆₄ speWord 1) ∗
      ((dst + 8#64) ↦₆₄ 14#64) ∗
      ((dst + 16#64) ↦₆₄ buf) ∗
      ((dst + 24#64) ↦₆₄ 14#64) ∗
      A.live buf 14 1 ∗
      (buf ↦ₛ utf8 "malformed file") ∗
      ((dst + 32#64) ↦₆₄ bundlePtr) ∗
      ((dst + 40#64) ↦₆₄ 6#64) ∗
      (bundlePtr ↦ᵣ utf8 "bundle")) ⊢
      speAt A (utf8 "bundle") dst .invalidState := by
  have hlen_m : (utf8 "malformed file").length = 14 := by decide +kernel
  have hlen_b : (utf8 "bundle").length = 6 := by decide +kernel
  have hvec : (((dst + 8#64) ↦₆₄ 14#64) ∗ ((dst + 16#64) ↦₆₄ buf) ∗
      ((dst + 24#64) ↦₆₄ 14#64) ∗ A.live buf 14 1 ∗ (buf ↦ₛ utf8 "malformed file")) ⊢
      (∃∗ bs : List (BitVec 8), vecU8 A (dst + 8#64) bs) := by
    refine Entails.sepExists_right (utf8 "malformed file") ?_
    unfold vecU8
    refine Entails.sepExists_right 14#64 (Entails.sepExists_right buf ?_)
    have h16 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
    have h24 : dst + 8#64 + 16#64 = dst + 24#64 := by bv_omega
    have hne : ((14#64 : BitVec 64) = 0) = False := eq_false (by decide)
    have h14 : (14#64 : BitVec 64).toNat = 14 := rfl
    simp only [vecU8At, vecHeader, hlen_m, hne, ↓reduceIte, h14, Nat.sub_self,
      memRegion_zero, sepConj_emp, h16, h24]
    rw [show (14 ≤ 14 ∧ 14 < 2 ^ 63 ∧ buf ≠ 0) = True from
      eq_true ⟨by decide, by decide, hbuf⟩, pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  have hstr : (((dst + 32#64) ↦₆₄ bundlePtr) ∗
      ((dst + 40#64) ↦₆₄ 6#64) ∗
      (bundlePtr ↦ᵣ utf8 "bundle")) ⊢
      strRefAt (dst + 32#64) (utf8 "bundle") := by
    unfold strRefAt
    refine Entails.sepExists_right bundlePtr ?_
    have h40 : dst + 32#64 + 8#64 = dst + 40#64 := by bv_omega
    rw [hlen_b, h40]
    exact Entails.of_eq (by ac_rfl)
  dsimp only [speAt]
  have hoff8 : asm64% spePayloadOff = 8#64 := rfl
  have hoff32 : asm64% speInvalidStateFnOff = 32#64 := rfl
  rw [hoff8, hoff32]
  have hgroup :
      ((dst ↦₆₄ speWord 1) ∗ ((dst + 8#64) ↦₆₄ 14#64) ∗ ((dst + 16#64) ↦₆₄ buf) ∗
        ((dst + 24#64) ↦₆₄ 14#64) ∗ A.live buf 14 1 ∗ (buf ↦ₛ utf8 "malformed file") ∗
        ((dst + 32#64) ↦₆₄ bundlePtr) ∗
        ((dst + 40#64) ↦₆₄ 6#64) ∗
        (bundlePtr ↦ᵣ utf8 "bundle")) =
      ((dst ↦₆₄ speWord 1) ∗
        (((dst + 8#64) ↦₆₄ 14#64) ∗ ((dst + 16#64) ↦₆₄ buf) ∗
          ((dst + 24#64) ↦₆₄ 14#64) ∗ A.live buf 14 1 ∗ (buf ↦ₛ utf8 "malformed file")) ∗
        (((dst + 32#64) ↦₆₄ bundlePtr) ∗
          ((dst + 40#64) ↦₆₄ 6#64) ∗
          (bundlePtr ↦ᵣ utf8 "bundle"))) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono hvec hstr)

def ssgMalfRO_p [LibsignalPlacement] : SepProp :=
  ((lsρ ssgMalfSym) ↦₆₄ᵣ malfLo) ∗
  (((lsρ ssgMalfSym) + 8#64) ↦ᵣ malfTail6) ∗
  ((lsρ ssgMalfSym) ↦ᵣ malfHead6) ∗
  (((lsρ ssgMalfSym) + 6#64) ↦₆₄ᵣ malfHi)

theorem ssgMalfRO_bundle_intro_p [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ssgMalfRO_p ∗ ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗ P := by
  have h1 := lsro_intro_chk hro (sym := ssgBundleSym) (bs := utf8 "bundle") (by decide +kernel) hP
  have h2 := lsro_intro_chk hro (sym := ssgMalfSym) (bs := utf8 "malformed file") (by decide +kernel) h1
  rw [pointsToBytesRO_malf_6_8] at h2
  have h3 := lsro_intro_chk hro (sym := ssgMalfSym) (bs := utf8 "malformed file") (by decide +kernel) h2
  rw [pointsToBytesRO_malf_8_6] at h3
  unfold ssgMalfRO_p lsρ
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h3

theorem ssg_call_lscro [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {α : Type} {callee_pc ret_pc : BitVec 64} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
      allocFailedIn s sf ∧ s.trace <+: sf.trace := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hnext : ∀ sf : State,
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (SsgPanicAllow s0)) :
    SepWPp prog ret s P Q (SsgPanicAllow s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) :=
    satisfies_lscro_pre hcrl hm_pre
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm (hcrl.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hpost
    have halloc := hpanic sm (F ∗ R) hpan hpost
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      ssgPanicAllow_of_eq halloc0⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact (hoom sm (F ∗ R) hoom_s hpost).elim

/-! ## `splitId file = none`: 48-Byte `Err` Copy -/

theorem step_err_copy_path_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {subStk stk : Nat}
    (hstk : 96 + subStk ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8))
    (hnone : splitId file = none)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hpc : s.pc = (blkPl_592).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hcs : SsgUpperSaved s0 s) :
    SepWPp (lsProg_592 H) (s0.readReg64 Reg.lr) s
      (ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        splitIdResultAt A (s0.sp - 96#64) fp file ∗
        ssgSavedRegs s0.sp s0 ∗
        stackAt (s0.sp - 96#64) subStk ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp file ∗
        memRegion retAddr 48 ∗
        A.pool)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ ssgMalfRO_p ∗
          (((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
            (⌜sf.trace = s0.trace⌝ ∗
              splitSignedResultAt A retAddr fp file ∗
              SpqrV1.ChainProofs.bytesAt ro fp file ∗
              stackAt s0.sp stk ∗ A.pool))))
      (SsgPanicAllow s0) := by
  have hsigned : splitSigned file = none := by
    simp only [splitSigned, hnone]
  have hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal
  rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
  dsimp only [splitIdResultAt]
  rw [hnone, speAt_invalidState_copy_open A (s0.sp - 96#64), ret48_open_err retAddr]
  unfold ssgSavedRegs
  simp only [pointsTo64_split32 (retAddr + 8#64), BitVec.add_assoc, BitVec.reduceAdd,
    ssg_sub_add_p, BitVec.reduceSub, ← speWord1_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
    SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
    SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
    SepWPp.exists_elim fun strPtr => SepWPp.exists_elim fun bs =>
    SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply bind_sepWP_state_p; intro sf
  apply SepWP.done (by simp only [sf, arm64_norm, *]) (by simp only [sf, arm64_norm, *])
  refine ⟨by simp only [sf, arm64_norm, *], ?_, ?_⟩
  · refine ⟨by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs⟩
  · have htrf : sf.trace = s0.trace := by simp only [sf, arm64_norm, htr]
    rw [htrf, eq_self, pure_true, emp_sepConj]
    dsimp only [splitSignedResultAt]
    rw [hsigned]
    have hspe_dst :
        ((retAddr ↦₆₄ speWord 1) ∗
          ((retAddr + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((retAddr + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((retAddr + 16#64) ↦₆₄ ptr) ∗
          ((retAddr + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((retAddr + 32#64) ↦₆₄ strPtr) ∗
          ((retAddr + 40#64) ↦₆₄ 6#64) ∗
          speVecHeap A bs cap ptr ∗
          (strPtr ↦ᵣ utf8 "bundle")) ⊢
        speAt A (utf8 "bundle") retAddr .invalidState := by
      rw [speAt_invalidState_copy_open A retAddr]
      exact Entails.sepExists_right strPtr (Entails.sepExists_right bs
        (Entails.sepExists_right cap (Entails.sepExists_right ptr
          (Entails.of_eq (by ac_rfl)))))
    have hcells_src :
        (((s0.sp - 96#64) ↦₆₄ speWord 1) ∗
          ((s0.sp - 88#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s0.sp - 84#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s0.sp - 80#64) ↦₆₄ ptr) ∗
          ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((s0.sp - 64#64) ↦₆₄ strPtr) ∗
          ((s0.sp - 56#64) ↦₆₄ 6#64)) ⊢
        cells (s0.sp - 96#64) 6 := by
      refine Entails.trans ?_
        (cells6_of_words s0.sp (speWord 1) cap ptr (BitVec.ofNat 64 bs.length) strPtr 6#64)
      rw [pointsTo64_split32 (s0.sp - 88#64) cap]
      simp only [ssg_sub_add_p, BitVec.reduceSub]
      exact Entails.of_eq (by ac_rfl)
    have hstk_pack :
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
          stackAt (s0.sp - 96#64) subStk ∗
          (((s0.sp - 96#64) ↦₆₄ speWord 1) ∗
            ((s0.sp - 88#64) ↦₃₂ cap.extractLsb' 0 32) ∗
            ((s0.sp - 84#64) ↦₃₂ cap.extractLsb' 32 32) ∗
            ((s0.sp - 80#64) ↦₆₄ ptr) ∗
            ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ((s0.sp - 64#64) ↦₆₄ strPtr) ∗
            ((s0.sp - 56#64) ↦₆₄ 6#64)) ∗
          ssgSavedRegs s0.sp s0) ⊢
        stackAt s0.sp stk :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcells_src)))
        (stackAt_ssg_pack_cells s0.sp subStk stk s0 hstk hstkle)
    rw [speWord1_eq]
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono hspe_dst
        (sepConj_mono_left
          (Q := ssgMalfRO_p ∗ ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗ A.pool)
          hstk_pack)) ?_)
    · unfold ssgSavedRegs
      simp only [sepConj_assoc]
      exact Entails.of_eq (by ac_rfl)
    · generalize stackAt s0.sp stk = topStk
      exact Entails.of_eq (by ac_rfl)

/-! ## `rest.length < 64`: Construct `"malformed file"` Error -/

theorem step_short_err_path_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {subStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hsub : dropSpeStackX ≤ subStk)
    (hstk : 96 + subStk ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8)) (id : BitVec 32) (rest : List (BitVec 8))
    (hsid : splitId file = some (id, rest))
    (hlt64 : rest.length < 64)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_592).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hcs : SsgUpperSaved s0 s) :
    SepWPp (lsProg_592 H) (s0.readReg64 Reg.lr) s
      (ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        splitIdResultAt A (s0.sp - 96#64) fp file ∗
        ssgSavedRegs s0.sp s0 ∗
        stackAt (s0.sp - 96#64) subStk ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp file ∗
        memRegion retAddr 48 ∗
        A.pool)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ ssgMalfRO_p ∗
          (⌜sf.trace = s0.trace⌝ ∗
            splitSignedResultAt A retAddr fp file ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗
            stackAt s0.sp stk ∗ A.pool)))
      (SsgPanicAllow s0) := by
  have hsigned : splitSigned file = none := by
    simp only [splitSigned, hsid, show ¬ (64 ≤ rest.length) by omega, ↓reduceIte]
  have hshim : subroutine_ok (lsProg_592 H) (lsρ lsRustNoAllocShimSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec extHookStack)) :=
    shim_lscro_of_cli (callerProg := lsProg_592 H) (stk := extHookStack) hC
  have halloc : subroutine_ok (lsProg_592 H) (lsρ lsRustAllocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)) :=
    alloc_lscro_of_cli (callerProg := lsProg_592 H) hC
  have hpanic : (lsProg_592 H).externAt? (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") =
      some Rust.panicked :=
    ls_panicAt_of_cliPanic hpan
  clear hC hpan
  have hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal
  have hlt_bv : (BitVec.ofNat 64 rest.length).toNat < 64 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hlt64
  have hcs_raw := cs_lt64_raw_p hlt_bv
  have hcs_norm : ConditionHolds CondCode.CS
      (AddWithCarry64 (BitVec.ofNat 64 rest.length) (bv% (2 ^ 64 - 65)) true).2 = false :=
    hcs_raw
  have hule := ule_lt64_false_p hlt_bv
  have hult := ult_lt64_true_p hlt_bv
  have _ := And.intro hcs_raw (And.intro hcs_norm (And.intro hule hult))
  dsimp only [splitIdResultAt]
  rw [hsid, ← splitOkTag_eq, memRegion16_open ((s0.sp - 96#64) + 32#64)]
  simp only [ssg_sub_add_p, BitVec.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWPp.exists_elim fun z1 => SepWPp.exists_elim fun z0 => ?_
  apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsρ lsRustNoAllocShimSymCli)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcrl1
  apply bind_sepWPp_state_p; intro s_sh
  have hal_sh : s_sh.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_sh, arm64_norm, hsp])
  have hcs_sh : SsgUpperSaved s0 s_sh := by
    rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
    simp only [s_sh, SsgUpperSaved, arm64_norm, *]
  refine ssg_call_lscro () hshim hcrl1
    (by simp only [s_sh, arm64_norm, htr])
    (by simp only [s_sh, arm64_norm, *])
    (by simp only [s_sh, arm64_norm, *])
    hal_sh
    (ret_pc := (blkPl_592).base + 64#64)
    (by simp only [s_sh, arm64_norm, *])
    (F := ssgMalfRO_p ∗
      ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
      ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
      ((s0.sp - 88#64) ↦₃₂ id) ∗
      memRegion (s0.sp - 84#64) 4 ∗
      ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
      ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      ((s0.sp - 64#64) ↦₆₄ z0) ∗
      ((s0.sp - 56#64) ↦₆₄ z1) ∗
      ssgSavedRegs s0.sp s0 ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
      SpqrV1.ChainProofs.bytesAt ro fp file ∗
      memRegion retAddr 48 ∗ A.pool)
    ?_ (hnext := ?_)
  · rw [stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega),
      stackAt_hook_split (s0.sp - 96#64)]
    dsimp only [withStack, sessionShimSpec]
    have hsp_eq : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
    rw [hsp_eq]
    generalize dropSpeStackX = dsz
    generalize extHookStack = hsz
    exact Entails.of_eq (by ac_rfl)
  · intro s_after_sh hcrl2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [withStack, sessionShimSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr2 => ?_
    have hx19_2 : s_after_sh.readReg64 .x19 = retAddr := by
      rw [hcsp2.1]; simp only [s_sh, arm64_norm, hx19]
    have hsp2' : s_after_sh.sp = s0.sp - 96#64 := by
      rw [hsp2]; simp only [s_sh, arm64_norm, hsp]
    clear hsp2
    have htr2' : s_after_sh.trace = s0.trace := by
      rw [htr2]; simp only [s_sh, arm64_norm, htr]
    have hcs2 : SsgUpperSaved s0 s_after_sh := hcs_sh.trans_calleeSaved hcsp2
    apply StoreKit.sepWPp_seq_lscro hcrl2 (mid := lsρ lsRustAllocSymCli)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl3
    apply bind_sepWPp_state_p; intro s_al
    have hal_al : s_al.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_al, arm64_norm, hsp2'])
    have hcs_al : SsgUpperSaved s0 s_al := by
      rcases hcs2 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
      simp only [s_al, SsgUpperSaved, arm64_norm, *]
    have hlay : LayoutOk 14 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
    refine ssg_call_lscro (14, 1) halloc hcrl3
      (by simp only [s_al, arm64_norm, htr2'])
      (by simp only [s_al, arm64_norm, *])
      (by simp only [s_al, arm64_norm, *])
      hal_al
      (ret_pc := (blkPl_592).base + 76#64)
      (by simp only [s_al, arm64_norm, *])
      (F := ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
        ((s0.sp - 88#64) ↦₃₂ id) ∗
        memRegion (s0.sp - 84#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
        ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
        ((s0.sp - 64#64) ↦₆₄ z0) ∗
        ((s0.sp - 56#64) ↦₆₄ z1) ∗
        ssgSavedRegs s0.sp s0 ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp file ∗
        memRegion retAddr 48)
      ?_ (hnext := ?_)
    · dsimp only [rustAllocSpecWithStack]
      have hpure_al :
          ((s_al.readReg64 .x0).toNat = 14 ∧ (s_al.readReg64 .x1).toNat = 1 ∧ LayoutOk 14 1) = True :=
        eq_true ⟨by simp only [s_al, arm64_norm], by simp only [s_al, arm64_norm], hlay⟩
      have hsp_eq1 : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
      have hsp_eq2 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
      rw [hpure_al, pure_true, emp_sepConj, hsp_eq1, hsp_eq2]
      generalize dropSpeStackX = dsz
      generalize extHookStack = hsz
      exact Entails.of_eq (by ac_rfl)
    · intro s_after_al hcrl4 hpc4 hrun4 hsp4 hcsp4
      let _ := hcrl4
      dsimp only [rustAllocSpecWithStack]
      have hx19_4 : s_after_al.readReg64 .x19 = retAddr := by
        rw [hcsp4.1]; simp only [s_al, arm64_norm, hx19_2]
      have hsp4' : s_after_al.sp = s0.sp - 96#64 := by
        rw [hsp4]; simp only [s_al, arm64_norm, hsp2']
      clear hsp4
      have hal4 : s_after_al.spAligned = true := sp_sub_96_spAligned hal0 hsp4'
      let _ := hal4
      have hcs4 : SsgUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved hcsp4
      by_cases hnull : s_after_al.readReg64 .x0 = 0
      ·
        have hnull64 : s_after_al.readReg64 .x0 = 0#64 := hnull
        let _ := hnull64
        simp only [hnull, ↓reduceIte, sepConj_assoc]
        refine sepWPp_pull_pure3_p fun htr_oom => ?_
        have htr_al : s_al.trace = s0.trace := by simp only [s_al, arm64_norm, htr2']
        apply SepWPp.of_sepWP
          (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.panic (by simp only [arm64_norm, *])
          (by simpa only [arm64_norm] using hpanic)
          (ssgPanicAllow_of_eq
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htr_oom, htr_al])))
      ·
        set buf := s_after_al.readReg64 .x0 with hbuf_def
        let _ := hbuf_def
        have hptr_ne : buf ≠ 0#64 := hnull
        have hptr_beq : (buf == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
        have hptr_bne : (buf != 0#64) = true := bne_iff_ne.mpr hptr_ne
        have _ := And.intro hptr_beq hptr_bne
        simp only [hnull, ↓reduceIte]
        have hw88 : (((s0.sp - 88#64) ↦₃₂ id) ∗ memRegion (s0.sp - 84#64) 4) ⊢
            ∃∗ w88 : BitVec 64, (s0.sp - 88#64) ↦₆₄ w88 := by
          have ha84 : (s0.sp - 88#64) + 4#64 = s0.sp - 84#64 := by bv_omega
          simpa only [ha84] using half32_pad_entails_cell64 (s0.sp - 88#64) id
        refine SepWPp.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
              (sepConj_mono_left hw88)))))) ?_
        rw [buf14_open_lo buf, ret48_open_err retAddr]
        unfold ssgMalfRO_p ssgSavedRegs
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
          SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
          SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
          SepWPp.exists_elim fun w88 => SepWPp.exists_elim fun w0 => ?_
        refine sepWPp_pull_pure3_p fun ⟨_, htr_ok⟩ => ?_
        have htr4' : s_after_al.trace = s0.trace := by
          rw [htr_ok]; simp only [s_al, arm64_norm, htr2']
        rcases hcs4 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
        apply SepWPp.of_sepWP (mid := (blkPl_592).base + 116#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have _ := hx19_4
        apply sepWPp_realign_buf14_p
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun w1 => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        apply bind_sepWP_state_p; intro sf
        apply SepWP.done (by simp only [sf, arm64_norm, *]) (by simp only [sf, arm64_norm, *])
        refine ⟨by simp only [sf, arm64_norm, *], ?_, ?_⟩
        · refine ⟨by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs⟩
        · have htrf : sf.trace = s0.trace := by simp only [sf, arm64_norm, htr4']
          rw [htrf, eq_self, pure_true, emp_sepConj]
          dsimp only [splitSignedResultAt]
          rw [hsigned]
          have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
          have hbuf_pack : ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) =
              (buf ↦ₛ utf8 "malformed file") := buf14_close buf
          have hcells_back :
              (((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗ ((s0.sp - 88#64) ↦₆₄ w88) ∗
                ((s0.sp - 80#64) ↦₆₄ buf) ∗ ((s0.sp - 72#64) ↦₆₄ 14#64) ∗
                ((s0.sp - 64#64) ↦₆₄ (lsρ ssgBundleSym)) ∗
                ((s0.sp - 56#64) ↦₆₄ 6#64)) ⊢ cells (s0.sp - 96#64) 6 :=
            cells6_of_words s0.sp (bv% (2 ^ 64 - 2)) w88 buf 14#64
              (lsρ ssgBundleSym) 6#64
          have hspe_pack :
              ((retAddr ↦₆₄ speWord 1) ∗
                ((retAddr + 8#64) ↦₆₄ 14#64) ∗
                ((retAddr + 16#64) ↦₆₄ buf) ∗
                ((retAddr + 24#64) ↦₆₄ 14#64) ∗
                A.live buf 14 1 ∗
                ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) ∗
                ((retAddr + 32#64) ↦₆₄ (lsρ ssgBundleSym)) ∗
                ((retAddr + 40#64) ↦₆₄ 6#64) ∗
                ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle")) ⊢
              speAt A (utf8 "bundle") retAddr .invalidState := by
            rw [hbuf_pack]
            exact speAt_invalidState_intro_p A (lsρ ssgBundleSym) retAddr buf hptr_ne
          have hstk_pack :
              (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
                (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                  (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
                    stackAt (s0.sp - 96#64) extHookStack)) ∗
                (((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗ ((s0.sp - 88#64) ↦₆₄ w88) ∗
                  ((s0.sp - 80#64) ↦₆₄ buf) ∗ ((s0.sp - 72#64) ↦₆₄ 14#64) ∗
                  ((s0.sp - 64#64) ↦₆₄ (lsρ ssgBundleSym)) ∗
                  ((s0.sp - 56#64) ↦₆₄ 6#64)) ∗
                ssgSavedRegs s0.sp s0) ⊢
              stackAt s0.sp stk := by
            rw [← stackAt_hook_split (s0.sp - 96#64),
              ← stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega)]
            exact Entails.trans
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcells_back)))
              (stackAt_ssg_pack_cells s0.sp subStk stk s0 hstk hstkle)
          rw [hsp_al0, speWord1_eq]
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono hspe_pack
              (sepConj_mono_left
                (Q := ssgMalfRO_p ∗ SpqrV1.ChainProofs.bytesAt ro fp file ∗ A.pool)
                hstk_pack)) ?_)
          · unfold ssgMalfRO_p ssgSavedRegs lsρ
            dsimp only [buf, Reg.x0, blkPl_592, ssgBundleSym, ssgMalfSym]
            simp only [sepConj_assoc]
            generalize dropSpeStackX = dsz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
          · unfold ssgMalfRO_p lsρ
            dsimp only [blkPl_592, ssgBundleSym, ssgMalfSym]
            simp only [sepConj_assoc]
            generalize stackAt s0.sp stk = topStk
            exact Entails.of_eq (by ac_rfl)

/-! ## `64 ≤ rest.length`: Drop Eager `SignalProtocolError` and Write `Ok` -/

theorem step_ok_signed_path_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {subStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hDrop : subroutine_ok (lsProg_592 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX A)))
    (hsub : dropSpeStackX ≤ subStk)
    (hstk : 96 + subStk ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8)) (id : BitVec 32) (rest : List (BitVec 8))
    (hsid : splitId file = some (id, rest))
    (hrest_lt64 : rest.length < 2 ^ 64)
    (hge64 : 64 ≤ rest.length)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_592).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hcs : SsgUpperSaved s0 s) :
    SepWPp (lsProg_592 H) (s0.readReg64 Reg.lr) s
      (ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        splitIdResultAt A (s0.sp - 96#64) fp file ∗
        ssgSavedRegs s0.sp s0 ∗
        stackAt (s0.sp - 96#64) subStk ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp file ∗
        memRegion retAddr 48 ∗
        A.pool)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ ssgMalfRO_p ∗
          (⌜sf.trace = s0.trace⌝ ∗
            splitSignedResultAt A retAddr fp file ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗
            stackAt s0.sp stk ∗ A.pool)))
      (SsgPanicAllow s0) := by
  have hsigned : splitSigned file =
      some (id, rest.take (rest.length - 64), rest.drop (rest.length - 64)) := by
    simp only [splitSigned, hsid, hge64, ↓reduceIte]
  have hkey_len : (rest.take (rest.length - 64)).length = rest.length - 64 := by
    rw [List.length_take]
    omega
  have hrest_bv : BitVec.ofNat 64 rest.length = BitVec.ofNat 64 (rest.length - 64) + 64#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hge_bv : 64 ≤ (BitVec.ofNat 64 (rest.length - 64) + 64#64).toNat := by
    rw [← hrest_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrest_lt64]
    exact hge64
  have hcs_raw := cs_ge64_raw_p hge_bv
  have hcs_norm : ConditionHolds CondCode.CS
      (AddWithCarry64 (BitVec.ofNat 64 (rest.length - 64) + 64#64) (bv% (2 ^ 64 - 65)) true).2 = true :=
    hcs_raw
  have hule := ule_ge64_true_p hge_bv
  have hult := ult_ge64_false_p hge_bv
  have _ := And.intro hcs_raw (And.intro hcs_norm (And.intro hule hult))
  have hshim : subroutine_ok (lsProg_592 H) (lsρ lsRustNoAllocShimSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec extHookStack)) :=
    shim_lscro_of_cli (callerProg := lsProg_592 H) (stk := extHookStack) hC
  have halloc : subroutine_ok (lsProg_592 H) (lsρ lsRustAllocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)) :=
    alloc_lscro_of_cli (callerProg := lsProg_592 H) hC
  have hpanic : (lsProg_592 H).externAt? (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") =
      some Rust.panicked :=
    ls_panicAt_of_cliPanic hpan
  clear hC hpan
  have hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal
  dsimp only [splitIdResultAt]
  rw [hsid]
  dsimp only
  rw [← splitOkTag_eq, hrest_bv, memRegion16_open ((s0.sp - 96#64) + 32#64)]
  simp only [ssg_sub_add_p, BitVec.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWPp.exists_elim fun z1 => SepWPp.exists_elim fun z0 => ?_
  apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsρ lsRustNoAllocShimSymCli)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcrl1
  apply bind_sepWPp_state_p; intro s_sh
  have hal_sh : s_sh.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_sh, arm64_norm, hsp])
  have hcs_sh : SsgUpperSaved s0 s_sh := by
    rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
    simp only [s_sh, SsgUpperSaved, arm64_norm, *]
  refine ssg_call_lscro () hshim hcrl1
    (by simp only [s_sh, arm64_norm, htr])
    (by simp only [s_sh, arm64_norm, *])
    (by simp only [s_sh, arm64_norm, *])
    hal_sh
    (ret_pc := (blkPl_592).base + 220#64)
    (by simp only [s_sh, arm64_norm, *])
    (F := ssgMalfRO_p ∗
      ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
      ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
      ((s0.sp - 88#64) ↦₃₂ id) ∗
      memRegion (s0.sp - 84#64) 4 ∗
      ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
      ((s0.sp - 72#64) ↦₆₄ (BitVec.ofNat 64 (rest.length - 64) + 64#64)) ∗
      ((s0.sp - 64#64) ↦₆₄ z0) ∗
      ((s0.sp - 56#64) ↦₆₄ z1) ∗
      ssgSavedRegs s0.sp s0 ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
      SpqrV1.ChainProofs.bytesAt ro fp file ∗
      memRegion retAddr 48 ∗ A.pool)
    ?_ (hnext := ?_)
  · rw [stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega),
      stackAt_hook_split (s0.sp - 96#64)]
    dsimp only [withStack, sessionShimSpec]
    have hsp_eq : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
    rw [hsp_eq]
    generalize dropSpeStackX = dsz
    generalize extHookStack = hsz
    exact Entails.of_eq (by ac_rfl)
  · intro s_after_sh hcrl2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [withStack, sessionShimSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr2 => ?_
    have hx19_2 : s_after_sh.readReg64 .x19 = retAddr := by
      rw [hcsp2.1]; simp only [s_sh, arm64_norm, hx19]
    have hx20_2 : s_after_sh.readReg64 .x20 = id.zeroExtend 64 := by
      rw [hcsp2.2.1]; simp only [s_sh, arm64_norm]
    have hx21_2 : s_after_sh.readReg64 .x21 = fp + 4#64 := by
      rw [hcsp2.2.2.1]; simp only [s_sh, arm64_norm]
    have hx22_2 : s_after_sh.readReg64 .x22 = BitVec.ofNat 64 (rest.length - 64) := by
      rw [hcsp2.2.2.2.1]; simp only [s_sh, arm64_norm]
    have hsp2' : s_after_sh.sp = s0.sp - 96#64 := by
      rw [hsp2]; simp only [s_sh, arm64_norm, hsp]
    clear hsp2
    have htr2' : s_after_sh.trace = s0.trace := by
      rw [htr2]; simp only [s_sh, arm64_norm, htr]
    have hcs2 : SsgUpperSaved s0 s_after_sh := hcs_sh.trans_calleeSaved hcsp2
    apply StoreKit.sepWPp_seq_lscro hcrl2 (mid := lsρ lsRustAllocSymCli)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl3
    apply bind_sepWPp_state_p; intro s_al
    have hal_al : s_al.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_al, arm64_norm, hsp2'])
    have hcs_al : SsgUpperSaved s0 s_al := by
      rcases hcs2 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
      simp only [s_al, SsgUpperSaved, arm64_norm, *]
    have hlay : LayoutOk 14 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
    refine ssg_call_lscro (14, 1) halloc hcrl3
      (by simp only [s_al, arm64_norm, htr2'])
      (by simp only [s_al, arm64_norm, *])
      (by simp only [s_al, arm64_norm, *])
      hal_al
      (ret_pc := (blkPl_592).base + 232#64)
      (by simp only [s_al, arm64_norm, *])
      (F := ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
        ((s0.sp - 88#64) ↦₃₂ id) ∗
        memRegion (s0.sp - 84#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
        ((s0.sp - 72#64) ↦₆₄ (BitVec.ofNat 64 (rest.length - 64) + 64#64)) ∗
        ((s0.sp - 64#64) ↦₆₄ z0) ∗
        ((s0.sp - 56#64) ↦₆₄ z1) ∗
        ssgSavedRegs s0.sp s0 ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp file ∗
        memRegion retAddr 48)
      ?_ (hnext := ?_)
    · dsimp only [rustAllocSpecWithStack]
      have hpure_al :
          ((s_al.readReg64 .x0).toNat = 14 ∧ (s_al.readReg64 .x1).toNat = 1 ∧ LayoutOk 14 1) = True :=
        eq_true ⟨by simp only [s_al, arm64_norm], by simp only [s_al, arm64_norm], hlay⟩
      have hsp_eq1 : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
      have hsp_eq2 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
      rw [hpure_al, pure_true, emp_sepConj, hsp_eq1, hsp_eq2]
      generalize dropSpeStackX = dsz
      generalize extHookStack = hsz
      exact Entails.of_eq (by ac_rfl)
    · intro s_after_al hcrl4 hpc4 hrun4 hsp4 hcsp4
      dsimp only [rustAllocSpecWithStack]
      have hx19_4 : s_after_al.readReg64 .x19 = retAddr := by
        rw [hcsp4.1]; simp only [s_al, arm64_norm, hx19_2]
      have hx20_4 : s_after_al.readReg64 .x20 = id.zeroExtend 64 := by
        rw [hcsp4.2.1]; simp only [s_al, arm64_norm, hx20_2]
      have hx21_4 : s_after_al.readReg64 .x21 = fp + 4#64 := by
        rw [hcsp4.2.2.1]; simp only [s_al, arm64_norm, hx21_2]
      have hx22_4 : s_after_al.readReg64 .x22 = BitVec.ofNat 64 (rest.length - 64) := by
        rw [hcsp4.2.2.2.1]; simp only [s_al, arm64_norm, hx22_2]
      have hsp4' : s_after_al.sp = s0.sp - 96#64 := by
        rw [hsp4]; simp only [s_al, arm64_norm, hsp2']
      clear hsp4
      have hal4 : s_after_al.spAligned = true := sp_sub_96_spAligned hal0 hsp4'
      let _ := hal4
      have hcs4 : SsgUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved hcsp4
      by_cases hnull : s_after_al.readReg64 .x0 = 0
      ·
        have hnull64 : s_after_al.readReg64 .x0 = 0#64 := hnull
        let _ := hnull64
        simp only [hnull, ↓reduceIte, sepConj_assoc]
        refine sepWPp_pull_pure3_p fun htr_oom => ?_
        have htr_al : s_al.trace = s0.trace := by simp only [s_al, arm64_norm, htr2']
        apply SepWPp.of_sepWP
          (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.panic (by simp only [arm64_norm, *])
          (by simpa only [arm64_norm] using hpanic)
          (ssgPanicAllow_of_eq
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htr_oom, htr_al])))
      ·
        set buf := s_after_al.readReg64 .x0 with hbuf_def
        let _ := hbuf_def
        have hptr_ne : buf ≠ 0#64 := hnull
        have hptr_beq : (buf == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
        have hptr_bne : (buf != 0#64) = true := bne_iff_ne.mpr hptr_ne
        have _ := And.intro hptr_beq hptr_bne
        simp only [hnull, ↓reduceIte]
        have hw88 : (((s0.sp - 88#64) ↦₃₂ id) ∗ memRegion (s0.sp - 84#64) 4) ⊢
            ∃∗ w88 : BitVec 64, (s0.sp - 88#64) ↦₆₄ w88 := by
          have ha84 : (s0.sp - 88#64) + 4#64 = s0.sp - 84#64 := by bv_omega
          simpa only [ha84] using half32_pad_entails_cell64 (s0.sp - 88#64) id
        refine SepWPp.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
              (sepConj_mono_left hw88)))))) ?_
        rw [buf14_open_lo buf]
        conv =>
          arg 4
          unfold ssgMalfRO_p
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun w88 => SepWPp.exists_elim fun w0 => ?_
        refine sepWPp_pull_pure3_p fun ⟨_, htr_ok⟩ => ?_
        have htr4' : s_after_al.trace = s0.trace := by
          rw [htr_ok]; simp only [s_al, arm64_norm, htr2']
        apply StoreKit.sepWPp_seq_lscro hcrl4 (mid := (blkPl_592).base + 256#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcrl5
        apply sepWPp_realign_buf14_p
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun w1 => ?_
        apply StoreKit.sepWPp_seq_lscro hcrl5 (mid := lsmpl.base 553)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcrl6
        apply bind_sepWPp_state_p; intro s_dr
        have hal_dr : s_dr.spAligned = true :=
          sp_sub_96_spAligned hal0 (by simp only [s_dr, arm64_norm, hsp4'])
        have hcs_dr : SsgUpperSaved s0 s_dr := by
          rcases hcs4 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
          simp only [s_dr, SsgUpperSaved, arm64_norm, *]
        refine ssg_call_lscro ⟨s0.sp - 96#64, utf8 "bundle", .invalidState⟩ hDrop hcrl6
          (by simp only [s_dr, arm64_norm, htr4'])
          (by simp only [s_dr, arm64_norm, *])
          (by simp only [s_dr, arm64_norm, *])
          hal_dr
          (ret_pc := (blkPl_592).base + 300#64)
          (by simp only [s_dr, arm64_norm, *])
          (F := ssgMalfRO_p ∗
            ssgSavedRegs s0.sp s0 ∗
            memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗
            memRegion retAddr 48)
          ?_ (hnext := ?_)
        · dsimp only [dropSpeSpecX]
          have hx0_dr : (s_dr.readReg64 .x0 = s0.sp - 96#64) = True :=
            eq_true (by simp only [s_dr, arm64_norm])
          have hsp_dr : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, arm64_norm, hsp4']
          have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
          rw [hx0_dr, pure_true, emp_sepConj, hsp_dr, stackAt_hook_split (s0.sp - 96#64), hsp_al0]
          unfold ssgMalfRO_p
          rw [speWord1_eq]
          have hbuf_pack : ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) =
              (buf ↦ₛ utf8 "malformed file") := buf14_close buf
          have hspe_pack :
              (((s0.sp - 96#64) ↦₆₄ speWord 1) ∗
                (((s0.sp - 96#64) + 8#64) ↦₆₄ 14#64) ∗
                (((s0.sp - 96#64) + 16#64) ↦₆₄ buf) ∗
                (((s0.sp - 96#64) + 24#64) ↦₆₄ 14#64) ∗
                A.live buf 14 1 ∗
                ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) ∗
                (((s0.sp - 96#64) + 32#64) ↦₆₄ (lsρ ssgBundleSym)) ∗
                (((s0.sp - 96#64) + 40#64) ↦₆₄ 6#64) ∗
                ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle")) ⊢
              speAt A (utf8 "bundle") (s0.sp - 96#64) .invalidState := by
            rw [hbuf_pack]
            exact speAt_invalidState_intro_p A (lsρ ssgBundleSym) (s0.sp - 96#64) buf hptr_ne
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q :=
              A.pool ∗
                memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
                stackAt (s0.sp - 96#64) extHookStack ∗
                ssgMalfRO_p ∗
                ssgSavedRegs s0.sp s0 ∗
                memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
                SpqrV1.ChainProofs.bytesAt ro fp file ∗
                memRegion retAddr 48) hspe_pack) ?_)
          · unfold ssgMalfRO_p lsρ
            dsimp only [buf, Reg.x0, blkPl_592, ssgBundleSym, ssgMalfSym]
            simp only [ssg_sub_add_p, BitVec.reduceSub, sepConj_assoc]
            generalize dropSpeStackX = dsz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
          · unfold ssgMalfRO_p lsρ
            dsimp only [blkPl_592, ssgBundleSym, ssgMalfSym]
            simp only [sepConj_assoc]
            generalize dropSpeStackX = dsz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
        ·
          intro s_ep hcrl7 hpc7 hrun7 hsp7 hcsp7
          let _ := hcrl7
          dsimp only [dropSpeSpecX]
          rw [sepConj_assoc]
          refine SepWPp.pure_elim fun htr7 => ?_
          have hx19_7 : s_ep.readReg64 .x19 = retAddr := by
            rw [hcsp7.1]; simp only [s_dr, arm64_norm, hx19_4]
          have hx20_7 : s_ep.readReg64 .x20 = id.zeroExtend 64 := by
            rw [hcsp7.2.1]; simp only [s_dr, arm64_norm, hx20_4]
          have hx21_7 : s_ep.readReg64 .x21 = fp + 4#64 := by
            rw [hcsp7.2.2.1]; simp only [s_dr, arm64_norm, hx21_4]
          have hx22_7 : s_ep.readReg64 .x22 = BitVec.ofNat 64 (rest.length - 64) := by
            rw [hcsp7.2.2.2.1]; simp only [s_dr, arm64_norm, hx22_4]
          have hsp7' : s_ep.sp = s0.sp - 96#64 := by
            rw [hsp7]; simp only [s_dr, arm64_norm, hsp4']
          clear hsp7
          have hal7 : s_ep.spAligned = true := sp_sub_96_spAligned hal0 hsp7'
          let _ := hal7
          have htr7' : s_ep.trace = s0.trace := by
            rw [htr7]; simp only [s_dr, arm64_norm, htr4']
          have hcs7 : SsgUpperSaved s0 s_ep := hcs_dr.trans_calleeSaved hcsp7
          rcases hcs7 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
          have hsdr_sp : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, arm64_norm, hsp4']
          rw [hsdr_sp, ret48_open_signed_ok retAddr]
          unfold ssgSavedRegs
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          refine SepWPp.exists_elim fun r40 => SepWPp.exists_elim fun r32 =>
            SepWPp.exists_elim fun r24 => SepWPp.exists_elim fun r16 =>
            SepWPp.exists_elim fun r8 => SepWPp.exists_elim fun r0 => ?_
          apply SepWPp.of_sepWP_ret
          wp_steps
          apply bind_sepWP_state_p; intro sf
          apply SepWP.done (by simp only [sf, arm64_norm, *]) (by simp only [sf, arm64_norm, *])
          refine ⟨by simp only [sf, arm64_norm, *], ?_, ?_⟩
          · refine ⟨by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, arm64_norm, *],
              by simp only [sf, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs⟩
          · have htrf : sf.trace = s0.trace := by simp only [sf, arm64_norm, htr7']
            rw [htrf, eq_self, pure_true, emp_sepConj]
            have hstk_pack :
                (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
                  (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                    stackAt (s0.sp - 96#64) dropSpeStackX) ∗
                  memRegion (s0.sp - 96#64) 48 ∗
                  ssgSavedRegs s0.sp s0) ⊢
                stackAt s0.sp stk := by
              rw [← stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega)]
              exact stackAt_ssg_pack_region s0.sp subStk stk s0 hstk hstkle
            refine Entails.trans (Q :=
              (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
                (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                  stackAt (s0.sp - 96#64) dropSpeStackX) ∗
                memRegion (s0.sp - 96#64) 48 ∗
                ssgSavedRegs s0.sp s0) ∗
              (ssgMalfRO_p ∗
                splitSignedResultAt A retAddr fp file ∗
                SpqrV1.ChainProofs.bytesAt ro fp file ∗
                A.pool)) ?_
              (Entails.trans (sepConj_mono_left hstk_pack) ?_)
            · dsimp only [splitSignedResultAt]
              rw [hsigned]
              dsimp only
              rw [← splitOkTag_eq, hkey_len]
              unfold ssgSavedRegs
              simp only [sepConj_assoc]
              generalize dropSpeStackX = dsz
              exact Entails.of_eq (by ac_rfl)
            · exact Entails.of_eq (by ac_rfl)

/-! ## Prologue and Top-Level Contracts -/

private theorem sepWPp_mono_post_p {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf)
    (h : SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q' Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hQ⟩ | hpan | hoom_s⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom_s)⟩

private theorem ssg_prologue_p [LibsignalPlacement] {H : LibsignalHooks}
    {s0 : State} {ret fp : BitVec 64} {s48 s40 s32 s24 s16 s8 : BitVec 64}
    {R_frame : SepProp} {post : State → SepProp → Prop}
    (hal0 : s0.spAligned = true)
    (hpc : s0.pc = lsmpl.base 592)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = fp)
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = lsmpl.base 593 →
      s1.status = .Running →
      s1.sp = s0.sp - 96#64 →
      s1.trace = s0.trace →
      s1.readReg64 Reg.lr = (blkPl_592).base + 32#64 →
      s1.readReg64 .x0 = s0.sp - 96#64 →
      s1.readReg64 .x1 = fp →
      s1.readReg64 .x2 = s0.readReg64 .x2 →
      s1.readReg64 .x19 = ret →
      SsgUpperSaved s0 s1 →
      P1 = (ssgSavedRegs s0.sp s0 ∗ R_frame) →
      post s1 P1) :
    SepWP (lsProg_592 H)
      (lsmpl.base 593) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ s24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗ R_frame)
      post := by
  have _ := And.intro hx0 hx1
  rw [show lsmpl.base 592 = (blkPl_592).base + 0#64 by rw [BitVec.add_zero]; rfl] at hpc
  wp_steps
  apply bind_sepWP_state_p; intro s1
  apply SepWP.done (by simp only [s1, arm64_norm, *]) (by simp only [s1, arm64_norm, *])
  refine hnext s1 _
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, SsgUpperSaved, calleeSavedVRegs, arm64_norm])
    ?_
  unfold ssgSavedRegs
  simp only [arm64_norm, sepConj_assoc]

/-- `signal_session::public::split_signed` (Block `592`) satisfies `splitSignedSpecPlaced A stk` under `[LibsignalPlacement]`. -/
theorem splitSigned_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {splitStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hSplit : subroutine_ok (lsProg_592 H) (lsmpl.base 593)
      (splitIdSpecPlaced A splitStk))
    (hDrop : subroutine_ok (lsProg_592 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX A)))
    (hstk : 0x60 + max splitStk dropSpeStackX ≤ stk) :
    subroutine_ok (lsProg_592 H) (lsmpl.base 592)
      (splitSignedSpecPlaced A stk) := by
  set subStk := max splitStk dropSpeStackX
  have hsub_sp : splitStk ≤ subStk := Nat.le_max_left _ _
  have hsub_dr : dropSpeStackX ≤ subStk := Nat.le_max_right _ _
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hal0
  obtain ⟨hcrl0, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [splitSignedSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2_nat⟩, hpre⟩ := hpre
  have hfile_lt64 : x.file.length < 2 ^ 64 := hx2_nat ▸ (s0.readReg64 .x2).isLt
  have hstkle : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (memRegion x.ret 48 ∗ (SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ A.pool ∗ R)) := by
      refine Satisfies.mono ?_ hpre
      generalize stackAt s0.sp stk = topStk
      exact Entails.of_eq (by ac_rfl)
    exact Nat.le_of_lt (stack_lt_addr_space hm_stk (by omega))
  have hpre_ro := ssgMalfRO_bundle_intro_p hcrl0.2 hpre
  rw [stackAt_ssg_split s0.sp subStk stk hstk hstkle, cells48_open s0.sp] at hpre_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s48, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s40, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s32, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s24, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s16, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s8, hpre_ro⟩ := hpre_ro
  refine ⟨(((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ s24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗
      (ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        memRegion (s0.sp - 96#64) 48 ∗
        stackAt (s0.sp - 96#64) subStk ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
        memRegion x.ret 48 ∗
        A.pool),
    R,
    by
      refine Satisfies.mono ?_ hpre_ro
      exact Entails.of_eq (by ac_rfl),
    ?_⟩
  have hwp : SepWPp (lsProg_592 H) (s0.readReg64 Reg.lr) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
          ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ s24) ∗
          ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗
        (ssgMalfRO_p ∗
          ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
          memRegion (s0.sp - 96#64) 48 ∗
          stackAt (s0.sp - 96#64) subStk ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
          memRegion x.ret 48 ∗
          A.pool))
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        ∃ G : SepProp, P_f ⊢ G ∗
          (⌜sf.trace = s0.trace⌝ ∗
            splitSignedResultAt A x.ret x.fp x.file ∗
            SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
            stackAt s0.sp stk ∗ A.pool))
      (SsgPanicAllow s0) := by
    rcases x with ⟨ret, fp, file, ro⟩
    dsimp only at *
    apply StoreKit.sepWPp_seq_lscro hcrl0 (mid := lsmpl.base 593)
    refine ssg_prologue_p hal0 hpc hrun hx0 hx1
      fun s1 P1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hcs1 hP1 hcrl1 => ?_
    rw [hP1]
    have hal1 : s1.spAligned = true := sp_sub_96_spAligned hal0 hsp1
    refine ssg_call_lscro ⟨s0.sp - 96#64, fp, file, ro⟩ hSplit hcrl1 htr1 hpc1 hrun1 hal1 hlr1
      (F := ssgSavedRegs s0.sp s0 ∗
        ssgMalfRO_p ∗
        ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - splitStk) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        memRegion ret 48)
      ?_
      (hpanic := fun sm R' _ hp => by
        dsimp only at hp
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        exact hp.1)
      (hnext := ?_)
    · rw [stackAt_sub_split (s0.sp - 96#64) splitStk subStk hsub_sp (by omega)]
      have hpure_sp :
          (s1.readReg64 .x0 = s0.sp - 96#64 ∧ s1.readReg64 .x1 = fp ∧
            (s1.readReg64 .x2).toNat = file.length) = True :=
        eq_true ⟨hx0_1, hx1_1, hx2_1 ▸ hx2_nat⟩
      dsimp only
      rw [hpure_sp, pure_true, emp_sepConj, hsp1]
      exact Entails.of_eq (by ac_rfl)
    · intro s2 hcrl2 hpc2 hrun2 hsp2 hcsp2
      dsimp only
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr2 => ?_
      have hx19_2 : s2.readReg64 .x19 = ret := hcsp2.1.trans hx19_1
      have hsp2' : s2.sp = s0.sp - 96#64 := hsp2.trans hsp1
      have htr2' : s2.trace = s0.trace := htr2.trans htr1
      have hcs2 : SsgUpperSaved s0 s2 := hcs1.trans_calleeSaved hcsp2
      have hpre2 :
          ((splitIdResultAt A (s0.sp - 96#64) fp file ∗
              SpqrV1.ChainProofs.bytesAt ro fp file ∗
              stackAt s1.sp splitStk ∗
              A.pool) ∗
            ssgSavedRegs s0.sp s0 ∗
            ssgMalfRO_p ∗
            ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
            memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - splitStk) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
            memRegion ret 48) ⊢
          (ssgMalfRO_p ∗
            ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle") ∗
            splitIdResultAt A (s0.sp - 96#64) fp file ∗
            ssgSavedRegs s0.sp s0 ∗
            stackAt (s0.sp - 96#64) subStk ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗
            memRegion ret 48 ∗
            A.pool) := by
        rw [hsp1, stackAt_sub_split (s0.sp - 96#64) splitStk subStk hsub_sp (by omega)]
        exact Entails.of_eq (by ac_rfl)
      cases hsid : splitId file with
      | none =>
        refine SepWPp.weaken_pre hpre2 ?_
        refine sepWPp_mono_post_p ?_
          (step_err_copy_path_p hstk hstkle ret fp ro file hsid hal0 hpc2 hrun2 hsp2' htr2' hx19_2 hcs2)
        intro sf P_f ⟨hspf, hcsf, hent⟩
        exact ⟨hspf, hcsf, ssgMalfRO_p ∗ ((lsρ ssgBundleSym) ↦ᵣ utf8 "bundle"),
          Entails.trans hent (Entails.of_eq (by ac_rfl))⟩
      | some p =>
        rcases p with ⟨id, rest⟩
        have hrest_lt : rest.length < 2 ^ 64 := by
          rcases file with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, tl⟩⟩⟩⟩ <;>
            simp [splitId] at hsid
          obtain ⟨_, rfl⟩ := hsid
          simp only [List.length_cons] at hfile_lt64
          omega
        by_cases hge64 : 64 ≤ rest.length
        · refine SepWPp.weaken_pre hpre2 ?_
          refine sepWPp_mono_post_p ?_
            (step_ok_signed_path_p hC hpan hDrop hsub_dr hstk hstkle ret fp ro file id rest
              hsid hrest_lt hge64 hal0 hcrl2 hpc2 hrun2 hsp2' htr2' hx19_2 hcs2)
          intro sf P_f ⟨hspf, hcsf, hent⟩
          exact ⟨hspf, hcsf, ssgMalfRO_p, hent⟩
        · have hlt64 : rest.length < 64 := by omega
          refine SepWPp.weaken_pre hpre2 ?_
          refine sepWPp_mono_post_p ?_
            (step_short_err_path_p hC hpan hsub_dr hstk hstkle ret fp ro file id rest
              hsid hlt64 hal0 hcrl2 hpc2 hrun2 hsp2' htr2' hx19_2 hcs2)
          intro sf P_f ⟨hspf, hcsf, hent⟩
          exact ⟨hspf, hcsf, ssgMalfRO_p, hent⟩
  intro Fr hm hL
  obtain ⟨sf, hsteps, hout⟩ := hwp Fr hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hspf, hcsf, G, hent⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨hoom_s, hmo⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf,
      (splitSignedSpecPlaced A stk).post x s0 sf,
      ?_, fun hmR => hmR, hspf, hcsf⟩⟩
    dsimp only [splitSignedSpecPlaced, StoreKit.withLsCodeRoLoaded]
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepConj_assoc] at hm1
    exact Satisfies.of_sep_right hm1
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, fun hmR => by
      dsimp only [splitSignedSpecPlaced, StoreKit.withLsCodeRoLoaded]
      exact hqp R hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hoom_s, hmo⟩)⟩

theorem splitSigned_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {splitStk stk : Nat} {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hSplit : subroutine_ok (lsProg_592 H) (lsmpl.base 593)
      (splitIdSpecPlaced A splitStk))
    (hDrop : subroutine_ok (lsProg_592 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX A)))
    (hstk : 0x60 + max splitStk dropSpeStackX ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 592) (splitSignedSpecPlaced A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 592)
    (splitSigned_placed_ok_of_deps hC hpan hSplit hDrop hstk) hi

end CryptoVerification.SignalSession.Cli.SplitSigned.Helpers

namespace CryptoVerification.SignalSession.Cli.SplitSigned

open Arm64 ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

theorem splitSigned_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {splitStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hSplit : subroutine_ok (lsProg_592 H) (lsmpl.base 593)
      (splitIdSpecPlaced A splitStk))
    (hDrop : subroutine_ok (lsProg_592 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX A)))
    (hstk : 0x60 + max splitStk dropSpeStackX ≤ stk) :
    subroutine_ok (lsProg_592 H) (lsmpl.base 592) (splitSignedSpecPlaced A stk) :=
  Helpers.splitSigned_placed_ok_of_deps hC hpan hSplit hDrop hstk

theorem splitSigned_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {splitStk stk : Nat} {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hSplit : subroutine_ok (lsProg_592 H) (lsmpl.base 593)
      (splitIdSpecPlaced A splitStk))
    (hDrop : subroutine_ok (lsProg_592 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX A)))
    (hstk : 0x60 + max splitStk dropSpeStackX ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 592) (splitSignedSpecPlaced A stk) :=
  Helpers.splitSigned_placed_caller_ok_of_deps hC hpan hSplit hDrop hstk hi

end CryptoVerification.SignalSession.Cli.SplitSigned
