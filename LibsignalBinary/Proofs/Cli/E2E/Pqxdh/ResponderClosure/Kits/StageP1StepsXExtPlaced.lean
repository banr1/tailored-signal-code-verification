/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExt
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlaced

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

theorem decryptPrekeyClosure_dealloc_ok_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) := by
  dsimp only [stageP1ProgPlaced, lsProg_518]
  exact ls_hook_ok_ultra_of_mem hdealloc (by decide)

theorem decryptPrekeyClosure_dealloc_ok_ext_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (stageP1ProgPlaced (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) := by
  obtain ⟨fn, hfn, hsat⟩ := hA
  have hne : Rust.isPanicSymbol "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" = false := by
    simp [Rust.isPanicSymbol]
  exact decryptPrekeyClosure_dealloc_ok_placed ⟨fn, by simp [Rust.withPanics, hne, hfn], hsat⟩

set_option maxHeartbeats 400000 in
theorem p1_seg1_vregs_wp_ext_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    loadShimAddr v_sp0 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = outPtr)
    (hx1 : s.readReg64 .x1 = coroPtr)
    (hx2 : s.readReg64 .x2 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) loadShimAddr s
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       ((sessStoreVt + 0x18#64) ↦₆₄ᵣ loadShimAddr) ∗
       ((s.sp - 0xcd0#64) ↦₆₄ v_sp0) ∗
       cells (s.sp - 0x60#64) 12)
      (fun s1 P_f =>
        (P_f ⊢
          decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
          ((sessStoreVt + 0x18#64) ↦₆₄ᵣ loadShimAddr) ∗
          ((s.sp - 0xcd0#64) ↦₆₄ 0#64) ∗
          decryptPrekeySavedRegsAt s.sp s) ∧
        s1.sp = s.sp - 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = sessStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = (s.sp - 0xcd0#64) + 0x370#64 ∧
        s1.readReg64 .x25 = (s.sp - 0xcd0#64) + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = (s.sp - 0xcd0#64) + 0xa90#64 ∧
        s1.readReg64 .x29 = s.sp - 0x60#64 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x130#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = outPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = coroPtr := hx1
  have hx2' : s.readReg64 (Reg.gpr 2#5) = ctxPtr := hx2
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  dsimp only [decryptPrekeyCoroInitAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub,
      bv_sub_add_lit, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  dsimp only [decryptPrekeyCoroInitAt, decryptPrekeyCoroCopyAt, decryptPrekeySavedRegsAt,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x29, Reg.x30]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem p1_seg5_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr trustFutPtr trustFutVt trustPollAddr u0 u1 u2 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x650#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = trustFutPtr)
    (hx1 : s.readReg64 .x1 = trustFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) trustPollAddr s
      (((coroPtr + 0x398#64) ↦₆₄ u0) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u1) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u2) ∗
       ((trustFutVt + 0x18#64) ↦₆₄ᵣ trustPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((trustFutVt + 0x18#64) ↦₆₄ᵣ trustPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = trustFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x66c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = trustFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = trustFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_seg6a_any_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr trustFutPtr trustFutVt trustDropAddr
    w_3e0 w_3f0 w_400 w_408 u_a8 u_b0 u_b8 u_c8 u_d0 : BitVec 64)
    (d_3e9 d_3f8 d_3fc : BitVec 32) (h_3ed : BitVec 16) (b_3e8 b_3ef : BitVec 8)
    (hw_ne_neg3 : w_3e0 ≠ 0xfffffffffffffffd#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x66c#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hdrop_nz : trustDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (stageP1ProgPlaced ext) trustDropAddr s
      (((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
       ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       ((s.sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
       ((s.sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
       ((s.sp + 0x3ef#64) ↦₈ b_3ef) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
       ((s.sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
       ((s.sp + 0x400#64) ↦₆₄ w_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ w_408))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
          ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ d_3fc.zeroExtend 64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w_3f0) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ d_3f8.zeroExtend 64) ∗
          memRegion (s.sp + 0x3e0#64) 48) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = trustFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w_3e0 ∧
        s1.readReg64 .x21 = trustFutPtr ∧
        s1.readReg64 .x23 = b_3e8.zeroExtend 64 ∧
        s1.readReg64 .x25 = trustFutVt ∧
        s1.readReg64 .x27 = w_408 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x6d0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond := cond_ne_adds64_of_ne_neg3_std3 hw_ne_neg3
  have hcond' : (w_3e0 + 3#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (trustDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = coroPtr + 0x390#64 := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps
  apply SepWP.fold
    (trustOut48_fold_p1 s.sp w_3e0 b_3e8 d_3e9 h_3ed b_3ef w_3f0 d_3f8 d_3fc
      w_400 w_408)
    (by sep_focus)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_post_dealloc_true_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr
    msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
    u_98 u_a0 : BitVec 64)
    (b_4f2 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x6e4#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 1#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x868#64) s
      (processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       cells (coroPtr + 0x428#64) 8 ∗
       cells (coroPtr + 0x490#64) 4 ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0))
      (fun s1 P_f =>
        (P_f ⊢
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64))) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = kyberStorePtr ∧
        s1.readReg64 .x9 = msgPtr ∧
        s1.readReg64 .x10 = kyberStoreVt ∧
        s1.readReg64 .x11 = preKeyStorePtr ∧
        s1.readReg64 .x12 = remoteAddrPtr ∧
        s1.readReg64 .x13 = preKeyStoreVt ∧
        s1.readReg64 .x14 = localAddrPtr ∧
        s1.readReg64 .x15 = idStorePtr ∧
        s1.readReg64 .x16 = idStoreVt ∧
        s1.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  dsimp only [processPrekeyInnerInitAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  dsimp only [processPrekeyInnerInitAt, processPrekeyPostTrustAt]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem p1_seg6_dealloc_vregs_wp_ext_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr trustFutPtr trustFutVt w_20 w_23 : BitVec 64)
    (trustBoxSize : Nat)
    (hpc : s.pc = stageP1EntryPlaced + 0x6d0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 trustBoxSize ≠ 0#64)
    (hbs_lt : trustBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w_20)
    (hx21 : s.readReg64 .x21 = trustFutPtr)
    (hx23 : s.readReg64 .x23 = w_23)
    (hx25 : s.readReg64 .x25 = trustFutVt) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x6e4#64) s
      (((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
       ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live trustFutPtr trustBoxSize 8 ∗
       memRegion trustFutPtr trustBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
          ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w_20 ∧
        s1.readReg64 .x23 = w_23 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hbs_beq : (BitVec.ofNat 64 trustBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 trustBoxSize).toNat = trustBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w_20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = trustFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w_23 := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = trustFutVt := hx25
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hdealloc hpc ⊢
  wp_steps
  wp_call hdealloc (trustFutPtr, trustBoxSize, 8)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_seg4_vregs_wp_ext_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr loadFutPtr loadFutVt trustShimAddr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (loadBoxSize : Nat) (b_390 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x238#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 loadBoxSize ≠ 0#64)
    (hbs_lt : loadBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = loadFutPtr)
    (hx23 : s.readReg64 .x23 = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 .x24 = loadFutVt) :
    SepWP (stageP1ProgPlaced ext) trustShimAddr s
      (((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
       ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live loadFutPtr loadBoxSize 8 ∗
       memRegion loadFutPtr loadBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr sessStoreVt idStorePtr idStoreVt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
          ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
          ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 8#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x650#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hbs_beq : (BitVec.ofNat 64 loadBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 loadBoxSize).toNat = loadBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = loadFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = loadFutVt := hx24
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hdealloc hpc ⊢
  wp_steps
  wp_call hdealloc (loadFutPtr, loadBoxSize, 8)
  dsimp only [decryptPrekeyCoroCopyAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  dsimp only [decryptPrekeyCoroCopyAt, sessionRecordEmptyHeaderAt, processPrekeyInnerInitAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
theorem p1_seg3_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX))
    (s : State) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (coroPtr loadFutPtr loadFutVt loadDropAddr
    w_3e8 w_3f4 w_3fc w_404 w_40c u0 u1 u2 u3 : BitVec 64)
    (d_3f0 d_414 du4 : BitVec 32) (bs312 : List (BitVec 8))
    (hpc : s.pc = stageP1EntryPlaced + 0x14c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs312 : bs312.length = 312)
    (hdrop_nz : loadDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x3e0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (stageP1ProgPlaced ext) loadDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
       ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
       memRegion (s.sp + 0xd8#64) 312 ∗
       ((s.sp + 0x210#64) ↦₆₄ u0) ∗ ((s.sp + 0x218#64) ↦₆₄ u1) ∗
       ((s.sp + 0x220#64) ↦₆₄ u2) ∗ ((s.sp + 0x228#64) ↦₆₄ u3) ∗
       ((s.sp + 0x230#64) ↦₃₂ du4) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
       ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
       ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
       ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
       ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
       ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
       ((s.sp + 0x418#64) ↦ₛ bs312) ∗
       stackAt s.sp extHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
          memRegion (s.sp + 0xd8#64) 348 ∗
          memRegion (s.sp + 0x3e0#64) 368 ∗
          stackAt s.sp extHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = loadFutPtr ∧
        s1.readReg64 .x22 = d_3f0.zeroExtend 64 ∧
        s1.readReg64 .x23 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x24 = loadFutVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x238#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdrop_beq : (loadDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x3e0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hmemcpy hpc ⊢
  apply StoreKit.sepWP_seq_lscro (mid := lsρ "memcpy") hcrl
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun ⟨hcl_m, hro_m⟩ => ?_
  conv =>
    arg 4
    rw [show memRegion (s.sp + 0xd8#64) 312 =
      memRegion (s.sp + 0xd8#64) bs312.length by rw [hbs312]]
  wp_call hmemcpy (s.sp + 0xd8#64, s.sp + 0x418#64, bs312)
  apply SepWP.fold
    (loadSessionScratch_fold_p1 s.sp 0xffffffffffffffff#64 w_3e8 w_3f4 w_3fc w_404 w_40c
      w_3f4 w_3fc w_404 w_40c d_3f0 d_414 d_414 hbs312)
    (by sep_focus)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_load_some_seg3_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX))
    (s : State) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (coroPtr loadFutPtr loadFutVt loadDropAddr
    w_3e0 w_3e8 w_3f4 w_3fc w_404 w_40c u0 u1 u2 u3 : BitVec 64)
    (d_3f0 d_414 du4 : BitVec 32) (bs312 : List (BitVec 8))
    (hw_ne_neg3 : w_3e0 ≠ 0xfffffffffffffffd#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x14c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs312 : bs312.length = 312)
    (hdrop_nz : loadDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x3e0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (stageP1ProgPlaced ext) loadDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
       ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
       memRegion (s.sp + 0xd8#64) 312 ∗
       ((s.sp + 0x210#64) ↦₆₄ u0) ∗ ((s.sp + 0x218#64) ↦₆₄ u1) ∗
       ((s.sp + 0x220#64) ↦₆₄ u2) ∗ ((s.sp + 0x228#64) ↦₆₄ u3) ∗
       ((s.sp + 0x230#64) ↦₃₂ du4) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
       ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
       ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
       ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
       ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
       ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
       ((s.sp + 0x418#64) ↦ₛ bs312) ∗
       stackAt s.sp extHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
          ((s.sp + 0xd8#64) ↦ₛ bs312) ∗
          ((s.sp + 0x210#64) ↦₆₄ w_3f4) ∗ ((s.sp + 0x218#64) ↦₆₄ w_3fc) ∗
          ((s.sp + 0x220#64) ↦₆₄ w_404) ∗ ((s.sp + 0x228#64) ↦₆₄ w_40c) ∗
          ((s.sp + 0x230#64) ↦₃₂ d_414) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
          ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
          ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
          ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
          ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
          ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
          ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
          ((s.sp + 0x418#64) ↦ₛ bs312) ∗
          stackAt s.sp extHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = loadFutPtr ∧
        s1.readReg64 .x22 = d_3f0.zeroExtend 64 ∧
        s1.readReg64 .x23 = w_3e0 ∧
        s1.readReg64 .x24 = loadFutVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x238#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond := cond_ne_adds64_of_ne_neg3_std3 hw_ne_neg3
  have hcond' : (w_3e0 + 3#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (loadDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x3e0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hmemcpy hpc ⊢
  apply StoreKit.sepWP_seq_lscro (mid := lsρ "memcpy") hcrl
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun ⟨hcl_m, hro_m⟩ => ?_
  conv =>
    arg 4
    rw [show memRegion (s.sp + 0xd8#64) 312 =
      memRegion (s.sp + 0xd8#64) bs312.length by rw [hbs312]]
  wp_call hmemcpy (s.sp + 0xd8#64, s.sp + 0x418#64, bs312)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_load_some_seg4_vregs_wp_ext_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX))
    (s : State) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (coroPtr loadFutPtr loadFutVt trustShimAddr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    w_3e0 w_3e8 v_210 v_218 v_220 v_228
    c0 c1 c_f4 c_fc c_104 c_10c : BitVec 64)
    (d_3f0 dv_230 c_f0 c_114 : BitVec 32)
    (bs312 : List (BitVec 8))
    (loadBoxSize : Nat) (b_390 : BitVec 8)
    (hw_ne_neg2 : w_3e0 ≠ 0xfffffffffffffffe#64)
    (hw_ne_neg1 : w_3e0 ≠ 0xffffffffffffffff#64)
    (hbs312 : bs312.length = 312)
    (hpc : s.pc = stageP1EntryPlaced + 0x238#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 loadBoxSize ≠ 0#64)
    (hbs_lt : loadBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = loadFutPtr)
    (hx22 : s.readReg64 .x22 = d_3f0.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = w_3e0)
    (hx24 : s.readReg64 .x24 = loadFutVt)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = w_3e8) :
    SepWP (stageP1ProgPlaced ext) trustShimAddr s
      (((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
       ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live loadFutPtr loadBoxSize 8 ∗
       memRegion loadFutPtr loadBoxSize ∗
       A.pool ∗
       stackAt s.sp extHookStack ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr sessStoreVt idStorePtr idStoreVt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       ((coroPtr + 0xe0#64) ↦₆₄ c0) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ c1) ∗
       ((coroPtr + 0xf0#64) ↦₃₂ c_f0) ∗
       ((coroPtr + 0xf4#64) ↦₆₄ c_f4) ∗
       ((coroPtr + 0xfc#64) ↦₆₄ c_fc) ∗
       ((coroPtr + 0x104#64) ↦₆₄ c_104) ∗
       ((coroPtr + 0x10c#64) ↦₆₄ c_10c) ∗
       ((coroPtr + 0x114#64) ↦₃₂ c_114) ∗
       memRegion (coroPtr + 0x118#64) 312 ∗
       ((s.sp + 0xd8#64) ↦ₛ bs312) ∗
       ((s.sp + 0x210#64) ↦₆₄ v_210) ∗
       ((s.sp + 0x218#64) ↦₆₄ v_218) ∗
       ((s.sp + 0x220#64) ↦₆₄ v_220) ∗
       ((s.sp + 0x228#64) ↦₆₄ v_228) ∗
       ((s.sp + 0x230#64) ↦₃₂ dv_230) ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
          ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp extHookStack ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          ((coroPtr + 0xe0#64) ↦₆₄ w_3e0) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ w_3e8) ∗
          ((coroPtr + 0xf0#64) ↦₃₂ d_3f0) ∗
          ((coroPtr + 0xf4#64) ↦₆₄ v_210) ∗
          ((coroPtr + 0xfc#64) ↦₆₄ v_218) ∗
          ((coroPtr + 0x104#64) ↦₆₄ v_220) ∗
          ((coroPtr + 0x10c#64) ↦₆₄ v_228) ∗
          ((coroPtr + 0x114#64) ↦₃₂ dv_230) ∗
          ((coroPtr + 0x118#64) ↦ₛ bs312) ∗
          ((s.sp + 0xd8#64) ↦ₛ bs312) ∗
          ((s.sp + 0x210#64) ↦₆₄ v_210) ∗
          ((s.sp + 0x218#64) ↦₆₄ v_218) ∗
          ((s.sp + 0x220#64) ↦₆₄ v_220) ∗
          ((s.sp + 0x228#64) ↦₆₄ v_228) ∗
          ((s.sp + 0x230#64) ↦₃₂ dv_230) ∗
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
          ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s1.readReg64 .x23 = w_3e0 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x650#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hstk_split := stackAt_split_of_le s.sp extHookStack allocHookStack (by decide) (by decide)
  have hcond_neg2 := cond_ne_adds64_of_ne_neg2_std3 hw_ne_neg2
  have hcond_neg1 := cond_eq_adds64_of_ne_neg1_std3 hw_ne_neg1
  have hcond_neg2' : (w_3e0 + 2#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hcond_neg1' : (w_3e0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
  have hbs_beq : (BitVec.ofNat 64 loadBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 loadBoxSize).toNat = loadBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = loadFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = d_3f0.zeroExtend 64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w_3e0 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = loadFutVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w_3e8 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hdealloc hmemcpy hpc ⊢
  apply StoreKit.sepWP_seq_lscro (mid := lsρ "memcpy") hcrl
  apply SepWP.fold (Entails.of_eq hstk_split) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  wp_call hdealloc (loadFutPtr, loadBoxSize, 8)
  apply SepWP.fold (Entails.of_eq hstk_split.symm) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun ⟨hcl_m, hro_m⟩ => ?_
  conv =>
    arg 4
    rw [show memRegion (coroPtr + 0x118#64) 312 =
      memRegion (coroPtr + 0x118#64) bs312.length by rw [hbs312]]
  wp_call hmemcpy (coroPtr + 0x118#64, s.sp + 0xd8#64, bs312)
  dsimp only [decryptPrekeyCoroCopyAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  dsimp only [decryptPrekeyCoroCopyAt, processPrekeyInnerInitAt]
  simp only [hsp_sf, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlaced
