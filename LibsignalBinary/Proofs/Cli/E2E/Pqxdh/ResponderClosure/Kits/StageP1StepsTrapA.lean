/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P1 `trTrapProgAt` Segment Lemmas — Part A

`calleeSavedVRegs`-preserving `SepWP` segment lemmas `p1_seg1_vregs_wp_trap ..
p1_seg5_vregs_wp_trap` over `trTrapProgAt b C abs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

set_option maxHeartbeats 1200000 in
theorem p1_seg1_vregs_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    loadShimAddr v_sp0 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = outPtr)
    (hx1 : s.readReg64 .x1 = coroPtr)
    (hx2 : s.readReg64 .x2 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) loadShimAddr s
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
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x130#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x0 0x40
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x88 0x90
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xe4 0x12c
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  subst hx0 hx1 hx2
  dsimp only [decryptPrekeyCoroInitAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub,
      bv_sub_add_lit, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
  refine ⟨?_, by simp [arm64_norm], rfl,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  dsimp only [decryptPrekeyCoroInitAt, decryptPrekeyCoroCopyAt, decryptPrekeySavedRegsAt,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x29, Reg.x30]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem p1_seg2_vregs_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr loadFutPtr loadFutVt loadPollAddr u0 u1 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x130#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = loadFutPtr)
    (hx1 : s.readReg64 .x1 = loadFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) loadPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u1) ∗
       ((loadFutVt + 0x18#64) ↦₆₄ᵣ loadPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x18#64) ↦₆₄ᵣ loadPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x14c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x130 0x148
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  subst hx0 hx1 hx19 hx27
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_seg3_vregs_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr loadFutPtr loadFutVt loadDropAddr
    w_3e8 w_3f4 w_3fc w_404 w_40c u0 u1 u2 u3 : BitVec 64)
    (d_3f0 d_414 du4 : BitVec 32) (bs312 : List (BitVec 8))
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x14c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs312 : bs312.length = 312)
    (hdrop_nz : loadDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x3e0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (trTrapProgAt b C abs) loadDropAddr s
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
       ((s.sp + 0x418#64) ↦ₛ bs312))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
          memRegion (s.sp + 0xd8#64) 348 ∗
          memRegion (s.sp + 0x3e0#64) 368) ∧
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
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x238#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy :=
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap
      (b := b) (C := C) (abs := abs)
  have hdrop_beq : (loadDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x14c 0x154
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1f4 0x234
  dsimp only [trTrapProgAt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x3e0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  wp_steps
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
theorem p1_seg4_vregs_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr loadFutPtr loadFutVt trustShimAddr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (loadBoxSize : Nat) (b_390 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x238#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 loadBoxSize ≠ 0#64)
    (hbs_lt : loadBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = loadFutPtr)
    (hx23 : s.readReg64 .x23 = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 .x24 = loadFutVt) :
    SepWP (trTrapProgAt b C abs) trustShimAddr s
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
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc :=
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap
      (b := b) (C := C) (abs := abs) hA
  have hbs_beq : (BitVec.ofNat 64 loadBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 loadBoxSize).toNat = loadBoxSize := Nat.mod_eq_of_lt hbs_lt
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x238 0x250
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x4c0 0x4c8
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x578 0x64c
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = loadFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = loadFutVt := hx24
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

set_option maxHeartbeats 800000 in
theorem p1_seg5_vregs_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr trustFutPtr trustFutVt trustPollAddr u0 u1 u2 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = trustFutPtr)
    (hx1 : s.readReg64 .x1 = trustFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) trustPollAddr s
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
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x66c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x650 0x668
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  subst hx0 hx1 hx19 hx27
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
